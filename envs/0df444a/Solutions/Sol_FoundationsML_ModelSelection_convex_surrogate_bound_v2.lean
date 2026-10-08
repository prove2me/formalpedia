-- Prove2me | solution 1 for FoundationsML.ModelSelection.convex_surrogate_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:15:06.558536+00:00
-- url     : https://prove2.me/submissions/54097cd7-2364-4b79-91a9-3e7a7d1c674b

import Mathlib
import Definitions.Def_FoundationsML_ModelSelection_BayesScore
import Definitions.Def_FoundationsML_ModelSelection_PhiLossPointwise
import Definitions.Def_FoundationsML_ModelSelection_ExpectedPhiLoss
import Definitions.Def_FoundationsML_ModelSelection_ScoringRisk

open MeasureTheory


namespace FoundationsML.ModelSelection

lemma csb_phi_zero_le (e Φ : ℝ → ℝ) (he : 0 ≤ e 0 ∧ e 0 ≤ 1)
    (hΦconv : ConvexOn ℝ Set.univ Φ) (hΦmono : Monotone Φ) (u : ℝ)
    (hbad : (u < 0 ∧ 1/2 ≤ e 0) ∨ (0 ≤ u ∧ e 0 < 1/2)) :
    e 0 * Φ (-0) + (1 - e 0) * Φ 0 ≤ e 0 * Φ (-u) + (1 - e 0) * Φ u := by
  have h1 : Φ (e 0 • (-u) + (1 - e 0) • u) ≤ e 0 • Φ (-u) + (1 - e 0) • Φ u :=
    hΦconv.2 (Set.mem_univ _) (Set.mem_univ _) he.1 (by linarith) (by ring)
  simp only [smul_eq_mul] at h1
  have h2 : Φ 0 ≤ Φ (e 0 * (-u) + (1 - e 0) * u) := by
    apply hΦmono
    rcases hbad with ⟨a, b⟩ | ⟨a, b⟩ <;> nlinarith
  simp only [neg_zero]
  nlinarith

theorem csb_core {X : Type*} [MeasurableSpace X] (DX : Measure X)
    [IsProbabilityMeasure DX] (η : X → ℝ) (hη_meas : Measurable η)
    (hη : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) (Φ : ℝ → ℝ)
    (hΦconv : ConvexOn ℝ Set.univ Φ) (hΦmono : Monotone Φ)
    (hΦstar : X → ℝ) (hΦstar_meas : Measurable hΦstar)
    (hΦstar_min : ∀ x u, PhiLossPointwise η Φ x (hΦstar x) ≤ PhiLossPointwise η Φ x u)
    (hΦstar_int : Integrable (fun x => PhiLossPointwise η Φ x (hΦstar x)) DX)
    (s c : ℝ) (hs : 1 ≤ s) (hc : 0 < c)
    (hbound : ∀ x, |BayesScore η x| ^ s ≤
      c ^ s * (PhiLossPointwise η Φ x 0 - PhiLossPointwise η Φ x (hΦstar x)))
    (h : X → ℝ) (hh_meas : Measurable h)
    (hh_int : Integrable (fun x => PhiLossPointwise η Φ x (h x)) DX) :
    ScoringRisk DX η h - ScoringRisk DX η (BayesScore η) ≤
      2 * c * (ExpectedPhiLoss DX η Φ h - ExpectedPhiLoss DX η Φ hΦstar) ^ (1 / s) := by
  classical
  set f : X → ℝ := fun x => if (h x < 0 ∧ 1/2 ≤ η x) ∨ (0 ≤ h x ∧ η x < 1/2)
    then |η x - 1/2| else 0 with hf_def
  set g : X → ℝ := fun x => PhiLossPointwise η Φ x (h x) - PhiLossPointwise η Φ x (hΦstar x)
    with hg_def
  have hs0 : 0 < s := by linarith
  have hf_meas : Measurable f := by
    apply Measurable.ite
    · apply MeasurableSet.union
      · exact (measurableSet_lt hh_meas measurable_const).inter (measurableSet_le measurable_const hη_meas)
      · exact (measurableSet_le measurable_const hh_meas).inter (measurableSet_lt hη_meas measurable_const)
    · exact (hη_meas.sub measurable_const).abs
    · exact measurable_const
  have hf_nn : ∀ x, 0 ≤ f x := by
    intro x; simp only [hf_def]; split_ifs <;> simp [abs_nonneg]
  have hf_le : ∀ x, f x ≤ 1 := by
    intro x; have := hη x; simp only [hf_def]; split_ifs
    · rw [abs_le]; constructor <;> linarith [this.1, this.2]
    · norm_num
  have hg_nn : ∀ x, 0 ≤ g x := fun x => by simp only [hg_def]; linarith [hΦstar_min x (h x)]
  have hfg : ∀ x, f x ^ s ≤ c ^ s * g x := by
    intro x
    simp only [hf_def, hg_def]
    split_ifs with hb
    · have := hbound x
      have hz := csb_phi_zero_le (fun _ => η x) Φ (hη x) hΦconv hΦmono (h x) hb
      simp only [BayesScore] at this
      have hcs : 0 ≤ c ^ s := Real.rpow_nonneg hc.le _
      calc |η x - 1/2| ^ s ≤ c ^ s * (PhiLossPointwise η Φ x 0 - PhiLossPointwise η Φ x (hΦstar x)) := this
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ hcs
          simp only [PhiLossPointwise] at hz ⊢
          linarith
    · rw [Real.zero_rpow hs0.ne']
      exact mul_nonneg (Real.rpow_nonneg hc.le _) (hg_nn x)
  have hf_int : Integrable f DX := by
    refine Integrable.of_bound hf_meas.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf_nn x)]; exact hf_le x
  have hg_int : Integrable g DX := hh_int.sub hΦstar_int
  have hfs_int : Integrable (fun x => f x ^ s) DX := by
    refine Integrable.mono' (hg_int.const_mul (c ^ s)) (hf_meas.pow_const s).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hf_nn x) _)]; exact hfg x
  -- Jensen
  have hJ : (∫ x, f x ∂DX) ^ s ≤ ∫ x, f x ^ s ∂DX := by
    have := (convexOn_rpow hs).map_integral_le (μ := DX) (f := f)
      ((Real.continuous_rpow_const hs0.le).continuousOn) isClosed_Ici
      (Filter.Eventually.of_forall fun x => (hf_nn x : (0:ℝ) ≤ f x)) hf_int hfs_int
    simpa using this
  have hG : ∫ x, g x ∂DX = ExpectedPhiLoss DX η Φ h - ExpectedPhiLoss DX η Φ hΦstar := by
    simp only [hg_def, ExpectedPhiLoss]; exact integral_sub hh_int hΦstar_int
  have hG_nn : 0 ≤ ∫ x, g x ∂DX := integral_nonneg hg_nn
  have h2 : (∫ x, f x ∂DX) ^ s ≤ c ^ s * ∫ x, g x ∂DX := by
    calc _ ≤ _ := hJ
      _ ≤ ∫ x, c ^ s * g x ∂DX := integral_mono hfs_int (hg_int.const_mul _) hfg
      _ = _ := integral_const_mul _ _
  have hI_nn : 0 ≤ ∫ x, f x ∂DX := integral_nonneg hf_nn
  have h3 : ∫ x, f x ∂DX ≤ c * (∫ x, g x ∂DX) ^ (1 / s) := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg hI_nn s) h2 (z := 1 / s) (by positivity)
    rwa [← Real.rpow_mul hI_nn, mul_one_div_cancel hs0.ne', Real.rpow_one,
      Real.mul_rpow (Real.rpow_nonneg hc.le _) hG_nn, ← Real.rpow_mul hc.le,
      mul_one_div_cancel hs0.ne', Real.rpow_one] at this
  -- risk difference
  have hR : ScoringRisk DX η h - ScoringRisk DX η (BayesScore η) ≤ 2 * ∫ x, f x ∂DX := by
    have hb1 : ∀ k : X → ℝ, Measurable k → Integrable (fun x => η x * (if k x < 0 then (1 : ℝ) else 0) +
        (1 - η x) * (if k x ≥ 0 then (1 : ℝ) else 0)) DX := by
      intro k hk
      refine Integrable.of_bound ?_ 2 (Filter.Eventually.of_forall fun x => ?_)
      · apply Measurable.aestronglyMeasurable
        apply Measurable.add
        · exact hη_meas.mul (Measurable.ite (measurableSet_lt hk measurable_const) measurable_const measurable_const)
        · exact (measurable_const.sub hη_meas).mul (Measurable.ite (measurableSet_le measurable_const hk) measurable_const measurable_const)
      · have := hη x
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> split_ifs <;> nlinarith [this.1, this.2]
    have hBm : Measurable (BayesScore η) := by
      show Measurable (fun x => η x - 1/2); exact hη_meas.sub measurable_const
    unfold ScoringRisk
    rw [← integral_sub (hb1 h hh_meas) (hb1 _ hBm), ← integral_const_mul]
    apply integral_mono ((hb1 h hh_meas).sub (hb1 _ hBm))
      (hf_int.const_mul 2)
    intro x
    have := hη x
    show (η x * (if h x < 0 then (1:ℝ) else 0) + (1 - η x) * (if h x ≥ 0 then (1:ℝ) else 0)) -
      (η x * (if η x - 1/2 < 0 then (1:ℝ) else 0) + (1 - η x) * (if η x - 1/2 ≥ 0 then (1:ℝ) else 0))
      ≤ 2 * (if (h x < 0 ∧ 1/2 ≤ η x) ∨ (0 ≤ h x ∧ η x < 1/2) then |η x - 1/2| else 0)
    rcases lt_or_ge (h x) 0 with h1 | h1 <;> rcases lt_or_ge (η x) (1/2) with h2 | h2
    · have e1 : ¬ (h x < 0 ∧ 1/2 ≤ η x ∨ 0 ≤ h x ∧ η x < 1/2) := by
        rintro (⟨_, _⟩ | ⟨_, _⟩) <;> linarith
      rw [if_neg e1, if_pos h1, if_neg (show ¬ h x ≥ 0 by intro; linarith),
        if_pos (show η x - 1/2 < 0 by linarith), if_neg (show ¬ η x - 1/2 ≥ 0 by intro; linarith)]
      linarith
    · have e1 : (h x < 0 ∧ 1/2 ≤ η x ∨ 0 ≤ h x ∧ η x < 1/2) := Or.inl ⟨h1, h2⟩
      rw [if_pos e1, if_pos h1, if_neg (show ¬ h x ≥ 0 by intro; linarith),
        if_neg (show ¬ η x - 1/2 < 0 by intro; linarith), if_pos (show η x - 1/2 ≥ 0 by linarith),
        abs_of_nonneg (show (0:ℝ) ≤ η x - 1/2 by linarith)]
      linarith
    · have e1 : (h x < 0 ∧ 1/2 ≤ η x ∨ 0 ≤ h x ∧ η x < 1/2) := Or.inr ⟨h1, h2⟩
      rw [if_pos e1, if_neg (show ¬ h x < 0 by intro; linarith), if_pos (show h x ≥ 0 from h1),
        if_pos (show η x - 1/2 < 0 by linarith), if_neg (show ¬ η x - 1/2 ≥ 0 by intro; linarith),
        abs_of_neg (show η x - 1/2 < 0 by linarith)]
      linarith
    · have e1 : ¬ (h x < 0 ∧ 1/2 ≤ η x ∨ 0 ≤ h x ∧ η x < 1/2) := by
        rintro (⟨_, _⟩ | ⟨_, _⟩) <;> linarith
      rw [if_neg e1, if_neg (show ¬ h x < 0 by intro; linarith), if_pos (show h x ≥ 0 from h1),
        if_neg (show ¬ η x - 1/2 < 0 by intro; linarith), if_pos (show η x - 1/2 ≥ 0 by linarith)]
      linarith
  rw [← hG]
  nlinarith [h3]

end FoundationsML.ModelSelection

open FoundationsML.ModelSelection


theorem solution {X : Type*} [MeasurableSpace X] (DX : Measure X)
    [IsProbabilityMeasure DX] (η : X → ℝ) (hη_meas : Measurable η)
    (hη : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) (Φ : ℝ → ℝ)
    (hΦconv : ConvexOn ℝ Set.univ Φ) (hΦmono : Monotone Φ)
    (hΦstar : X → ℝ) (hΦstar_meas : Measurable hΦstar)
    (hΦstar_min : ∀ x u, PhiLossPointwise η Φ x (hΦstar x) ≤ PhiLossPointwise η Φ x u)
    (hΦstar_int : Integrable (fun x => PhiLossPointwise η Φ x (hΦstar x)) DX)
    (s c : ℝ) (hs : 1 ≤ s) (hc : 0 < c)
    (hbound : ∀ x, |BayesScore η x| ^ s ≤
      c ^ s * (PhiLossPointwise η Φ x 0 - PhiLossPointwise η Φ x (hΦstar x)))
    (h : X → ℝ) (hh_meas : Measurable h)
    (hh_int : Integrable (fun x => PhiLossPointwise η Φ x (h x)) DX) :
    ScoringRisk DX η h - ScoringRisk DX η (BayesScore η) ≤
      2 * c * (ExpectedPhiLoss DX η Φ h - ExpectedPhiLoss DX η Φ hΦstar) ^ (1 / s) := by
  exact csb_core DX η hη_meas hη Φ hΦconv hΦmono hΦstar hΦstar_meas hΦstar_min hΦstar_int s c hs hc hbound h hh_meas hh_int
