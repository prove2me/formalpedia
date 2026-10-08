-- Prove2me | solution 1 for BesbesZeevi.Parametric.fact1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:27:28.34402+00:00
-- url     : https://prove2.me/submissions/3a14db8d-6752-4da8-9449-486a2f072ca6

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_Model

open MeasureTheory Pointwise

namespace BesbesZeevi.Parametric

lemma detFeasible_scale_iff_b58 (D : Market) (lam : ℝ → ℝ) (x c : ℝ) (hc : 0 < c)
    (p : ℝ → ℝ) :
    DetFeasible D (fun q => c * lam q) (c * x) p ↔ DetFeasible D lam x p := by
  unfold DetFeasible
  have hu : IsUnit c := isUnit_iff_ne_zero.mpr hc.ne'
  have h1 : IntegrableOn (fun t => c * lam (p t)) (Set.Icc (0 : ℝ) D.T) ↔
      IntegrableOn (fun t => lam (p t)) (Set.Icc (0 : ℝ) D.T) :=
    integrable_const_mul_iff hu _
  have h2e : (fun t => p t * (c * lam (p t))) = (fun t => c * (p t * lam (p t))) := by
    funext t; ring
  have h2 : IntegrableOn (fun t => p t * (c * lam (p t))) (Set.Icc (0 : ℝ) D.T) ↔
      IntegrableOn (fun t => p t * lam (p t)) (Set.Icc (0 : ℝ) D.T) := by
    rw [h2e]; exact integrable_const_mul_iff hu _
  have h3 : (∫ t in Set.Icc (0 : ℝ) D.T, c * lam (p t)) =
      c * ∫ t in Set.Icc (0 : ℝ) D.T, lam (p t) := integral_const_mul c _
  simp only []
  rw [h1, h2, h3, mul_le_mul_iff_of_pos_left hc]

lemma jDet_scale_b58 (D : Market) (lam : ℝ → ℝ) (x c : ℝ) (hc : 0 < c) :
    jDet D (fun q => c * lam q) (c * x) = c * jDet D lam x := by
  unfold jDet
  have hset : {v : ℝ | ∃ p : ℝ → ℝ, DetFeasible D (fun q => c * lam q) (c * x) p ∧
      v = ∫ t in Set.Icc (0 : ℝ) D.T, p t * (fun q => c * lam q) (p t)} =
      c • {v : ℝ | ∃ p : ℝ → ℝ, DetFeasible D lam x p ∧
        v = ∫ t in Set.Icc (0 : ℝ) D.T, p t * lam (p t)} := by
    have hint : ∀ p : ℝ → ℝ, (∫ t in Set.Icc (0 : ℝ) D.T, p t * (fun q => c * lam q) (p t))
        = c * ∫ t in Set.Icc (0 : ℝ) D.T, p t * lam (p t) := by
      intro p
      rw [← integral_const_mul]
      congr 1
      funext t
      simp only []
      ring
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_smul_set, smul_eq_mul,
      detFeasible_scale_iff_b58 D lam x c hc, hint]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p, hp, rfl⟩
  rw [hset, Real.sSup_smul_of_nonneg hc.le, smul_eq_mul]

lemma jDet_lower_b58 (D : Market) (lam γ : ℝ → ℝ) (h : IsRegularDemand D lam γ) :
    D.m * min D.T (D.x / D.M) ≤ jDet D lam D.x := by
  obtain ⟨hoff, hbd, -, -, -, -, -, -, ⟨ps, hps, hm⟩⟩ := h
  set τ := min D.T (D.x / D.M) with hτ
  have hτ0 : 0 ≤ τ := le_min D.T_pos.le (div_pos D.x_pos D.M_pos).le
  have hτT : τ ≤ D.T := min_le_left _ _
  have hτx : τ ≤ D.x / D.M := min_le_right _ _
  have hps0 : 0 < ps := lt_of_lt_of_le D.pLo_pos hps.1
  obtain ⟨hl0, hlM⟩ := hbd ps hps
  -- the path
  let p : ℝ → ℝ := fun t => if t ≤ τ then ps else D.pOff
  have hpm : Measurable p :=
    Measurable.ite measurableSet_Iic measurable_const measurable_const
  have hlam : (fun t => lam (p t)) = (Set.Iic τ).indicator (fun _ => lam ps) := by
    funext t
    simp only [p, Set.indicator, Set.mem_Iic]
    split_ifs <;> simp [hoff]
  have hrev : (fun t => p t * lam (p t)) = (Set.Iic τ).indicator (fun _ => ps * lam ps) := by
    funext t
    simp only [p, Set.indicator, Set.mem_Iic]
    split_ifs <;> simp [hoff]
  have hmeas : (volume.restrict (Set.Icc (0 : ℝ) D.T)) (Set.Iic τ) = ENNReal.ofReal τ := by
    rw [Measure.restrict_apply measurableSet_Iic]
    have : Set.Iic τ ∩ Set.Icc (0 : ℝ) D.T = Set.Icc 0 τ := by
      ext t; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, le_trans h2 hτT⟩
    rw [this, Real.volume_Icc, sub_zero]
  have hint_c : ∀ a : ℝ, (∫ t in Set.Icc (0 : ℝ) D.T, (Set.Iic τ).indicator (fun _ => a) t)
      = τ * a := by
    intro a
    rw [integral_indicator_const a measurableSet_Iic, measureReal_def, hmeas,
      ENNReal.toReal_ofReal hτ0, smul_eq_mul]
  have hfin : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) D.T)) := by
    rw [isFiniteMeasure_restrict]; exact measure_Icc_lt_top.ne
  have hintegr : ∀ a : ℝ, IntegrableOn ((Set.Iic τ).indicator (fun _ => a))
      (Set.Icc (0 : ℝ) D.T) := by
    intro a
    exact (integrable_const a).indicator measurableSet_Iic
  have hfeas : DetFeasible D lam D.x p := by
    refine ⟨hpm, ?_, ?_, ?_, ?_⟩
    · intro t _
      simp only [p]
      split_ifs
      · exact Or.inl hps
      · exact Or.inr rfl
    · rw [hlam]; exact hintegr _
    · rw [hrev]; exact hintegr _
    · rw [hlam, hint_c]
      calc τ * lam ps ≤ (D.x / D.M) * D.M :=
            mul_le_mul hτx hlM hl0 (div_pos D.x_pos D.M_pos).le
        _ = D.x := div_mul_cancel₀ _ D.M_pos.ne'
  -- boundedness
  have hbdd : BddAbove {v : ℝ | ∃ p : ℝ → ℝ, DetFeasible D lam D.x p ∧
      v = ∫ t in Set.Icc (0 : ℝ) D.T, p t * lam (p t)} := by
    refine ⟨∫ t in Set.Icc (0 : ℝ) D.T, D.pHi * D.M, ?_⟩
    rintro v ⟨q, hq, rfl⟩
    obtain ⟨-, hrange, -, hqi, -⟩ := hq
    refine setIntegral_mono_on hqi (integrableOn_const measure_Icc_lt_top.ne) measurableSet_Icc ?_
    intro t ht
    have hHi : 0 < D.pHi := lt_trans D.pLo_pos D.price_order
    rcases hrange t ht with hq' | hq'
    · obtain ⟨a, b⟩ := hbd (q t) hq'
      have hq0 : 0 < q t := lt_of_lt_of_le D.pLo_pos hq'.1
      exact mul_le_mul hq'.2 b a hHi.le
    · rw [hq', hoff, mul_zero]
      exact (mul_pos hHi D.M_pos).le
  have hval : τ * (ps * lam ps) ∈ {v : ℝ | ∃ p : ℝ → ℝ, DetFeasible D lam D.x p ∧
      v = ∫ t in Set.Icc (0 : ℝ) D.T, p t * lam (p t)} :=
    ⟨p, hfeas, by rw [hrev, hint_c]⟩
  unfold jDet
  calc D.m * τ ≤ τ * (ps * lam ps) := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left hm hτ0
    _ ≤ _ := le_csSup hbdd hval

end BesbesZeevi.Parametric

set_option autoImplicit false

open BesbesZeevi.Parametric in
theorem solution {k : ℕ} (D : Market) (F : Family k D) :
    (∀ θ ∈ F.Θ, ∀ n : ℕ, 1 ≤ n →
      jDetScaled D F θ n = (n : ℝ) * jDet D (fun p => F.demand p θ) D.x) ∧
    (∀ θ ∈ F.Θ,
      D.m * min D.T (D.x / D.M) ≤ jDet D (fun p => F.demand p θ) D.x) := by
  refine ⟨?_, ?_⟩
  · intro θ _ n hn
    have hc : (0 : ℝ) < n := by exact_mod_cast hn
    unfold jDetScaled
    exact jDet_scale_b58 D (fun p => F.demand p θ) D.x n hc
  · intro θ hθ
    exact jDet_lower_b58 D _ _ (F.regular θ hθ)
