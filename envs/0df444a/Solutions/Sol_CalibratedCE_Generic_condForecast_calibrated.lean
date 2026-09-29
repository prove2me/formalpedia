-- Prove2me | solution 1 for CalibratedCE.Generic.condForecast_calibrated
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:40:12.152992+00:00
-- url     : https://prove2.me/submissions/e0a2397d-2371-4f6a-9616-b7ef43c1c3b9

import Mathlib
import Definitions.Def_CalibratedCE_Generic_Game
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Generic_Forecasts

open Filter Topology

namespace CalibratedCE.Generic

/-- Fiberwise counting: rounds whose forecast `F (x s)` equals `p` split according to `x s`. -/
theorem aux_ccf_count {α β : Type} [Fintype α] [DecidableEq α] [DecidableEq β]
    (x : ℕ → α) (F : α → β) (P : ℕ → Prop) [DecidablePred P] (p : β) (t : ℕ) :
    ((Finset.range t).filter (fun s => F (x s) = p ∧ P s)).card =
      ∑ a ∈ Finset.univ.filter (fun a => F a = p),
        ((Finset.range t).filter (fun s => x s = a ∧ P s)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := x) (t := Finset.univ.filter (fun a => F a = p))]
  · apply Finset.sum_congr rfl
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    congr 1
    ext s
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, _, h3⟩, h4⟩
      exact ⟨h1, h4, h3⟩
    · rintro ⟨h1, h4, h3⟩
      exact ⟨⟨h1, h4 ▸ ha, h3⟩, h4⟩
  · intro s hs
    simp only [Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hs ⊢
    exact hs.2.1

/-- Calibration of the conditional forecasts of player 1. -/
theorem aux_ccf_cal {m n : ℕ} (D : Fin m → Fin n → ℝ) (hD0 : ∀ a b, 0 ≤ D a b)
    (x : ℕ → Fin m) (y : ℕ → Fin n)
    (hlim : ∀ a b, Tendsto (fun t => empDist x y t a b) atTop (𝓝 (D a b))) :
    Shared.Calibrated (fun t => condForecast₁ D (x t)) y := by
  intro j
  set f : ℕ → Fin n → ℝ := fun t => condForecast₁ D (x t) with hf
  set S : Finset (Fin n → ℝ) := Finset.univ.image (condForecast₁ D) with hS
  have key : ∀ t, Shared.calibScore f y j t =
      ∑ p ∈ S, |∑ a ∈ Finset.univ.filter (fun a => condForecast₁ D a = p),
        (empDist x y t a j - p j * ∑ b, empDist x y t a b)| := by
    intro t
    unfold Shared.calibScore
    rw [Finset.sum_subset (s₁ := (Finset.range t).image f) (s₂ := S)]
    · apply Finset.sum_congr rfl
      intro p _
      have hC : ((Finset.range t).filter (fun s => f s = p ∧ y s = j)).card =
          ∑ a ∈ Finset.univ.filter (fun a => condForecast₁ D a = p),
            ((Finset.range t).filter (fun s => x s = a ∧ y s = j)).card :=
        aux_ccf_count x (condForecast₁ D) (fun s => y s = j) p t
      have hN : Shared.N f p t = ∑ a ∈ Finset.univ.filter (fun a => condForecast₁ D a = p),
          ∑ b, ((Finset.range t).filter (fun s => x s = a ∧ y s = b)).card := by
        unfold Shared.N
        rw [Finset.card_eq_sum_card_fiberwise (f := y) (t := Finset.univ) (by simp)]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.filter_filter]
        exact aux_ccf_count x (condForecast₁ D) (fun s => y s = b) p t
      have hCN : ((Finset.range t).filter (fun s => f s = p ∧ y s = j)).card ≤ Shared.N f p t := by
        unfold Shared.N
        apply Finset.card_le_card
        intro s hs
        simp only [Finset.mem_filter] at hs ⊢
        exact ⟨hs.1, hs.2.1⟩
      have hR : ∑ a ∈ Finset.univ.filter (fun a => condForecast₁ D a = p),
          (empDist x y t a j - p j * ∑ b, empDist x y t a b) =
          ((((Finset.range t).filter (fun s => f s = p ∧ y s = j)).card : ℝ)
            - p j * (Shared.N f p t : ℝ)) / (t : ℝ) := by
        rw [hC, hN]
        push_cast
        unfold empDist
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro a _
        rw [← Finset.sum_div]
        ring
      rw [hR, abs_div, Nat.abs_cast]
      congr 1
      by_cases h0 : Shared.N f p t = 0
      · have hr : Shared.rho f y p j t = 0 := by simp [Shared.rho, h0]
        have hc : ((Finset.range t).filter (fun s => f s = p ∧ y s = j)).card = 0 := by omega
        rw [hr, h0, hc]
        simp
      · have hr : Shared.rho f y p j t =
            (((Finset.range t).filter (fun s => f s = p ∧ y s = j)).card : ℝ) /
              (Shared.N f p t : ℝ) := by
          simp [Shared.rho, h0]
        have hNpos : (0 : ℝ) < (Shared.N f p t : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero h0
        rw [hr]
        rw [← abs_of_pos hNpos, ← abs_mul, abs_of_pos hNpos]
        congr 1
        field_simp
    · intro p hp
      simp only [Finset.mem_image, Finset.mem_range, hS, Finset.mem_univ, true_and] at hp ⊢
      obtain ⟨s, _, rfl⟩ := hp
      exact ⟨x s, rfl⟩
    · intro p _ hp
      have : Shared.N f p t = 0 := by
        unfold Shared.N
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro s hs hfs
        exact hp (Finset.mem_image.mpr ⟨s, hs, hfs⟩)
      rw [this]
      simp
  have hT : Tendsto (fun t => ∑ p ∈ S, |∑ a ∈ Finset.univ.filter (fun a => condForecast₁ D a = p),
        (empDist x y t a j - p j * ∑ b, empDist x y t a b)|) atTop
      (𝓝 (∑ p ∈ S, |∑ a ∈ Finset.univ.filter (fun a => condForecast₁ D a = p),
        (D a j - p j * ∑ b, D a b)|)) := by
    apply tendsto_finsetSum
    intro p _
    apply Filter.Tendsto.abs
    apply tendsto_finsetSum
    intro a _
    exact (hlim a j).sub ((tendsto_finsetSum _ (fun b _ => hlim a b)).const_mul _)
  have hzero : ∑ p ∈ S, |∑ a ∈ Finset.univ.filter (fun a => condForecast₁ D a = p),
        (D a j - p j * ∑ b, D a b)| = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    rw [abs_eq_zero]
    apply Finset.sum_eq_zero
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    subst ha
    simp only [condForecast₁]
    by_cases hs : ∑ c, D a c = 0
    · have h1 : D a j = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => hD0 a c)).mp hs j (Finset.mem_univ _)
      rw [h1, hs]
      simp
    · rw [div_mul_cancel₀ _ hs, sub_self]
  rw [hzero] at hT
  exact hT.congr (fun t => (key t).symm)

theorem aux_ccf_isDist {m n : ℕ} (D : Fin m → Fin n → ℝ) (hD0 : ∀ a b, 0 ≤ D a b)
    (a : Fin m) (b : Fin n) (hpos : 0 < D a b) : IsDist (condForecast₁ D a) := by
  have hs : 0 < ∑ c, D a c :=
    lt_of_lt_of_le hpos (Finset.single_le_sum (fun c _ => hD0 a c) (Finset.mem_univ b))
  refine ⟨fun c => div_nonneg (hD0 a c) hs.le, ?_⟩
  simp only [condForecast₁]
  rw [← Finset.sum_div, div_self hs.ne']

end CalibratedCE.Generic

open CalibratedCE CalibratedCE.Generic
open Filter Topology

theorem solution {m n : ℕ} (D : Fin m → Fin n → ℝ) (hD : IsJointDist D)
    (x : ℕ → Fin m) (y : ℕ → Fin n) (hsupp : ∀ t, 0 < D (x t) (y t))
    (hlim : ∀ a b, Tendsto (fun t => empDist x y t a b) atTop (𝓝 (D a b))) :
    (∀ t, IsDist (condForecast₁ D (x t))) ∧ (∀ t, IsDist (condForecast₂ D (y t))) ∧
      Shared.Calibrated (fun t => condForecast₁ D (x t)) y ∧
      Shared.Calibrated (fun t => condForecast₂ D (y t)) x := by
  refine ⟨fun t => aux_ccf_isDist D hD.1 (x t) (y t) (hsupp t),
    fun t => aux_ccf_isDist (fun b a => D a b) (fun b a => hD.1 a b) (y t) (x t) (hsupp t),
    aux_ccf_cal D hD.1 x y hlim, ?_⟩
  have hlim' : ∀ b a, Tendsto (fun t => empDist y x t b a) atTop (𝓝 (D a b)) := by
    intro b a
    refine (hlim a b).congr (fun t => ?_)
    unfold empDist
    congr 3
    ext s
    simp only [Finset.mem_filter]
    tauto
  exact aux_ccf_cal (fun b a => D a b) (fun b a => hD.1 a b) y x hlim'
