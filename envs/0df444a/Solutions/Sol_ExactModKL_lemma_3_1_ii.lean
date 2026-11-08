-- Prove2me | solution 1 for ExactModKL.lemma_3_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:54:16.272654+00:00
-- url     : https://prove2.me/submissions/3e60340a-28c7-48a1-bf9f-2f92070ff527

import Mathlib
import Definitions.Def_ExactModKL_Ieta
import Definitions.Def_ExactModKL_leftDeriv
import Definitions.Def_ExactModKL_PhiClass

open scoped ENNReal

open ExactModKL in
theorem solution (η : ℝ≥0∞) (hη : 0 < η) (ϕ : ℝ → ℝ) (hconc : ConcaveOn ℝ (ExactModKL.Ieta η) ϕ)
    (hϕ : ExactModKL.PhiClass η ϕ) :
    AntitoneOn (ExactModKL.leftDeriv ϕ) {t | 0 < t ∧ ENNReal.ofReal t < η} ∧
      ∀ t : ℝ, 0 < t → ENNReal.ofReal t < η → 0 < ExactModKL.leftDeriv ϕ t := by
  have hOpen : IsOpen {t : ℝ | 0 < t ∧ ENNReal.ofReal t < η} :=
    (isOpen_lt continuous_const continuous_id).inter
      (isOpen_lt ENNReal.continuous_ofReal continuous_const)
  have hS : {t : ℝ | 0 < t ∧ ENNReal.ofReal t < η} ⊆ interior (ExactModKL.Ieta η) := by
    apply interior_maximal _ hOpen
    intro t ht
    exact ⟨ht.1.le, ht.2⟩
  have hmono := hconc.neg.monotoneOn_leftDeriv
  constructor
  · intro x hx y hy hxy
    have := hmono (hS hx) (hS hy) hxy
    simp only [derivWithin.neg] at this
    unfold ExactModKL.leftDeriv
    linarith
  · intro t ht0 htη
    have htS : t ∈ {t : ℝ | 0 < t ∧ ENNReal.ofReal t < η} := ⟨ht0, htη⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hOpen t htS
    have hd : dist (t + ε / 2) t < ε := by
      rw [Real.dist_eq, show t + ε / 2 - t = ε / 2 by ring, abs_of_pos (by linarith)]
      linarith
    have hy : t + ε / 2 ∈ {t : ℝ | 0 < t ∧ ENNReal.ofReal t < η} := hball hd
    have hyS : t + ε / 2 ∈ ExactModKL.Ieta η := ⟨hy.1.le, hy.2⟩
    have htI : t ∈ ExactModKL.Ieta η := ⟨ht0.le, htη⟩
    have hty : t < t + ε / 2 := by linarith
    have h1 := hconc.neg.leftDeriv_le_rightDeriv_of_mem_interior (hS htS)
    have h2 := hconc.neg.rightDeriv_le_slope_of_mem_interior (hS htS) hyS hty
    simp only [derivWithin.neg, slope_def_field, Pi.neg_apply] at h1 h2
    have hlt : ϕ t < ϕ (t + ε / 2) := hϕ.2.2.2 htI hyS hty
    have hq : 0 < (ϕ (t + ε / 2) - ϕ t) / (t + ε / 2 - t) := div_pos (by linarith) (by linarith)
    have he : (-ϕ (t + ε / 2) - -ϕ t) / (t + ε / 2 - t) =
        -((ϕ (t + ε / 2) - ϕ t) / (t + ε / 2 - t)) := by ring
    unfold ExactModKL.leftDeriv
    linarith
