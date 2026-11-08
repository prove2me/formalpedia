-- Prove2me | solution 1 for CorrelatedLocalSearch.source_class_mono
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:18:37.306286+00:00
-- url     : https://prove2.me/submissions/31e535a0-a5b2-4d0f-b040-bc1cb21a0fdc

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_SourceClass
import Definitions.Def_CorrelatedLocalSearch_Clause
import Definitions.Def_CorrelatedLocalSearch_walkTau

set_option autoImplicit false

open CorrelatedLocalSearch in
theorem solution (k : ℕ) (hk : 1 ≤ k) :
    (∀ s' s D : ℝ, s' ≤ s → SourceClass k s D ⊆ SourceClass k s' D) ∧
      ∀ (n : ℕ) (Φ : List (Clause k n)) (sel : Selector k n) (x₀ : Fin n → Bool),
        Satisfies Φ x₀ → ∀ ω : ℕ → Fin k, walkTau Φ sel x₀ ω = 0 := by
  refine ⟨fun s' s D hss ν hν => ?_, fun n Φ sel x₀ hx ω => ?_⟩
  · obtain ⟨hprob, hb⟩ := hν
    refine ⟨hprob, fun w => ?_⟩
    have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hm0 : 0 < refMass k w := by
      unfold refMass
      exact pow_pos (inv_pos.mpr (by linarith)) _
    have hm1 : refMass k w ≤ 1 := by
      unfold refMass
      exact pow_le_one₀ (inv_nonneg.mpr (by linarith)) (inv_le_one_of_one_le₀ hkr)
    have h := hb w
    by_cases hD : 0 ≤ D
    · refine le_trans h (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hD))
      exact Real.rpow_le_rpow_of_exponent_ge hm0 hm1 hss
    · push_neg at hD
      have hneg : D * refMass k w ^ s ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hD.le (Real.rpow_nonneg hm0.le _)
      rw [ENNReal.ofReal_of_nonpos hneg] at h
      exact le_trans h (by simp)
  · have h0 : Satisfies Φ (walkState Φ sel x₀ (tapePrefix ω 0)) := by
      have ht : tapePrefix ω 0 = [] := by simp [tapePrefix]
      rw [ht]
      exact hx
    refine le_antisymm ?_ (by simp)
    unfold walkTau
    have := iInf₂_le (f := fun (t : ℕ) (_ : Satisfies Φ (walkState Φ sel x₀ (tapePrefix ω t))) =>
      (t : ℕ∞)) 0 h0
    simpa using this
