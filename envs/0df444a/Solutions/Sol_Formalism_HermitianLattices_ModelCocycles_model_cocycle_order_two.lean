-- Prove2me | solution 1 for Formalism.HermitianLattices.ModelCocycles.model_cocycle_order_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:57.35762+00:00
-- url     : https://prove2.me/submissions/66e464b9-42d4-4dff-a1a6-5196fefb4fc7

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ModelCocycleExponent
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_TeichmullerUnitAllPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ModelCocycles
open Finset Formalism.HermitianLattices.IntegralLatticeDensity
namespace Formalism.HermitianLattices.ModelCocycles
theorem _root_.solution : ModelCocycleTwo := by
  intro d hd
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, d + 1 = 8 * m := ⟨(d + 1) / 8, by omega⟩
  have n2 : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by have := Padic.norm_p (p := 2); simpa using this
  refine ⟨?_, ?_⟩
  · have n2' : ‖(2 : ℤ_[2])‖ = 2⁻¹ := by have := PadicInt.norm_p (p := 2); simpa using this
    have H := hensels_lemma (p := 2) (R := ℤ_[2])
      (F := Polynomial.X ^ 2 + Polynomial.C (d : ℤ_[2])) (a := 1) (by
        have e1 : Polynomial.aeval (1 : ℤ_[2]) (Polynomial.X ^ 2 + Polynomial.C (d : ℤ_[2])) =
            2 ^ 3 * (m : ℤ_[2]) := by
          have : ((d + 1 : ℕ) : ℤ_[2]) = ((8 * m : ℕ) : ℤ_[2]) := by rw [hm]
          push_cast at this
          simp
          linear_combination this
        have e2 : Polynomial.aeval (1 : ℤ_[2])
            (Polynomial.derivative (Polynomial.X ^ 2 + Polynomial.C (d : ℤ_[2]))) = 2 := by
          simp; norm_num
        rw [e1, e2, norm_mul, norm_pow, n2']
        have := PadicInt.norm_le_one (m : ℤ_[2])
        have h0 := norm_nonneg (m : ℤ_[2])
        nlinarith)
    obtain ⟨z, hz, _⟩ := H
    refine ⟨(z : ℚ_[2]), ?_⟩
    have hz' : z ^ 2 + (d : ℤ_[2]) = 0 := by simpa using hz
    have := congrArg (fun w : ℤ_[2] => (w : ℚ_[2])) hz'
    push_cast at this
    linear_combination this
  · intro δ hδ
    have nd : ‖(d : ℚ_[2])‖ = 1 := by
      rw [Padic.norm_natCast_eq_one_iff]
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; omega
    have nδ : ‖δ‖ = 1 := by
      have : ‖δ‖ ^ 2 = 1 := by rw [← norm_pow, hδ, norm_neg, nd]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 this
    have δ0 : δ ≠ 0 := by intro h; rw [h, norm_zero] at nδ; exact zero_ne_one nδ
    let z : ℤ_[2] := ⟨δ, nδ.le⟩
    have hz : (z : ℚ_[2]) = δ := rfl
    have hz2 : z ^ 2 = -(d : ℤ_[2]) := by
      apply PadicInt.ext; push_cast; rw [hz, hδ]
    have hprod : (1 - z) * (1 + z) = 2 * (4 * (m : ℤ_[2])) := by
      have : ((d + 1 : ℕ) : ℤ_[2]) = ((8 * m : ℕ) : ℤ_[2]) := by rw [hm]
      push_cast at this
      linear_combination this - hz2
    have pr : Prime (2 : ℤ_[2]) := by have := PadicInt.prime_p (p := 2); simpa using this
    have both : (2 : ℤ_[2]) ∣ 1 - z ∧ (2 : ℤ_[2]) ∣ 1 + z := by
      rcases pr.dvd_or_dvd (Dvd.intro _ hprod.symm) with h | h
      · refine ⟨h, ?_⟩
        have : 1 + z = 2 - (1 - z) := by ring
        rw [this]; exact dvd_sub (dvd_refl _) h
      · refine ⟨?_, h⟩
        have : 1 - z = 2 - (1 + z) := by ring
        rw [this]; exact dvd_sub (dvd_refl _) h
    obtain ⟨⟨c, hc⟩, ⟨c', hc'⟩⟩ := both
    have hcq : 1 - δ = 2 * (c : ℚ_[2]) := by
      have := congrArg (fun w : ℤ_[2] => (w : ℚ_[2])) hc
      push_cast at this; rwa [hz] at this
    have hcq' : 1 + δ = 2 * (c' : ℚ_[2]) := by
      have := congrArg (fun w : ℤ_[2] => (w : ℚ_[2])) hc'
      push_cast at this; rwa [hz] at this
    refine ⟨?_, ?_, ?_⟩
    · rw [hcq, mul_div_mul_left _ _ two_ne_zero, norm_div, nδ, div_one]; exact c.2
    · rw [hcq', norm_div, norm_neg, ← norm_div, mul_div_mul_left _ _ two_ne_zero, norm_div, nδ, div_one]
      exact c'.2
    · intro a b
      field_simp
      ring
end Formalism.HermitianLattices.ModelCocycles
