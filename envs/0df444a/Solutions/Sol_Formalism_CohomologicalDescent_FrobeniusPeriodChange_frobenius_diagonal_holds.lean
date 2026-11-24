-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.frobenius_diagonal_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:14:55.732947+00:00
-- url     : https://prove2.me/submissions/3ca430c1-57e3-4e91-9c1d-fb87edca7460

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_frobenius_laws_hold

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution : PhiDiag := by
  intro k _ l s p v w w' κ κ' hl heq
  obtain ⟨-, hmul, hC, -⟩ := frobenius_laws_hold k l hl
  let φ : k⟦X⟧ →+* LaurentSeries k := HahnSeries.ofPowerSeries ℤ k
  have hφ : Function.Injective φ := HahnSeries.ofPowerSeries_injective
  change φ (frob0 l (w' : k⟦X⟧)) * φ X ^ ((l : ℤ) * κ') * φ ((v : k⟦X⟧) * X ^ s) =
    φ p * φ (w : k⟦X⟧) * φ X ^ κ at heq
  have hx : φ X ≠ 0 := (map_ne_zero_iff φ hφ).2 X_ne_zero
  have hfu : frob0 l (w' : k⟦X⟧) * frob0 l ((w'⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) = 1 := by
    rw [← hmul, Units.mul_inv, ← map_one (C : k →+* k⟦X⟧), hC]
  let A : k⟦X⟧ := frob0 l (w' : k⟦X⟧) * (v : k⟦X⟧) * ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧)
  have hF : IsUnit (frob0 l (w' : k⟦X⟧)) := ⟨⟨_, _, hfu, by rw [mul_comm]; exact hfu⟩, rfl⟩
  have hA : IsUnit A := (hF.mul v.isUnit).mul (w⁻¹).isUnit
  have hww : φ (w : k⟦X⟧) * φ ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  set e : ℤ := (l : ℤ) * κ' + (s : ℤ) - κ with he
  have key : φ p = φ A * φ X ^ e := by
    have h1 : φ p * φ (w : k⟦X⟧) * φ X ^ κ * (φ ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) * φ X ^ (-κ)) = φ p := by
      rw [show φ p * φ (w : k⟦X⟧) * φ X ^ κ * (φ ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) * φ X ^ (-κ)) =
        φ p * (φ (w : k⟦X⟧) * φ ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧)) * (φ X ^ κ * φ X ^ (-κ)) by ring, hww,
        ← zpow_add₀ hx, add_neg_cancel, zpow_zero, mul_one, mul_one]
    rw [← h1, ← heq]
    simp only [A, map_mul, map_pow]
    rw [he, sub_eq_add_neg, zpow_add₀ hx, zpow_add₀ hx, zpow_natCast]
    ring
  by_cases he0 : 0 ≤ e
  · refine ⟨he0, hA.unit, hφ ?_⟩
    rw [IsUnit.unit_spec, map_mul, map_pow, key, ← zpow_natCast, Int.toNat_of_nonneg he0]
  · exfalso
    push_neg at he0
    have hm : φ p * φ X ^ (-e) = φ A := by
      rw [key, mul_assoc, ← zpow_add₀ hx, add_neg_cancel, zpow_zero, mul_one]
    obtain ⟨m, hm'⟩ : ∃ m : ℕ, -e = (m : ℤ) + 1 := ⟨(-e - 1).toNat, by omega⟩
    rw [hm', zpow_add_one₀ hx, zpow_natCast, ← map_pow, ← map_mul, ← map_mul] at hm
    have h5 := congrArg constantCoeff (hφ hm)
    simp only [map_mul, constantCoeff_X, mul_zero] at h5
    exact (hA.map constantCoeff).ne_zero h5.symm
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
