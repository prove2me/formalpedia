-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.odd_cyc_inertia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:49:12.272923+00:00
-- url     : https://prove2.me/submissions/9ef70b6a-b06b-4513-9e54-8966f4d49a2e

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_InvLength
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_natCast_not_mem
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_two_pow_not_dvd
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_eq_one_of_sub_one_mem
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_autToPow_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution {L : Type} [Field L] [NumberField L] {n : ℕ} {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ n)) (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(r : ℤ)})]
    (σ : Gal(L/ℚ)) (hσ : ∀ x : 𝓞 L, σ • x - x ∈ P) : hζ.autToPow ℚ σ = 1 := by
  set Z := hζ.toInteger with hZdef
  have hZ : IsPrimitiveRoot Z (2 ^ n) := hζ.toInteger_isPrimitiveRoot
  set e := ((hζ.autToPow ℚ σ : ZMod (2 ^ n))).val with he
  have h1 : Z ^ e - Z ∈ P := by rw [← odd_autToPow_smul hζ σ]; exact hσ Z
  have hm1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hZm : Z ^ (2 ^ n - 1) * Z = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hm1, hZ.pow_eq_one]
  have hη : (Z ^ e * Z ^ (2 ^ n - 1)) ^ (2 ^ n) = 1 := by
    rw [← pow_add, ← pow_mul, mul_comm, pow_mul, hZ.pow_eq_one, one_pow]
  have hsub : Z ^ e * Z ^ (2 ^ n - 1) - 1 ∈ P := by
    have : Z ^ e * Z ^ (2 ^ n - 1) - 1 = (Z ^ e - Z) * Z ^ (2 ^ n - 1) := by
      linear_combination hZm
    rw [this]
    exact P.mul_mem_right _ h1
  have hm : ((2 ^ n : ℕ) : 𝓞 L) ∉ P := odd_natCast_not_mem r P _ (odd_two_pow_not_dvd r n hr hr2)
  have hone := odd_eq_one_of_sub_one_mem P hη hm hsub
  rw [← pow_add, hZ.pow_eq_one_iff_dvd] at hone
  have h2 : e + (2 ^ n - 1) ≡ 1 + (2 ^ n - 1) [MOD 2 ^ n] := by
    rw [Nat.add_sub_cancel' hm1]
    exact (Nat.modEq_zero_iff_dvd.mpr hone).trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl).symm
  have h3 : e ≡ 1 [MOD 2 ^ n] := Nat.ModEq.add_right_cancel' _ h2
  have h4 : (e : ZMod (2 ^ n)) = ((1 : ℕ) : ZMod (2 ^ n)) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr h3
  rw [he, ZMod.natCast_zmod_val, Nat.cast_one] at h4
  exact Units.ext (by rw [h4, Units.val_one])
end Formalism.TwoAdicCyclotomicDecomposition
