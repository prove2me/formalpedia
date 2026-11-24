-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.phi15_is_unit_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:47.305315+00:00
-- url     : https://prove2.me/submissions/7446a0fb-5568-400a-955e-5446f6636b73

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_PrimitiveRootFifteenSubOneUnit
import Mathlib
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Adjugate
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Mobius
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Window
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Koszul
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Parabolic
import Definitions.Def_Formalism_ResultantValuation_BoundedCubic
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Laplace
import Definitions.Def_Formalism_ResultantValuation_PrimePairDyadicDisjointAlt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_natAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_natAdd
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.glue_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.glue_natAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_natAdd
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z
namespace Formalism.IrreducibleCountingLemmas.Z
theorem _root_.solution : PrimitiveRootFifteenSubOneUnit := by
  intro R _ _ ζ hζ
  have hnp : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, p ^ k ≠ 15 := by
    intro p hp k h
    have h3 : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow (show 3 ∣ p ^ k by rw [h]; norm_num)
    have h5 : 5 ∣ p := (by norm_num : Nat.Prime 5).dvd_of_dvd_pow (show 5 ∣ p ^ k by rw [h]; norm_num)
    have e3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3
    have e5 := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 5) hp).mp h5
    omega
  have hev : (Polynomial.cyclotomic 15 R).eval 1 = 1 := Polynomial.eval_one_cyclotomic_not_prime_pow hnp
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at hev
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hev
  have hmem : ζ ∈ primitiveRoots 15 R := (mem_primitiveRoots (by norm_num)).mpr hζ
  have hdvd : (1 - ζ) ∣ 1 := (Finset.dvd_prod_of_mem (fun μ => (1 : R) - μ) hmem).trans hev.dvd
  have hu : IsUnit (1 - ζ) := isUnit_of_dvd_one hdvd
  rw [show ζ - 1 = -(1 - ζ) by ring]
  exact hu.neg
end Formalism.IrreducibleCountingLemmas.Z
