-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.dpow_int_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:11:48.031951+00:00
-- url     : https://prove2.me/submissions/1ffad1ed-4d85-4804-9c43-fd85684b6ef6

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_dpow_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_dpow_succ_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_sq_X
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_X_mul_int
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_dpow_succ_C
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_X_mul_int_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_intPol_iff_norm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (LL : Letters N) (j : ℕ)
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (c : Fin r) (hc : c ≠ 0) (P : MvPolynomial (Fin N × Fin r) ℤ_[p]) :
    ∀ k, dpow p LL j c k (map (algebraMap ℤ_[p] ℚ_[p]) P) ∈ IntPol p (Fin N × Fin r) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro k
    rw [map_C]
    cases k with
    | zero =>
      rw [dpow_zero, intPol_iff_norm]
      intro m
      rw [coeff_C]
      split_ifs
      · exact PadicInt.norm_le_one a
      · simp
    | succ k => rw [dpow_succ_C]; exact Submodule.zero_mem _
  | add f g hf hg =>
    intro k
    rw [map_add, map_add]
    exact Submodule.add_mem _ (hf k) (hg k)
  | mul_X f v hf =>
    intro k
    rw [map_mul, map_X, mul_comm]
    cases k with
    | zero =>
      rw [dpow_zero, X_mul_int_iff]
      have := hf 0
      rwa [dpow_zero] at this
    | succ k =>
      rw [dpow_succ_mul p LL j c _ _ (glAct_sq_X p LL j c hc v) k]
      exact Submodule.add_mem _ ((X_mul_int_iff _ _).2 (hf _)) (glAct_X_mul_int p LL j c v _ (hf k))
end Formalism.InvariantFactorPaths.L4
