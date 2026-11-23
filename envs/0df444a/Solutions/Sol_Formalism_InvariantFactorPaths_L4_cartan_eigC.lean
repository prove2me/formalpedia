-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.cartan_eigC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:03.60024+00:00
-- url     : https://prove2.me/submissions/5dc778d6-0ba3-4deb-9b82-0c60efba9ad3

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Theorems.Thm_Formalism_CountingSumsFrames_coeff_cartan
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
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
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (μ : Fin r → ℤ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hx : x ∈ WtSpC p LL j Cs μ) (c : Fin r) (hc : c ∈ Cs) :
    glAct p LL j c c x = ((μ c : ℤ) : ℚ_[p]) • x := by
  rw [WtSpC, mem_restrictSupport_iff] at hx
  ext m
  rw [coeff_cartan, coeff_smul, smul_eq_mul]
  by_cases h : coeff m x = 0
  · simp [h]
  · have hm := hx (Finset.mem_coe.mpr (mem_support_iff.mpr h))
    rw [Set.mem_setOf_eq] at hm
    rw [hm c hc]
end Formalism.InvariantFactorPaths.L4
