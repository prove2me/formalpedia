-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.glRest_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:57.75431+00:00
-- url     : https://prove2.me/submissions/aed362fe-5ab7-45eb-9bc6-89fd7722ca7b

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glRest_mem
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_mem
import Theorems.Thm_Formalism_GM_FockB_ops_apply_comm
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
theorem _root_.solution (LL : Letters N) (j j' : ℕ) (hjj : j ≤ j') (c d a b : Fin r)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glRest p LL j j' c d (glAct p LL j a b x) = glAct p LL j a b (glRest p LL j j' c d x) := FockB.ops_apply_comm (S := {v : Fin N × Fin r | j ≤ (v.1 : ℕ)}) (S' := {v : Fin N × Fin r | (v.1 : ℕ) < j})
  (Set.disjoint_left.mpr fun v h1 h2 => by
    simp only [Set.mem_setOf_eq] at h1 h2
    omega)
  (glRest_mem LL j j' hjj c d) (glAct_mem LL j a b) x
end Formalism.InvariantFactorPaths.L4
