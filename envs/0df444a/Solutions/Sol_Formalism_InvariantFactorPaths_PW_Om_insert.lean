-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.Om_insert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:57:03.282957+00:00
-- url     : https://prove2.me/submissions/bc67f727-d4f8-46f2-8ae5-750503abe088

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_lop_pow_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_lop_commute
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Om_eq_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_GlRel_commF
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_GlRel_commE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset
variable {K W ι : Type} [Field K] [AddCommGroup W] [Module K W] [DecidableEq ι]
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution {E : ι → ι → Module.End K W} (h : GlRel E) {S : Finset ι} {z i : ι} (hz : z ∉ insert i S)
    (hi : i ∉ S) (q : ℕ) :
    Om E (insert i S) z q =
      ∑ k ∈ range (q + 1), (q.choose k : K) • ((E z i) ^ k * Om E S z (q - k) * (E i z) ^ k) := by
  have hzi : i ≠ z := fun e => hz (e ▸ Finset.mem_insert_self _ _)
  have hcomm : Commute (lop (E z i) (E i z)) (∑ j ∈ S, lop (E z j) (E j z)) := by
    refine Commute.sum_right _ _ _ fun j hj => ?_
    have hjz : j ≠ z := fun e => hz (e ▸ Finset.mem_insert_of_mem hj)
    exact lop_commute (h.commF hzi hjz) (h.commE hzi hjz)
  rw [Om_eq_pow, Finset.sum_insert hi, hcomm.add_pow, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, map_nsmul,
    ← Om_eq_pow, lop_pow_apply, ← Nat.cast_smul_eq_nsmul K]
end Formalism.InvariantFactorPaths.PW
