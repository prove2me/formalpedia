-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_indepF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:58.460214+00:00
-- url     : https://prove2.me/submissions/34b3f9cd-6dbb-4e6f-9190-57bb7a4d4d7e

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbIndepField
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_indep_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {M : GLMod n} (CF : ColFam M) (F : Type) [Field F] (nu : Fin n → ℤ) :
    LinearIndependent F
      (fun j : {j : CF.J // CF.mu j = nu} => fun i => ((CF.ph j.1 i (canT (CF.mu j.1)) : ℤ) : F)) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  obtain ⟨p, hp⟩ := CharP.exists F
  rcases CharP.char_is_prime_or_zero F p with hpp | rfl
  · haveI := Fact.mk hpp
    letI := ZMod.algebra F p
    refine qb_indep_ext (k := ZMod p) _ (CF.indepP p hpp nu) a fun i => ?_
    have := congrFun ha i
    simpa [Algebra.smul_def, mul_comm] using this
  · haveI := CharP.charP_to_charZero F
    refine qb_indep_ext (k := ℚ) _ (CF.indepQ nu) a fun i => ?_
    have := congrFun ha i
    simpa [Algebra.smul_def, mul_comm] using this
end Formalism.InvariantFactorPaths.ColumnFamilies
