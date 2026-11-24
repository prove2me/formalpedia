-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.Pstep_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:16:05.866934+00:00
-- url     : https://prove2.me/submissions/8e1f52a5-3811-4d7a-88ea-2c7456ef4a9d

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Om_int

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
variable {p : ℕ} [Fact p.Prime]
variable {W ι : Type} [AddCommGroup W] [Module ℚ_[p] W] [DecidableEq ι]
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution {E : ι → ι → Module.End ℚ_[p] W} (hE : GlRel E) {M : AddSubgroup W} (hZ : ZpClosed p M)
    (hD : DivStable E M) {z : ι} {S : Finset ι} (hz : z ∉ S) (l : ℕ) {u : W} (hu : u ∈ M) :
    ((p : ℚ_[p]) ^ (S.card * Nat.log p (l + S.card))) • Pstep E S z l u ∈ M := by
  unfold Pstep
  rw [LinearMap.sum_apply, Finset.smul_sum]
  refine AddSubgroup.sum_mem _ fun q hq => ?_
  have hql : q ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
  have h := Om_int hE hZ hD z (l + S.card) S hz S.card q (by omega) u hu
  have h2 := hZ ((-1 : ℚ_[p]) ^ q) (by simp) _ h
  convert h2 using 1
  simp only [LinearMap.smul_apply, smul_smul]
  congr 1
  ring
end Formalism.InvariantFactorPaths.PW
