-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LLcv.gramPl_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:29:29.473288+00:00
-- url     : https://prove2.me/submissions/ce3d04db-c026-4e6e-a9e0-d6a3c879b58e

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_fcoord_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LLcv
open Formalism.HN Formalism.HermitianLatticesTheory Formalism.LFunctionChainParameters.slopeLatticeData
open scoped Matrix
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.LFunctionChainParameters.LLcv
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) {j : ℕ} (e : Fin j → V) (g : Matrix (Fin j) (Fin j) K) :
    gramPl b X v (fun a => ∑ c, g c a • e c) =
      (g.map v.embedding)ᴴ * gramPl b X v e * g.map v.embedding := by
  let Mv : Matrix ι (Fin j) ℂ := Matrix.of fun i a => fcoord b X v (e a) i
  have hG : gramPl b X v e = Mvᴴ * Mv := by
    ext a c
    simp [gramPl, majAt, Mv, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hG' : gramPl b X v (fun a => ∑ c, g c a • e c) =
      (Mv * g.map v.embedding)ᴴ * (Mv * g.map v.embedding) := by
    ext a c
    simp only [gramPl, majAt, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      fcoord_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Mv, Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    · congr 1
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    · exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hG', hG, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
end Formalism.LFunctionChainParameters.LLcv
