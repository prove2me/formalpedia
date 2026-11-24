-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LLcv.det_gramPl_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:45:36.018637+00:00
-- url     : https://prove2.me/submissions/8230f56b-859a-4523-9142-eaa7372cf379

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_gramPl_baseChange

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
    (v : InfinitePlace K) {j : ℕ} (e : Fin j → V) (g : Matrix (Fin j) (Fin j) K)
    (him : (gramPl b X v e).det.im = 0) :
    (gramPl b X v (fun a => ∑ c, g c a • e c)).det.re =
      v g.det ^ 2 * (gramPl b X v e).det.re := by
  have hdet : (g.map v.embedding).det = v.embedding g.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have hw : (gramPl b X v e).det = (((gramPl b X v e).det.re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simp [him])
  rw [gramPl_baseChange, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hdet, hw]
  have e1 : star (v.embedding g.det) * (((gramPl b X v e).det.re : ℝ) : ℂ) * v.embedding g.det =
      ((Complex.normSq (v.embedding g.det) * (gramPl b X v e).det.re : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self, Complex.star_def]
    ring
  rw [e1, Complex.ofReal_re, Complex.normSq_eq_norm_sq, InfinitePlace.norm_embedding_eq,
    Complex.ofReal_re]
end Formalism.LFunctionChainParameters.LLcv
