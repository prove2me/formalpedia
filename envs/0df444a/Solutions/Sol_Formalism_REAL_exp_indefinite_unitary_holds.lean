-- Prove2me | solution 1 for Formalism.REAL.exp_indefinite_unitary_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:46.0998+00:00
-- url     : https://prove2.me/submissions/28312b89-7246-4f42-92f2-03b4d4055121

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Theorems.Thm_Formalism_REAL_f1alg_exp_inUJ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : ExpUJ := by
  intro n ε X hX t
  apply f1alg_exp_inUJ
  unfold inG at hX ⊢
  have hs : ((t : ℂ) • X)ᴴ = (t : ℂ) • Xᴴ := by
    rw [conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
  rw [hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]
end Formalism.REAL
