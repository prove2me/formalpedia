-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CommonEigenvectors.hop_move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:52:21.284795+00:00
-- url     : https://prove2.me/submissions/f4196497-9f07-41bd-ad07-abf59310c5d8

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommonEigenvectors
import Theorems.Thm_Formalism_FourierDecayAlt_P_CommonEigenvectors_diag_move
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CommonEigenvectors
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.CommonEigenvectors
theorem _root_.solution {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (a b : Fin n) (x : V) :
    hop E (E a b x) = E a b (hop E x) + (((b : ℕ) : ℂ) - ((a : ℕ) : ℂ)) • E a b x := by
  unfold hop
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, diag_move hE, smul_add, smul_sub,
    smul_ite, smul_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rw [← sub_smul]
  congr 2
  ring
end Formalism.FourierDecayAlt.P.CommonEigenvectors
