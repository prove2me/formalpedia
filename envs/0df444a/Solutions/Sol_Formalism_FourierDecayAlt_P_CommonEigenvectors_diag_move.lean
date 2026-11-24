-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CommonEigenvectors.diag_move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:14:21.347995+00:00
-- url     : https://prove2.me/submissions/c2b92b6d-782d-43d8-b046-d3609d310026

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommonEigenvectors
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
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
theorem _root_.solution {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (c a b : Fin n) (x : V) :
    E c c (E a b x) = E a b (E c c x) + ((if c = a then E a b x else 0) - (if b = c then E a b x else 0)) := by
  have h : E c c (E a b x) - E a b (E c c x) = ((if c = a then E c b else 0) - (if b = c then E a c else 0)) x :=
    congrArg (fun T => T x) (hE c c a b)
  rw [sub_eq_iff_eq_add'] at h
  rw [h, LinearMap.sub_apply]
  congr 1
  split_ifs <;> subst_vars <;> simp
end Formalism.FourierDecayAlt.P.CommonEigenvectors
