-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ProductIntervalFrames.isInternal_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:08:04.27772+00:00
-- url     : https://prove2.me/submissions/45b55d5a-b03d-48db-8099-892cc2afaa1a

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ProductIntervalFrames
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ProductIntervalFrames
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
namespace Formalism.FourierDecayAlt.P.ProductIntervalFrames
theorem _root_.solution {ι κ W : Type*} [DecidableEq ι] [DecidableEq κ] [AddCommGroup W] [Module ℂ W]
    (Φ : ι → κ) (hΦ : Function.Bijective Φ) (S : κ → Submodule ℂ W) (h : DirectSum.IsInternal S) :
    DirectSum.IsInternal (fun i => S (Φ i)) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at h ⊢
  exact ⟨h.1.comp hΦ.1, by rw [hΦ.2.iSup_comp S]; exact h.2⟩
end Formalism.FourierDecayAlt.P.ProductIntervalFrames
