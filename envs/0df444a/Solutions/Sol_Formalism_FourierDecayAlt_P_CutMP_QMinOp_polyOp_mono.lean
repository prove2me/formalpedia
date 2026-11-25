-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.QMinOp.polyOp_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:25:12.871203+00:00
-- url     : https://prove2.me/submissions/c915e619-e37f-4f2a-a87a-d199eb9a3bec

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatOpA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatQMinOp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.QMinOp
open Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.CutMP.QMinOp
theorem _root_.solution {o o' κ κ' : ℕ} {Θ : B.DiffOp k r Wp Wq} (h : PolyOp o κ Θ) (ho : o ≤ o') (hκ : κ ≤ κ') :
    PolyOp o' κ' Θ := by
  unfold PolyOp at *
  intro Tm hTm
  obtain ⟨h1, P, hP, h2, h3⟩ := h Tm hTm
  obtain ⟨q, hq, hq'⟩ := hP
  exact ⟨h1.trans ho, P, ⟨q, hq.trans hκ, hq'⟩, h2, h3⟩
end Formalism.FourierDecayAlt.P.CutMP.QMinOp
