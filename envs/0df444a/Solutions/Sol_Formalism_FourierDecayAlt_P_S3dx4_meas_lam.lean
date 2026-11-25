-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.meas_lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:02:52.749485+00:00
-- url     : https://prove2.me/submissions/fa9c7a67-fabe-4579-b7de-9e866b007389

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousSandwichedProduct
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasurableEnormComposition
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_meas_lam_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.S3dx4
theorem _root_.solution {e0 : Mx k r → ℂ} (he0 : Continuous e0) (γ : Mx k r)
    (μp μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) [SFinite μp] [SFinite μq] :
    Measurable (fun t : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => abelian₂ e0 γ μp μq t.1 t.2) := by
  unfold abelian₂
  have m4 := meas_lam_int he0 γ (α := ((Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) × (Formalism.QuantumDeterminants.Mt k r ×
      Formalism.QuantumDeterminants.Mt k r)) × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r))
    (measurable_fst.fst.fst) (measurable_fst.fst.snd) measurable_fst.snd measurable_snd
  have m3 := m4.lintegral_prod_right' (ν := μq)
  exact m3.lintegral_prod_right' (ν := μp)
end Formalism.FourierDecayAlt.P.S3dx4
