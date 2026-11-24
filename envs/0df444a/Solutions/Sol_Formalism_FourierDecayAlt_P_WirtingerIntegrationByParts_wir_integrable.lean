-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.wir_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:05.706633+00:00
-- url     : https://prove2.me/submissions/d7af5458-0d59-41ec-8884-1cdb4a7a6890

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_contDiff_smul_of_tsupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution {d : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {φ : (Fin d → ℂ) → ℂ} {a : (Fin d → ℂ) → V} {Ω : Set (Fin d → ℂ)} (hΩ : IsOpen Ω) (hφ : ContinuousOn φ Ω)
    (ha : Continuous a) (hc : HasCompactSupport a) (hsupp : tsupport a ⊆ Ω) :
    Integrable (fun x => φ x • a x) (volume : Measure (Fin d → ℂ)) := by
  have h1 : Continuous (fun x => φ x • a x) :=
    contDiff_zero.mp (contDiff_smul_of_tsupport hΩ (contDiffOn_zero.mpr hφ) (contDiff_zero.mpr ha) hsupp)
  exact h1.integrable_of_hasCompactSupport (hc.smul_left (f := φ))
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
