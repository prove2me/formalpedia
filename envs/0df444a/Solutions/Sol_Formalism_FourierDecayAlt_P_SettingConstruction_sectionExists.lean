-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SettingConstruction.sectionExists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:38:41.766299+00:00
-- url     : https://prove2.me/submissions/e7cab03e-cb43-4fc5-a9f2-c3dc613d830a

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_section_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SettingConstruction
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.SettingConstruction
theorem _root_.solution : Formalism.QuantumDeterminants.SectionExists := by
  intro k r z z' hk hz hz' hT hT'
  obtain ⟨μ, h1, h2⟩ := section_core k hk (wbPart k r z) (wbPart k r z') (Tz k r z) (Tz k r z') hT hT'
    (herm_self k r z hz) (herm_self k r z' hz')
  exact ⟨μ, h1, h2⟩
end Formalism.FourierDecayAlt.P.SettingConstruction
