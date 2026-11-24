-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SettingConstruction.setting_exists_of_haar_normalisation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:59:46.466581+00:00
-- url     : https://prove2.me/submissions/a1af95a9-492f-46f4-addb-83a4e49aa171

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_sectionExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_base_vector_exists
import Theorems.Thm_Formalism_FourierDecayAlt_P_character_exists_alt
import Theorems.Thm_Formalism_FourierDecayAlt_P_setting_exists_of_parts

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P
namespace SettingConstruction
theorem _root_.solution (hG : HaarGExists) (hW : HaarWExists) (hN : HaarNExists) (hI : IntNorm) :
    RealPlaceDataExists ∧ RealPlaceDataNonempty := by
  exact setting_exists_of_parts hG hW hN SettingConstruction.sectionExists character_exists_alt hI base_vector_exists
end SettingConstruction
end Formalism.FourierDecayAlt.P
