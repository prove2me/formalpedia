-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.modelExists_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:36:19.332853+00:00
-- url     : https://prove2.me/submissions/656cb0c7-d10f-4631-ae69-c9cb0f0881b7

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementW
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_WittTeichmullerRoot
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_WModel
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_abv_p
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_abv_value
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_abv_sig
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_ultra
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_complete
import Theorems.Thm_Formalism_FG_witt_char_zero
import Theorems.Thm_Formalism_FG_witt_teichmuller_root


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NNReal
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open WModel
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : ModelExists := by
  intro p _ hp2
  have hW : CharZero (WW p) := Formalism.FG.witt_char_zero p
  obtain ⟨ζ, hζ⟩ := Formalism.FG.witt_teichmuller_root p 2 (by norm_num)
  refine ⟨KK p, nf p, ?_, ?_, complete p, sig p, ⟨Fact.out, hp2, abv_p p, abv_value p, abv_sig p⟩,
    algebraMap (WW p) (KK p) ζ, hζ.map_of_injective (IsFractionRing.injective (WW p) (KK p))⟩
  · exact ultra p
  · exact charZero_of_injective_algebraMap (IsFractionRing.injective (WW p) (KK p))
end Formalism.InvariantFactorPaths.G7
