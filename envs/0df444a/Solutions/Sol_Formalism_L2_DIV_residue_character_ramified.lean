-- Prove2me | solution 1 for Formalism.L2.DIV.residue_character_ramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:01:41.611544+00:00
-- url     : https://prove2.me/submissions/056ff4cd-1bcf-4688-92a9-a318149b02cd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_residue_character_exists
import Theorems.Thm_Formalism_L2_DIV_residue_character_conj
import Theorems.Thm_Formalism_L2_DIV_residue_character_ramified_of_quadratic
import Theorems.Thm_Formalism_L2_DIV_twist_exists_unit
import Theorems.Thm_Formalism_L2_DIV_twist_wild_trivial
import Theorems.Thm_Formalism_L2_DIV_twist_approximation
import Theorems.Thm_Formalism_L2_DIV_twist_comap
import Theorems.Thm_Formalism_L2_DIV_twist_off_support

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.DIV
namespace Formalism.L2.DIV
theorem _root_.solution : ResCharRam := fun F E _ _ _ _ _ L _ hdeg =>
  residue_character_ramified_of_quadratic twist_exists_unit twist_wild_trivial twist_approximation twist_comap twist_off_support residue_character_exists
    residue_character_conj F E hdeg L
end Formalism.L2.DIV
