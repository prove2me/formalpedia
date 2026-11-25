-- Prove2me | solution 1 for Formalism.L2.DIV.residue_character_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:08:37.006846+00:00
-- url     : https://prove2.me/submissions/a3813569-0e18-44b6-b884-0f1b5fbcb38a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_residue_character_exists
import Theorems.Thm_Formalism_L2_DIV_b_resChar_spec

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {L : Type} [Field L]
namespace Formalism.L2.DIV
theorem _root_.solution : ResCharMul := by
  intro F E _ _ _ _ _ L _ ξ η hξ hη P
  have hξη : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ (ξ * η).ker := fun v =>
    (kills Lˣ (wildAt E v)).mul_mem (hξ v) (hη v)
  apply (residue_character_exists F E L (ξ * η) hξη P).unique (b_resChar_spec _ hξη P)
  intro v hv u a b hb hu huP huP'
  rw [MonoidHom.mul_apply, MonoidHom.mul_apply, b_resChar_spec ξ hξ P v hv u a b hb hu huP huP',
    b_resChar_spec η hη P v hv u a b hb hu huP huP']
end Formalism.L2.DIV
