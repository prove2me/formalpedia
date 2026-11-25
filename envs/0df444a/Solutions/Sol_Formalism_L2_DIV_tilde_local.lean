-- Prove2me | solution 1 for Formalism.L2.DIV.tilde_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:14:22.418148+00:00
-- url     : https://prove2.me/submissions/38c34f0f-9bbc-4ce3-9821-fe43500d5c05

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_norm_quotient_ker_le
import Theorems.Thm_Formalism_L2_DIV_b_resChar_spec
import Theorems.Thm_Formalism_L2_DIV_tilde_norm_quotient


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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
namespace Formalism.L2.DIV
theorem _root_.solution : TildeLocal := by
  intro F E _ _ _ _ _ L _ σ ξ hσ hξ hF P v hPv u a b hb hu huP huP'
  rw [tilde_norm_quotient σ ξ (norm_quotient_ker_le σ ξ hσ hF)]
  exact b_resChar_spec ξ hξ P v hPv u a b hb hu huP huP'
end Formalism.L2.DIV
