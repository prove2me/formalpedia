-- Prove2me | solution 1 for Formalism.UG.P.levelv_phi_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:51:25.219509+00:00
-- url     : https://prove2.me/submissions/43c00381-8860-4320-ae3c-fbcea456adf9

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelv
import Theorems.Thm_Formalism_UG_P_levelv_range_le_S
import Theorems.Thm_Formalism_UG_P_levelv_mem_lat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
open IsDedekindDomain NumberField
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (α : n → Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletionIntegers F) :
    levelvPhi F E v n α ∈ stdLat (n := n) ↥(lvS F E v) := by
  rw [levelv_mem_lat]
  intro j
  exact levelv_range_le_S v (α j)
end Formalism.UG.P
