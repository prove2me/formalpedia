-- Prove2me | solution 1 for Formalism.UG.P.levelv_range_le_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:38:57.887482+00:00
-- url     : https://prove2.me/submissions/d4b483b9-824a-4afc-9abf-0363d41b638a

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelv
import Theorems.Thm_Formalism_UG_P_levelv_tmul_mem

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
  (v : HeightOneSpectrum (𝓞 F))
namespace Formalism.UG.P
theorem _root_.solution (a : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletionIntegers F) :
    levelvPsi F E v a ∈ lvS F E v := by
  simp only [levelvPsi, AddMonoidHom.mk'_apply]
  exact sum_mem fun i _ => levelv_tmul_mem v _ (RingHom.mem_range.mpr ⟨_, rfl⟩) _ (a i).2
end Formalism.UG.P
