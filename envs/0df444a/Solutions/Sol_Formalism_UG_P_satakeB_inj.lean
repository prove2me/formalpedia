-- Prove2me | solution 1 for Formalism.UG.P.satakeB_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:24:29.619003+00:00
-- url     : https://prove2.me/submissions/5083fe8b-2699-433b-97ec-0c92bd90bb1a

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeRes
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Satake
import Theorems.Thm_Formalism_UG_P_satakeRep_inj
import Theorems.Thm_Formalism_UG_P_satake_unif_inv_not_mem
import Theorems.Thm_Formalism_UG_P_satake_unif_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
  {ϖ : v.adicCompletion F} (hϖ : ϖ ∈ Ov F v) (hu : IsUnifV F v ϖ)
namespace Formalism.UG.P
theorem _root_.solution {j : ℕ} :
    Function.Injective (fun i : SatakeIdx v hϖ (n := n) j =>
      ((satakeB v hϖ hu i : GL (Fin n) (v.adicCompletion F)) :
        GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v))) := by
  intro i i' h
  have h' := QuotientGroup.eq.1 h
  exact satakeRep_inj (Ov F v) ⟨ϖ, hϖ⟩ (satake_unif_ne_zero v hu) (satake_unif_inv_not_mem v hu) j i i' h'
end Formalism.UG.P
