-- Prove2me | solution 1 for Formalism.UG.P.satakeB_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:24:32.792955+00:00
-- url     : https://prove2.me/submissions/ae4ccd19-720c-485e-8e45-5df2dbd17fc1

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeRes
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Satake
import Theorems.Thm_Formalism_UG_P_satakeGL_mem_doset
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
theorem _root_.solution {j : ℕ} (i : SatakeIdx v hϖ (n := n) j) : satakeB v hϖ hu i ∈ satakeTset v ϖ j := by
  obtain ⟨a, ha, b, hb, e⟩ := satakeGL_mem_doset (Ov F v) (satake_unif_ne_zero v hu) i.1.1
    (fun p => satakeSec (Ov F v) ⟨ϖ, hϖ⟩ (i.2 p))
  rw [i.1.2] at e
  exact ⟨a, ha, b, hb, e⟩
end Formalism.UG.P
