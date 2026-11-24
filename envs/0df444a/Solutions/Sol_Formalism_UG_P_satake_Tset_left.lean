-- Prove2me | solution 1 for Formalism.UG.P.satake_Tset_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:39:43.69156+00:00
-- url     : https://prove2.me/submissions/c6d13efb-5b86-4b76-a8bd-02ddd2bd95e1

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeRes
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Satake

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
namespace Formalism.UG.P
theorem _root_.solution {ϖ : v.adicCompletion F} {j : ℕ} {g k : GL (Fin n) (v.adicCompletion F)}
    (hg : g ∈ satakeTset v ϖ j) (hk : k ∈ GLint (Fin n) (Ov F v)) : k * g ∈ satakeTset v ϖ j := by
  obtain ⟨a, ha, b, hb, e⟩ := hg
  exact ⟨k * a, (GLint (Fin n) (Ov F v)).mul_mem hk ha, b, hb, by
    rw [Units.val_mul, e, Units.val_mul]; simp only [Matrix.mul_assoc]⟩
end Formalism.UG.P
