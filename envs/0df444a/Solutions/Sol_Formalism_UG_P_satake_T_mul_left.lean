-- Prove2me | solution 1 for Formalism.UG.P.satake_T_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:53:02.5739+00:00
-- url     : https://prove2.me/submissions/9c0f66c8-0c2f-4c23-8275-12f0b16ce601

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeRes
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Satake
import Theorems.Thm_Formalism_UG_P_satake_Tset_left
import Theorems.Thm_Formalism_UG_P_satake_Tj_eq

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
theorem _root_.solution (j : ℕ) (z c : GL (Fin n) (v.adicCompletion F)) (hc : c ∈ GLint (Fin n) (Ov F v)) :
    Tj ℂ n (Ov F v) ϖ j (c * z) = Tj ℂ n (Ov F v) ϖ j z := by
  rw [satake_Tj_eq, satake_Tj_eq]
  by_cases h : z ∈ satakeTset v ϖ j
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (satake_Tset_left v h hc)]; rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem]
    intro h'
    apply h
    have := satake_Tset_left v h' ((GLint (Fin n) (Ov F v)).inv_mem hc)
    rwa [inv_mul_cancel_left] at this
end Formalism.UG.P
