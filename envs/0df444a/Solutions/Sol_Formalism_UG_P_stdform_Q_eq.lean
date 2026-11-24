-- Prove2me | solution 1 for Formalism.UG.P.stdform_Q_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:51:22.722247+00:00
-- url     : https://prove2.me/submissions/b6423c5f-b680-4b24-8752-edd792bb7659

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform
import Theorems.Thm_Formalism_UG_P_stdform_hform_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {n : Type} [Fintype n] [DecidableEq n] {F E : Type} [Field F] [Field E] [Algebra F E]
namespace Formalism.UG.P
theorem _root_.solution (σ : E →ₐ[F] E) (τ : E →+* ℂ)
    (hσ : τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) (J : Matrix n n E) (ι : F →+* ℝ)
    (hι : τ.comp (algebraMap F E) = (algebraMap ℝ ℂ).comp ι) (x : n → E) (a : F)
    (ha : algebraMap F E a = hform (σ : E →+* E) J x x) :
    stdformQ (J.map τ) (fun i => τ (x i)) = ι a := by
  show (∑ i, ∑ j, starRingEnd ℂ (τ (x i)) * (J.map τ) i j * τ (x j)).re = ι a
  rw [← stdform_hform_map σ τ hσ J x, ← ha]
  have h := RingHom.congr_fun hι a
  simp only [RingHom.comp_apply] at h
  rw [h]
  simp
end Formalism.UG.P
