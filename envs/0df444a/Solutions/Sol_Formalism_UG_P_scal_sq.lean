-- Prove2me | solution 1 for Formalism.UG.P.scal_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:39:45.873801+00:00
-- url     : https://prove2.me/submissions/a7848af6-0be8-48d4-a091-c056f81a6fc3

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.P
open Matrix
namespace Formalism.UG.P
theorem _root_.solution {n : Type} (ev : n → ℝ) (i : n) :
    scal ev i * (ev i : ℂ) * scal ev i = ((ev i / |ev i| : ℝ) : ℂ) := by
  have key : (Real.sqrt |ev i|)⁻¹ * ev i * (Real.sqrt |ev i|)⁻¹ = ev i / |ev i| := by
    set t := Real.sqrt |ev i| with ht
    have hs : t * t = |ev i| := Real.mul_self_sqrt (abs_nonneg _)
    rw [div_eq_mul_inv, ← hs]
    ring
  simp only [scal]
  rw [← key]
  push_cast
  ring
end Formalism.UG.P
