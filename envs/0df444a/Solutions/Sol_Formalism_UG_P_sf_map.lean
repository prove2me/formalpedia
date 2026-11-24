-- Prove2me | solution 1 for Formalism.UG.P.sf_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:39:48.340328+00:00
-- url     : https://prove2.me/submissions/ee5ef77a-8fd0-49e6-8ec0-ef1892e4bcee

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField ComplexConjugate
open Formalism Formalism.UG Formalism.UG.P
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution {E : Type} [CommRing E] (σ : E →+* E) (τ : E →+* ℂ)
    (hτ : τ.comp σ = (starRingEnd ℂ).comp τ) (J : Matrix n n E) (x y : n → E) :
    τ (hform σ J x y) = hform (starRingEnd ℂ) (J.map τ) (fun k => τ (x k)) (fun k => τ (y k)) := by
  unfold hform
  simp only [map_sum, map_mul, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 := RingHom.congr_fun hτ (x i)
  simp only [RingHom.comp_apply] at h1
  rw [h1]
end Formalism.UG.P
