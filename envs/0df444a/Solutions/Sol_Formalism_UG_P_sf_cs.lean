-- Prove2me | solution 1 for Formalism.UG.P.sf_cs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:54:10.057919+00:00
-- url     : https://prove2.me/submissions/e3e2de78-38b3-446e-a523-333437af941f

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin
import Theorems.Thm_Formalism_UG_P_sf_expand
import Theorems.Thm_Formalism_UG_P_sf_conj

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
theorem _root_.solution (A : Matrix n n ℂ) (hA : ∀ i j, conj (A j i) = A i j) (u v : n → ℂ) :
    hform (starRingEnd ℂ) A (hform (starRingEnd ℂ) A u u • v + (-hform (starRingEnd ℂ) A u v) • u)
      (hform (starRingEnd ℂ) A u u • v + (-hform (starRingEnd ℂ) A u v) • u) =
    hform (starRingEnd ℂ) A u u * (hform (starRingEnd ℂ) A u u * hform (starRingEnd ℂ) A v v
      - conj (hform (starRingEnd ℂ) A u v) * hform (starRingEnd ℂ) A u v) := by
  rw [sf_expand]
  have h1 : conj (hform (starRingEnd ℂ) A u u) = hform (starRingEnd ℂ) A u u := sf_conj A hA u u
  have h2 : hform (starRingEnd ℂ) A v u = conj (hform (starRingEnd ℂ) A u v) := (sf_conj A hA u v).symm
  rw [h2, map_neg, h1]
  ring
end Formalism.UG.P
