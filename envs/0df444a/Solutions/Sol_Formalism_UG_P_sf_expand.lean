-- Prove2me | solution 1 for Formalism.UG.P.sf_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:39:47.056261+00:00
-- url     : https://prove2.me/submissions/a09ab7db-39ba-4762-ac02-60810536e173

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
theorem _root_.solution (A : Matrix n n ℂ) (a b : ℂ) (u v : n → ℂ) :
    hform (starRingEnd ℂ) A (a • v + b • u) (a • v + b • u) =
      conj a * a * hform (starRingEnd ℂ) A v v + conj a * b * hform (starRingEnd ℂ) A v u +
      conj b * a * hform (starRingEnd ℂ) A u v + conj b * b * hform (starRingEnd ℂ) A u u := by
  unfold hform
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [map_add, map_mul]
  ring
end Formalism.UG.P
