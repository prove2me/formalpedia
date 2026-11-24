-- Prove2me | solution 1 for Formalism.UG.P.sf_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:39:46.413792+00:00
-- url     : https://prove2.me/submissions/cfe9213f-a3aa-4b6b-bd47-016c5e4785d0

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
theorem _root_.solution (A : Matrix n n ℂ) (hA : ∀ i j, conj (A j i) = A i j) (u v : n → ℂ) :
    conj (hform (starRingEnd ℂ) A u v) = hform (starRingEnd ℂ) A v u := by
  unfold hform
  simp only [map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, Complex.conj_conj, hA]
  ring
end Formalism.UG.P
