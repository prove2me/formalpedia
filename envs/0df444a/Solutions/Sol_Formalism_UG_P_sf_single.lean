-- Prove2me | solution 1 for Formalism.UG.P.sf_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:05.987547+00:00
-- url     : https://prove2.me/submissions/145fb497-32bb-482d-91c6-8f86bb88caf2

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
theorem _root_.solution {A : Type} [CommRing A] (σ : A →+* A) (J : Matrix n n A) (i : n) (y : n → A) :
    hform σ J (Pi.single i 1) y = (J *ᵥ y) i := by
  unfold hform
  rw [Finset.sum_eq_single i]
  · simp [Matrix.mulVec, dotProduct]
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_univ i) h
end Formalism.UG.P
