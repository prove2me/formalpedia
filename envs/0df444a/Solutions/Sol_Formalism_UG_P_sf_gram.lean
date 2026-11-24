-- Prove2me | solution 1 for Formalism.UG.P.sf_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:39:47.658153+00:00
-- url     : https://prove2.me/submissions/3ed82579-1a15-4c18-ae00-5ce047e5af87

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
theorem _root_.solution {A : Type} [CommRing A] (σ : A →+* A) (J M : Matrix n n A) (a b : n) :
    (cT σ M * J * M) a b = hform σ J (fun k => M k a) (fun k => M k b) := by
  unfold hform cT
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
end Formalism.UG.P
