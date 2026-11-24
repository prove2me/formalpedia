-- Prove2me | solution 1 for Formalism.UG.P.afsplit_mulVec_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:37:08.321625+00:00
-- url     : https://prove2.me/submissions/fd675691-4f64-46c0-8acf-895101662fd6

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (S : Subring A) (M : Matrix n n A) (hM : ∀ i j, M i j ∈ S) (x : n → A)
    (hx : ∀ i, x i ∈ S) (i : n) : (M *ᵥ x) i ∈ S := by
  show ∑ j, M i j * x j ∈ S
  exact sum_mem fun j _ => mul_mem (hM i j) (hx j)
end Formalism.UG.P
