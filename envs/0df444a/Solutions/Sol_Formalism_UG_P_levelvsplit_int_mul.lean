-- Prove2me | solution 1 for Formalism.UG.P.levelvsplit_int_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:39:00.984439+00:00
-- url     : https://prove2.me/submissions/875598b8-81d4-4327-8ced-4b0626577628

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelvsplit

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
variable {B K : Type} [CommRing B] [CommRing K] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution {S : Type} [SetLike S K] [SubringClass S K] (O : S)
    (M N : Matrix n n K) (hM : ∀ i j, M i j ∈ O) (hN : ∀ i j, N i j ∈ O) :
    ∀ i j, (M * N) i j ∈ O := by
  intro i j
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hM i k) (hN k j)
end Formalism.UG.P
