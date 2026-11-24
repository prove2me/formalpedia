-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_mk_mem_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:05:29.964353+00:00
-- url     : https://prove2.me/submissions/32a23d7d-19f1-45fd-bf52-0744076edba7

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaB
import Theorems.Thm_Formalism_UG_P_fIwasawa_int_inv
import Theorems.Thm_Formalism_UG_P_fIwasawa_mk_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (M : Matrix (Fin n) (Fin n) L)
    (hM : fIwasawaUn σ M) (hI : fIwasawaInt M) : fIwasawaMk σ M hM ∈ KU σ n := by
  have hinvI := fIwasawa_int_inv σ hσv M hI
  rw [KU, Subgroup.mem_subgroupOf]
  refine Subgroup.mem_inf.2 ⟨(fIwasawaMk σ M hM).2, ?_⟩
  let A : Matrix (Fin n) (Fin n) (intL L) := Matrix.of fun i j => ⟨M i j, hI i j⟩
  let B : Matrix (Fin n) (Fin n) (intL L) := Matrix.of fun i j => ⟨fIwasawaInv σ M i j, hinvI i j⟩
  have hinj : Function.Injective
      (RingHom.mapMatrix (intL L).subtype : Matrix (Fin n) (Fin n) (intL L) →+* Matrix (Fin n) (Fin n) L) :=
    fun X Y h => by
      ext i j
      exact congrFun (congrFun h i) j
  have hA : RingHom.mapMatrix (intL L).subtype A = M := by ext i j; rfl
  have hB : RingHom.mapMatrix (intL L).subtype B = fIwasawaInv σ M := by ext i j; rfl
  have hAB : A * B = 1 := hinj (by rw [map_mul, hA, hB, map_one, fIwasawa_mul_inv σ M hM])
  have hBA : B * A = 1 := hinj (by rw [map_mul, hA, hB, map_one, fIwasawa_inv_mul σ M hM])
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  apply Units.ext
  show RingHom.mapMatrix (intL L).subtype A = _
  rw [hA]
  exact (fIwasawa_mk_val σ M hM).symm
end Formalism.UG.P
