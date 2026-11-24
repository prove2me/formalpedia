-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_int_E
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:38:12.482355+00:00
-- url     : https://prove2.me/submissions/a7c8b60e-ed1e-4b68-981f-1eb320f26b24

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaB

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
theorem _root_.solution (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (e z : Fin n → L) (c : L)
    (he : ∀ i, Valued.v (e i) ≤ 1) (hz : ∀ i, Valued.v (z i) ≤ 1) (hc : Valued.v c ≤ 1) :
    fIwasawaInt (fIwasawaE σ e z c) := by
  intro i j
  simp only [fIwasawaE, Matrix.of_apply]
  have h1 : Valued.v (if i = j then (1 : L) else 0) ≤ 1 := by split_ifs <;> simp
  refine Valuation.map_add_le _ (Valuation.map_sub_le _ (Valuation.map_add_le _ h1 ?_) ?_) ?_
  · rw [map_mul, hσv]
    exact mul_le_one' (hz i) (he _)
  · rw [map_mul, hσv]
    exact mul_le_one' (he i) (hz _)
  · rw [map_mul, map_mul, hσv]
    exact mul_le_one' (mul_le_one' hc (he i)) (he _)
end Formalism.UG.P
