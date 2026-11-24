-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_int_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:50:07.527366+00:00
-- url     : https://prove2.me/submissions/77b7fd25-8665-4627-a159-9ef7c4358424

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaB
import Theorems.Thm_Formalism_UG_P_fIwasawa_int_mul

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
    (hM : fIwasawaInt M) : fIwasawaInt (fIwasawaInv σ M) := by
  have hJ : fIwasawaInt (antiJ L n) := by
    intro i j
    simp only [antiJ]
    split_ifs <;> simp
  have hcT : fIwasawaInt (cT σ M) := by
    intro i j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
    rw [hσv]
    exact hM j i
  unfold fIwasawaInv
  exact fIwasawa_int_mul _ _ (fIwasawa_int_mul _ _ hJ hcT) hJ
end Formalism.UG.P
