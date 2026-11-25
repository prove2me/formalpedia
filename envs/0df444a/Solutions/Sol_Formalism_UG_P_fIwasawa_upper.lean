-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:54:38.456453+00:00
-- url     : https://prove2.me/submissions/724ff284-10b5-4cd8-a781-b4f3f6c93dcf

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaD
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaE
import Theorems.Thm_Formalism_UG_P_fIwasawa_reduce
import Theorems.Thm_Formalism_UG_P_fIwasawa_rows
import Theorems.Thm_Formalism_UG_P_fIwasawa_un_mul


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
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (hσv : ∀ x, Valued.v (σ x) = Valued.v x)
    (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) :
    ∃ k, fIwasawaKm σ k ∧ (k * M).BlockTriangular id := by
  obtain ⟨k, hk, hT⟩ := fIwasawa_reduce (σ := σ) hσ hσv M hM (n / 2) (by omega)
  refine ⟨k, hk, ?_⟩
  have hkM : fIwasawaUn σ (k * M) := fIwasawa_un_mul (σ := σ) k M (And.left hk) hM
  intro i j hij
  have hij' : j < i := hij
  by_cases hj : j.val < n / 2
  · exact hT i j hj hij'
  · have hlt := Fin.lt_iff_val_lt_val.mp hij'
    have hi := i.isLt
    have hs : (Fin.rev i).val < n / 2 := by
      rw [Fin.val_rev]
      omega
    have h0 := (fIwasawa_rows (σ := σ) (k * M) hkM (n / 2) hT (Fin.rev i) hs).2 j
      (by rw [Fin.rev_rev]; exact hij')
    rwa [Fin.rev_rev] at h0
end Formalism.UG.P
