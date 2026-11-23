-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_col_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:10.01424+00:00
-- url     : https://prove2.me/submissions/a6ef2078-c538-4830-a68c-9ac86934e26a

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaC
import Theorems.Thm_Formalism_UG_P_fIwasawa_rows

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
theorem _root_.solution (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) (r : ℕ)
    (hT : fIwasawaTri r M) (ρ : Fin n) (hρr : ρ.val = r) (hρ : ρ < Fin.rev ρ) :
    ∀ i, Fin.rev ρ < i → M i ρ = 0 := by
  intro i hi
  have hi' := i.isLt
  have hρ' := ρ.isLt
  have hs : (Fin.rev i).val < r := by
    rw [Fin.val_rev, ← hρr]
    rw [Fin.lt_def, Fin.val_rev] at hi
    omega
  have h := (fIwasawa_rows σ M hM r hT (Fin.rev i) hs).2 ρ (by rw [Fin.rev_rev]; exact lt_trans hρ hi)
  rwa [Fin.rev_rev] at h
end Formalism.UG.P
