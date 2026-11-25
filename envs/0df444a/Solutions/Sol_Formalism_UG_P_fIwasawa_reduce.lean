-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_reduce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:39:39.962571+00:00
-- url     : https://prove2.me/submissions/3926d3d5-ea0c-4505-b105-087e99118b74

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaD
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaE
import Theorems.Thm_Formalism_UG_P_fIwasawa_tri_succ_of_max_pivot
import Theorems.Thm_Formalism_UG_P_fIwasawa_Km_mul
import Theorems.Thm_Formalism_UG_P_fIwasawa_Km_one
import Theorems.Thm_Formalism_UG_P_fIwasawa_exists_max_pivot
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
    ∀ r : ℕ, 2 * r ≤ n → ∃ k, fIwasawaKm σ k ∧ fIwasawaTri r (k * M) := by
  intro r
  induction r with
  | zero =>
    intro _
    refine ⟨1, fIwasawa_Km_one (σ := σ), ?_⟩
    intro i j hj _
    exact absurd hj (Nat.not_lt_zero _)
  | succ r ih =>
    intro hr
    obtain ⟨k, hk, hkT⟩ := ih (by omega)
    have hrn : r < n := by omega
    have hρ : (⟨r, hrn⟩ : Fin n) < Fin.rev ⟨r, hrn⟩ := by
      rw [Fin.lt_iff_val_lt_val, Fin.val_rev]
      show r < n - (r + 1)
      omega
    have hkM : fIwasawaUn σ (k * M) := fIwasawa_un_mul (σ := σ) k M (And.left hk) hM
    obtain ⟨k1, hk1, hT1, hp1, hmax1⟩ :=
      fIwasawa_exists_max_pivot (σ := σ) hσv (k * M) hkM r hkT ⟨r, hrn⟩ rfl hρ
    have hk1M : fIwasawaUn σ (k1 * (k * M)) :=
      fIwasawa_un_mul (σ := σ) k1 (k * M) (And.left hk1) hkM
    obtain ⟨k2, hk2, hT2⟩ :=
      fIwasawa_tri_succ_of_max_pivot (σ := σ) hσ hσv (k1 * (k * M)) hk1M r hT1 ⟨r, hrn⟩ rfl hρ hp1 hmax1
    refine ⟨k2 * (k1 * k), fIwasawa_Km_mul (σ := σ) hk2 (fIwasawa_Km_mul (σ := σ) hk1 hk), ?_⟩
    simpa only [Matrix.mul_assoc] using hT2
end Formalism.UG.P
