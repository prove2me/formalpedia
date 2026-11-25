-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_iwasawa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:11:15.577046+00:00
-- url     : https://prove2.me/submissions/a5692359-261b-4a8d-9c2a-0cda6324062d

import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawa
import Theorems.Thm_Formalism_UG_P_fIwasawa_mem_un
import Theorems.Thm_Formalism_UG_P_fIwasawa_mk_mem_K
import Theorems.Thm_Formalism_UG_P_fIwasawa_mk_val
import Theorems.Thm_Formalism_UG_P_fIwasawa_upper
import Theorems.Thm_Formalism_UG_P_spherical_upper_iff
import Theorems.Thm_Formalism_UG_P_spherical_upper_inv


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
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable (σ : L →+* L) {n m : ℕ} (q : ℕ) (α : Fin m → ℂ)
namespace Formalism.UG.P
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (hσv : ∀ x, Valued.v (σ x) = Valued.v x)
    (g : GU σ n) : ∃ b k : GU σ n, IsBorelU b ∧ k ∈ KU σ n ∧ g = b * k := by
  obtain ⟨k, hk, hup⟩ := fIwasawa_upper σ hσ hσv _ (fIwasawa_mem_un σ g⁻¹)
  have hkG : fIwasawaMk σ k hk.1 ∈ KU σ n := fIwasawa_mk_mem_K σ hσv k hk.1 hk.2
  refine ⟨(fIwasawaMk σ k hk.1 * g⁻¹)⁻¹, fIwasawaMk σ k hk.1, ?_, hkG, by group⟩
  have h1 : (((fIwasawaMk σ k hk.1 * g⁻¹ : GU σ n) : GL (Fin n) L) :
      Matrix (Fin n) (Fin n) L).BlockTriangular id := by
    rw [Subgroup.coe_mul, Units.val_mul, fIwasawa_mk_val]; exact hup
  have h2 := spherical_upper_inv _ h1
  rw [← Subgroup.coe_inv] at h2
  exact (spherical_upper_iff _).2 h2
end Formalism.UG.P
