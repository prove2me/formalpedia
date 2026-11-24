-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_wd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:05:26.442828+00:00
-- url     : https://prove2.me/submissions/ae90bccd-5b13-46f6-914a-cb1a32110541

import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawa
import Theorems.Thm_Formalism_UG_P_fIwasawa_chi_mul
import Theorems.Thm_Formalism_UG_P_fIwasawa_chi_int
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.UG Matrix
namespace Formalism.UG.P
section FIwasawaFinal
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable (σ : L →+* L) {n m : ℕ} (q : ℕ) (α : Fin m → ℂ)
private lemma GL_inv_blockTriangular (g : GL (Fin n) L)
    (hg : (g : Matrix (Fin n) (Fin n) L).BlockTriangular id) :
    ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id := by
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hg
end FIwasawaFinal
end Formalism.UG.P
end

set_option autoImplicit false
open Formalism.UG Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable (σ : L →+* L) {n m : ℕ} (q : ℕ) (α : Fin m → ℂ)
namespace Formalism.UG.P
theorem _root_.solution (hα : ∀ i, α i ≠ 0) (hq : (q : ℂ) ≠ 0) (b b' k k' : GU σ n)
    (hb : ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id)
    (hb' : ((b' : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id)
    (hk : k ∈ KU σ n) (hk' : k' ∈ KU σ n) (h : b * k = b' * k') :
    chiDeltaU q α b = chiDeltaU q α b' := by
  have hc_eq : b = b' * (k' * k⁻¹) := by
    calc b = b * k * k⁻¹ := by group
      _ = b' * k' * k⁻¹ := by rw [h]
      _ = b' * (k' * k⁻¹) := by group
  have hkk : k' * k⁻¹ ∈ KU σ n := (KU σ n).mul_mem hk' ((KU σ n).inv_mem hk)
  have hc_eq2 : k' * k⁻¹ = b'⁻¹ * b := by rw [hc_eq]; group
  have htri : (((k' * k⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id := by
    rw [hc_eq2]
    exact Matrix.BlockTriangular.mul (GL_inv_blockTriangular (b' : GL (Fin n) L) hb') hb
  rw [hc_eq, fIwasawa_chi_mul σ q α hα hq b' (k' * k⁻¹) hb' htri,
    fIwasawa_chi_int σ q α (k' * k⁻¹) htri hkk, mul_one]
end Formalism.UG.P
