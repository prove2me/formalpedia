-- Prove2me | solution 1 for Formalism.UG.P.fSatake_cell_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:07:58.159438+00:00
-- url     : https://prove2.me/submissions/07f8588a-6a9d-4768-bb80-39c3590bcee5

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeC
import Theorems.Thm_Formalism_UG_P_fSatake_ne_zero_of_borel
import Theorems.Thm_Formalism_UG_P_fSatake_tMat_apply_lt
import Theorems.Thm_Formalism_UG_P_fSatake_borel_tMat
import Theorems.Thm_Formalism_UG_P_fSatake_tMat_exists
import Theorems.Thm_Formalism_UG_P_fSatake_K_int
import Theorems.Thm_Formalism_UG_P_fSatake_borel_diag_mul
import Theorems.Thm_Formalism_UG_P_fSatake_borel_inv
import Theorems.Thm_Formalism_UG_P_fSatake_borel_mul
import Theorems.Thm_Formalism_UG_P_fSatake_ord_mul
import Theorems.Thm_Formalism_UG_P_fSatake_ord_nonneg
import Theorems.Thm_Formalism_UG_P_fSatake_ord_of_v
import Theorems.Thm_Formalism_UG_P_fSatake_ord_one
import Theorems.Thm_Formalism_UG_P_fSatake_ord_zpow
import Theorems.Thm_Formalism_UG_P_fSatake_unit_diag


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
local notation "⟪" b "⟫" => (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
namespace Formalism.UG.P
theorem _root_.solution {ϖ : L} {q m : ℕ} (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n)
    {a a' : Fin m → ℤ} {u u' k k' : GU σ n} (hu : IsUnipU u) (hu' : IsUnipU u')
    (hk : k ∈ KU σ n) (hk' : k' ∈ KU σ n)
    (h : tMat ϖ n m a * ⟪u⟫ * ⟪k⟫ = tMat ϖ n m a' * ⟪u'⟫ * ⟪k'⟫) : a = a' := by
  have hϖ0 : ϖ ≠ 0 := by
    intro h; have := hU.2.2.2.1; rw [h, Valuation.map_zero] at this; exact absurd this WithZero.zero_ne_coe
  obtain ⟨t, ht⟩ := fSatake_tMat_exists hU hm a
  obtain ⟨t', ht'⟩ := fSatake_tMat_exists hU hm a'
  have htb := fSatake_borel_tMat ht
  have htb' := fSatake_borel_tMat ht'
  have hx : t * u * k = t' * u' * k' := by
    apply Subtype.ext; apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, ht, ht']
    exact h
  have hwk : (t' * u')⁻¹ * (t * u) = k' * k⁻¹ := by
    calc (t' * u')⁻¹ * (t * u) = (t' * u')⁻¹ * (t * u * k) * k⁻¹ := by group
      _ = (t' * u')⁻¹ * (t' * u' * k') * k⁻¹ := by rw [hx]
      _ = k' * k⁻¹ := by group
  have hwK : (t' * u')⁻¹ * (t * u) ∈ KU σ n := by rw [hwk]; exact mul_mem hk' (inv_mem hk)
  have hb1 := fSatake_borel_mul htb hu.1
  have hb2 := fSatake_borel_mul htb' hu'.1
  have hwb : IsBorelU ((t' * u')⁻¹ * (t * u)) := fSatake_borel_mul (fSatake_borel_inv hb2) hb1
  have htu : t * u = (t' * u') * ((t' * u')⁻¹ * (t * u)) := by group
  funext j
  have hj : (j : ℕ) < n := by omega
  have hdiag : ⟪t * u⟫ ⟨j, hj⟩ ⟨j, hj⟩ = ⟪(t' * u') * ((t' * u')⁻¹ * (t * u))⟫ ⟨j, hj⟩ ⟨j, hj⟩ :=
    congrArg (fun z : GU σ n => ⟪z⟫ ⟨j, hj⟩ ⟨j, hj⟩) htu
  rw [fSatake_borel_diag_mul hb2 hwb, fSatake_borel_diag_mul htb hu.1,
    fSatake_borel_diag_mul htb' hu'.1, hu.2, hu'.2, ht, ht', mul_one, mul_one,
    fSatake_tMat_apply_lt ϖ a j hj, fSatake_tMat_apply_lt ϖ a' j hj] at hdiag
  set w := (t' * u')⁻¹ * (t * u)
  have hw0 : ⟪w⟫ ⟨j, hj⟩ ⟨j, hj⟩ ≠ 0 := fSatake_ne_zero_of_borel hwb _
  have hwr0 := fSatake_ne_zero_of_borel hwb (⟨j, hj⟩ : Fin n).rev
  have hpair := congrArg ordL (fSatake_unit_diag hwb ⟨j, hj⟩)
  rw [fSatake_ord_mul ((map_ne_zero σ).2 hw0) hwr0, fSatake_ord_of_v (hU.2.1 _),
    fSatake_ord_one] at hpair
  have hn1 := fSatake_ord_nonneg hw0 (fSatake_K_int hwK _ _)
  have hn2 := fSatake_ord_nonneg hwr0 (fSatake_K_int hwK _ _)
  have h3 := congrArg ordL hdiag
  rw [fSatake_ord_mul (zpow_ne_zero _ hϖ0) hw0, fSatake_ord_zpow hU.2.2.2.1,
    fSatake_ord_zpow hU.2.2.2.1] at h3
  omega
end Formalism.UG.P
