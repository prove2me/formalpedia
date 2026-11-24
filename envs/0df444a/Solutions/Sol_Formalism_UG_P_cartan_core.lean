-- Prove2me | solution 1 for Formalism.UG.P.cartan_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:50:11.631694+00:00
-- url     : https://prove2.me/submissions/b5088191-d85b-4536-9f42-1d3052fc1d23

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Theorems.Thm_Formalism_UG_P_cartan_entries_of_mem
import Theorems.Thm_Formalism_UG_P_cartan_val_det
import Theorems.Thm_Formalism_UG_P_cartan_pigeon

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] (O : Subring L) {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
namespace Formalism.UG.P
theorem _root_.solution (val : Valuation L Γ) (hO : ∀ x, x ∈ O ↔ val x ≤ 1) (ϖ : L)
    (hϖ0 : ϖ ≠ 0) (hϖ : val ϖ < 1) {m : ℕ} (a b : Fin m → ℤ) (ha : Antitone a)
    (hb : Antitone b) (k : GL (Fin m) L) (hk : k ∈ GLint (Fin m) O)
    (k' : Matrix (Fin m) (Fin m) L) (hk' : ∀ i j, k' i j ∈ O)
    (h : Matrix.diagonal (fun i => ϖ ^ a i) * (k : Matrix (Fin m) (Fin m) L) =
      k' * Matrix.diagonal (fun i => ϖ ^ b i)) (i : Fin m) (hi : a i < b i) : False := by
  have hvϖ : val ϖ ≠ 0 := (Valuation.ne_zero_iff val).mpr hϖ0
  have hent : ∀ p q, ϖ ^ a p * (k : Matrix (Fin m) (Fin m) L) p q = k' p q * ϖ ^ b q := by
    intro p q
    have e := congrFun (congrFun h p) q
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at e
    exact e
  have hsmall : ∀ p q, i ≤ p → q ≤ i → val ((k : Matrix (Fin m) (Fin m) L) p q) < 1 := by
    intro p q hp hq
    have hkpq : (k : Matrix (Fin m) (Fin m) L) p q = k' p q * ϖ ^ (b q - a p) := by
      have h0 := zpow_ne_zero (a p) hϖ0
      rw [zpow_sub₀ hϖ0, ← mul_div_assoc, ← hent p q]
      field_simp
    have hap := ha hp
    have hbq := hb hq
    obtain ⟨N, hN⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ b q - a p - 1 by omega)
    have hN' : b q - a p = (N : ℤ) + 1 := by omega
    have h1 : val (k' p q) ≤ 1 := (hO _).mp (hk' p q)
    have h2 : val ϖ ^ N ≤ 1 := pow_le_one' hϖ.le N
    rw [hkpq, map_mul, map_zpow₀, hN', zpow_add₀ hvϖ, zpow_natCast, zpow_one]
    calc val (k' p q) * (val ϖ ^ N * val ϖ) ≤ 1 * (1 * val ϖ) :=
          mul_le_mul' h1 (mul_le_mul' h2 le_rfl)
      _ = val ϖ := by rw [one_mul, one_mul]
      _ < 1 := hϖ
  have hle : ∀ p q, val ((k : Matrix (Fin m) (Fin m) L) p q) ≤ 1 :=
    fun p q => (hO _).mp (cartan_entries_of_mem O k hk p q)
  have hdet : val (k : Matrix (Fin m) (Fin m) L).det < 1 := by
    rw [Matrix.det_apply]
    refine Valuation.map_sum_lt val one_ne_zero (fun σ _ => ?_)
    obtain ⟨j, hj, hσj⟩ := cartan_pigeon σ i
    have hprod : val (∏ x, (k : Matrix (Fin m) (Fin m) L) (σ x) x) < 1 := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), map_mul, map_prod]
      calc val ((k : Matrix (Fin m) (Fin m) L) (σ j) j) *
            ∏ x ∈ Finset.univ.erase j, val ((k : Matrix (Fin m) (Fin m) L) (σ x) x)
          ≤ val ((k : Matrix (Fin m) (Fin m) L) (σ j) j) * 1 :=
            mul_le_mul' le_rfl (Finset.prod_le_one' (fun x _ => hle _ _))
        _ < 1 := by rw [mul_one]; exact hsmall _ _ hσj hj
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs]
    · rw [one_smul]
      exact hprod
    · rw [Units.neg_smul, one_smul, Valuation.map_neg]
      exact hprod
  exact absurd (cartan_val_det O val hO k hk) (ne_of_lt hdet)
end Formalism.UG.P
