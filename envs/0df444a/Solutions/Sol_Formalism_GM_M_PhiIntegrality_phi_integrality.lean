-- Prove2me | solution 1 for Formalism.GM.M.PhiIntegrality.phi_integrality
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:40.97922+00:00
-- url     : https://prove2.me/submissions/725cc195-261f-4299-8c6b-ed12419a31af

import Definitions.Def_Formalism_MahlerMeasure_IsIntegral
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_norm_choose_inv_le
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_bnd_sum
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_bnd_smul
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_bnd_mono
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_commute_pderiv
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_contr_comp
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_contr_D
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_contr_E
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_contr_pow
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_contr_Fsum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.GM.M.PhiIntegrality
open MvPolynomial Finset
open MvPolynomial Finset
section
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type}
end
open MvPolynomial Finset
section
variable {p : ℕ} [hp : Fact p.Prime] {σ : Type}
end
open MvPolynomial Finset
section
variable {p : ℕ} [hp : Fact p.Prime] {σ : Type}
private theorem contr_finset_sum {ι : Type} {C : ℝ} (hC : 0 ≤ C) (s : Finset ι)
    (T : ι → (MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]))
    (h : ∀ i ∈ s, Contr C (T i)) : Contr C (∑ i ∈ s, T i) := by
  intro B hB u hu
  rw [LinearMap.sum_apply]
  exact bnd_sum _ _ (mul_nonneg hB hC) fun i hi => h i hi B hB u hu
private theorem contr_smul_mahler_measure {C : ℝ} (a : ℚ_[p])
    {T : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]} (h : Contr C T) :
    Contr (‖a‖ * C) (a • T) := by
  intro B hB u hu
  rw [LinearMap.smul_apply]
  exact bnd_mono (bnd_smul a (h B hB u hu)) (le_of_eq (by ring))
private theorem contr_mono' {C C' : ℝ}
    {T : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]} (h : Contr C T) (hCC : C ≤ C') :
    Contr C' T :=
  fun B hB u hu => bnd_mono (h B hB u hu) (mul_le_mul_of_nonneg_left hCC hB)
end
open MvPolynomial Finset
end Formalism.GM.M.PhiIntegrality
namespace Formalism.GM
end Formalism.GM
end

set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.PhiIntegrality
open MvPolynomial Finset
open MvPolynomial Finset
open MvPolynomial Finset
open MvPolynomial Finset
open MvPolynomial Finset
set_option maxHeartbeats 800000
namespace Formalism.GM.M.PhiIntegrality
theorem _root_.solution : PhiInt := by

  intro p hp σ r w e hw he hwe hr o n z u hu
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  set L := Nat.log p (o + n + r + z) with hL
  set Mc : ℝ := (p : ℝ) ^ L with hMcdef
  have hM1 : 1 ≤ Mc := one_le_pow₀ hp1
  have hMc0 : (0 : ℝ) ≤ Mc := zero_le_one.trans hM1
  have hM : ∀ j ≤ o, ∀ k ≤ j, ‖(((j.choose k : ℕ) : ℚ_[p]))⁻¹‖ ≤ Mc := fun j hj k hk =>
    (norm_choose_inv_le j k hk).trans (pow_le_pow_right₀ hp1 (Nat.log_mono_right (by omega)))
  have hcomm : ∀ a b : Fin r, Commute
      ((pderiv (w a) : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap ∘ₗ
        (pderiv (e a)).toLinearMap)
      ((pderiv (w b) : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap ∘ₗ
        (pderiv (e b)).toLinearMap) := fun a b =>
    ((commute_pderiv _ _).mul_right (commute_pderiv _ _)).mul_left
      ((commute_pderiv _ _).mul_right (commute_pderiv _ _))
  have hΦ : Contr (p := p) (Mc ^ (r + 1)) (Formalism.GM.tiePhi (k := ℚ_[p]) w e o n z) := by
    unfold Formalism.GM.tiePhi
    refine contr_finset_sum (pow_nonneg hMc0 _) _ _ fun j hj => ?_
    have hjo : j ≤ o := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hterm : (((-1 : ℚ_[p]) ^ j) / (((j.factorial : ℚ_[p]) ^ 2) *
          ((o + n + r + z - 1).choose j : ℚ_[p]))) •
          (((Formalism.GM.tieE (k := ℚ_[p]) w e) ^ j).comp ((Formalism.GM.tieF (k := ℚ_[p]) w e) ^ j)) =
        ((-1 : ℚ_[p]) ^ j * (((o + n + r + z - 1).choose j : ℕ) : ℚ_[p])⁻¹) •
          ((Formalism.GM.tieE (k := ℚ_[p]) w e) ^ j *
            ((((j.factorial : ℚ_[p]) ^ 2))⁻¹ • (Formalism.GM.tieF (k := ℚ_[p]) w e) ^ j)) := by
      rw [mul_smul_comm, smul_smul, Module.End.mul_eq_comp]
      congr 1
      rw [div_eq_mul_inv, mul_inv]
      ring
    rw [hterm]
    have hF := contr_Fsum (p := p) _ hcomm (fun a k => contr_D (w a) (e a) k) hM1 o hM Finset.univ j hjo
    simp only [Finset.card_univ, Fintype.card_fin] at hF
    have hE := contr_pow (C := 1) zero_le_one (contr_E (p := p) w e) j
    have h1 := contr_smul_mahler_measure ((-1 : ℚ_[p]) ^ j * (((o + n + r + z - 1).choose j : ℕ) : ℚ_[p])⁻¹)
      (contr_comp (pow_nonneg hMc0 _) hF hE)
    refine contr_mono' (by unfold Formalism.GM.tieF; exact h1) ?_
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, mul_one, pow_succ' Mc r]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hMc0 _)
    exact (norm_choose_inv_le _ j (by omega)).trans (pow_le_pow_right₀ hp1 (Nat.log_mono_right (by omega)))
  have hv := hΦ 1 zero_le_one u hu
  have hs := bnd_smul ((p : ℚ_[p]) ^ ((r + 1) * (L + 1))) hv
  refine bnd_mono hs ?_
  rw [norm_pow, Padic.norm_p, one_mul, hMcdef, ← pow_mul, inv_pow]
  have : ((p : ℝ) ^ ((r + 1) * (L + 1)))⁻¹ * (p : ℝ) ^ (L * (r + 1)) = ((p : ℝ) ^ (r + 1))⁻¹ := by
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    rw [show (r + 1) * (L + 1) = L * (r + 1) + (r + 1) by ring, pow_add]
    field_simp
  rw [this]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hp1)
end Formalism.GM.M.PhiIntegrality
