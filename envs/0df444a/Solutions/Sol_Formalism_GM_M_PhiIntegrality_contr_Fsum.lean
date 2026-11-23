-- Prove2me | solution 1 for Formalism.GM.M.PhiIntegrality.contr_Fsum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:39.157915+00:00
-- url     : https://prove2.me/submissions/edb38820-0ccb-46d0-8fff-a29cb383f7c4

import Definitions.Def_Formalism_MahlerMeasure_IsIntegral
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_bnd_sum
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_bnd_smul
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_bnd_mono
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_contr_comp
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
private theorem inv_factorial_sq_mul_choose_eq {j m : ℕ} (hm : m ≤ j) :
    (((j.factorial : ℚ_[p]) ^ 2))⁻¹ * ((j.choose m : ℕ) : ℚ_[p]) =
      (((j.choose m : ℕ) : ℚ_[p]))⁻¹ *
        ((((m.factorial : ℚ_[p]) ^ 2))⁻¹ * ((((j - m).factorial : ℚ_[p]) ^ 2))⁻¹) := by
  have h := Nat.choose_mul_factorial_mul_factorial hm
  have hc : ((j.choose m : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hm).ne'
  have h1 : (m.factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have h2 : ((j - m).factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast (j - m).factorial_ne_zero
  rw [← h]
  push_cast
  field_simp
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
variable {p : ℕ} [hp : Fact p.Prime] {σ : Type}
namespace Formalism.GM.M.PhiIntegrality
theorem _root_.solution {ι : Type} [DecidableEq ι]
    (D : ι → (MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]))
    (hcomm : ∀ a b, Commute (D a) (D b))
    (hdiv : ∀ a k, Contr 1 ((((k.factorial : ℚ_[p]) ^ 2))⁻¹ • (D a ^ k)))
    {Mc : ℝ} (hM1 : 1 ≤ Mc) (N : ℕ)
    (hM : ∀ j ≤ N, ∀ k ≤ j, ‖(((j.choose k : ℕ) : ℚ_[p]))⁻¹‖ ≤ Mc) (S : Finset ι) :
    ∀ j ≤ N, Contr (Mc ^ S.card) ((((j.factorial : ℚ_[p]) ^ 2))⁻¹ • ((∑ c ∈ S, D c) ^ j)) := by

  have hMc0 : (0 : ℝ) ≤ Mc := zero_le_one.trans hM1
  induction S using Finset.induction_on with
  | empty =>
    intro j _
    rcases j with _ | j
    · intro B hB u hu m
      simpa using hu m
    · intro B hB u hu m
      simp [hB]
  | @insert a s ha ih =>
    intro j hj
    have hc : Commute (D a) (∑ c ∈ s, D c) := Commute.sum_right _ _ _ fun c _ => hcomm a c
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, hc.add_pow, Finset.smul_sum]
    refine contr_finset_sum (pow_nonneg hMc0 _) _ _ fun m hm => ?_
    have hmj : m ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [← Nat.cast_comm, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ_[p], smul_smul, inv_factorial_sq_mul_choose_eq hmj,
      ← smul_smul, ← smul_mul_smul_comm]
    have h1 := contr_smul_mahler_measure (((j.choose m : ℕ) : ℚ_[p]))⁻¹
      (contr_comp (pow_nonneg hMc0 _) (ih (j - m) (by omega)) (hdiv a m))
    refine contr_mono' h1 ?_
    rw [mul_one, pow_succ']
    exact mul_le_mul_of_nonneg_right (hM j hj m hmj) (pow_nonneg hMc0 _)
end Formalism.GM.M.PhiIntegrality
