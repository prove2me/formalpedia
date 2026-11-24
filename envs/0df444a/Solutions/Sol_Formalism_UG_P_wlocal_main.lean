-- Prove2me | solution 1 for Formalism.UG.P.wlocal_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:10:41.120808+00:00
-- url     : https://prove2.me/submissions/9e9a4187-a015-47c5-9765-4b8ac96dd35d

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Theorems.Thm_Formalism_UG_P_wlocal_E_mul_apply
import Theorems.Thm_Formalism_UG_P_wlocal_L_mul_apply
import Theorems.Thm_Formalism_UG_P_wlocal_good_one
import Theorems.Thm_Formalism_UG_P_wlocal_good_E
import Theorems.Thm_Formalism_UG_P_wlocal_E_zero
import Theorems.Thm_Formalism_UG_P_wlocal_E_mul_E
import Theorems.Thm_Formalism_UG_P_wlocal_L_mul_L
import Theorems.Thm_Formalism_UG_P_wlocal_L_one
import Theorems.Thm_Formalism_UG_P_wlocal_good_L
import Theorems.Thm_Formalism_UG_P_wlocal_good_of_factor
import Theorems.Thm_Formalism_UG_P_wlocal_unit_add
import Theorems.Thm_Formalism_UG_P_wlocal_pivot
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


section
open MvPolynomial
noncomputable section
namespace Formalism.UG.P
open Formalism.GradedWeylDivisibility
section
variable {R : Type} [CommRing R]
end
section
variable {R : Type} [CommRing R]
end
section
variable {R : Type} [CommRing R]
variable [IsLocalRing R]
private lemma mul_mul_mul_eq_one_of_inverses {r : ℕ} {N M A B : Matrix (Fin r) (Fin r) R} (h : N * M = 1)
    (hBA : B * A = 1) : N * B * (A * M) = 1 := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc B A M, hBA, Matrix.one_mul, h]
end
section
variable {R S : Type} [CommRing R] [CommRing S]
end
section
variable {R : Type} [CommRing R]
end
end Formalism.UG.P
end
end

set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.GradedWeylDivisibility
variable {R : Type} [CommRing R]
variable [IsLocalRing R]
namespace Formalism.UG.P
theorem _root_.solution {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    ∀ d k : ℕ, k + d = r → ∀ M N : Matrix (Fin r) (Fin r) R, N * M = 1 →
      (∀ i j : Fin r, j.val < k → M i j = if i = j then 1 else 0) → wlocal_Good hn ν M := by
  intro d
  induction d with
  | zero =>
    intro k hk M N _ hstd
    have hM : M = 1 := by
      ext i j
      rw [hstd i j (by have := j.isLt; omega), Matrix.one_apply]
    rw [hM]
    exact wlocal_good_one hn ν
  | succ d ih =>
    intro k hk M N hNM hstd
    have hkr : k < r := by omega
    obtain ⟨kk, hkk⟩ : ∃ kk : Fin r, kk.val = k := ⟨⟨k, hkr⟩, rfl⟩
    have cont : ∀ P P' : Matrix (Fin r) (Fin r) R, P' * P = 1 → wlocal_Good hn ν P' →
        IsUnit ((P * M) kk kk) →
        (∀ l j : Fin r, j.val < k → (P * M) l j = if l = j then 1 else 0) → wlocal_Good hn ν M := by
      intro P P' hPP hP' hunit hstd1
      obtain ⟨u, hu⟩ := hunit
      obtain ⟨M1, hM1⟩ : ∃ M1, M1 = P * M := ⟨_, rfl⟩
      rw [← hM1] at hu hstd1
      obtain ⟨M2, hM2⟩ : ∃ M2, M2 = wlocal_E kk kk ((↑u⁻¹ : R) - 1) * M1 := ⟨_, rfl⟩
      have h2 : ∀ l j : Fin r, M2 l j = M1 l j + (if l = kk then ((↑u⁻¹ : R) - 1) * M1 kk j else 0) := by
        intro l j
        rw [hM2, wlocal_E_mul_apply]
      have h2kk : M2 kk kk = 1 := by
        rw [h2, if_pos rfl, ← hu]
        linear_combination (Units.inv_mul u)
      have h2std : ∀ l j : Fin r, j.val < k → M2 l j = if l = j then 1 else 0 := by
        intro l j hj
        have hkj : kk ≠ j := by
          intro h
          rw [← h] at hj
          omega
        rw [h2, hstd1 l j hj, hstd1 kk j hj, if_neg hkj, mul_zero, ite_self, add_zero]
      obtain ⟨M3, hM3⟩ : ∃ M3, M3 = wlocal_L kk (fun l => -(M2 l kk)) * M2 := ⟨_, rfl⟩
      have h3 : ∀ l j : Fin r, M3 l j = M2 l j + (if l ≠ kk then -(M2 l kk) * M2 kk j else 0) := by
        intro l j
        rw [hM3, wlocal_L_mul_apply]
      have h3std : ∀ l j : Fin r, j.val < k + 1 → M3 l j = if l = j then 1 else 0 := by
        intro l j hj
        rw [h3]
        by_cases hjk : j.val < k
        · have hkj : kk ≠ j := by
            intro h
            rw [← h] at hjk
            omega
          rw [h2std l j hjk, h2std kk j hjk, if_neg hkj, mul_zero, ite_self, add_zero]
        · have hj' : j = kk := by
            apply Fin.ext
            omega
          rw [hj', h2kk, mul_one]
          by_cases hl : l = kk
          · simp [hl, h2kk]
          · rw [if_pos hl, if_neg hl]
            ring
      have hLL : wlocal_L kk (fun l => M2 l kk) * wlocal_L kk (fun l => -(M2 l kk)) = 1 := by
        rw [wlocal_L_mul_L]
        have h0 : ((fun l => M2 l kk) + fun l => -(M2 l kk)) = (0 : Fin r → R) := by
          funext l
          simp
        rw [h0, wlocal_L_one]
      have hEE : wlocal_E kk kk ((u : R) - 1) * wlocal_E kk kk ((↑u⁻¹ : R) - 1) = 1 := by
        rw [wlocal_E_mul_E, if_pos rfl,
          show ((u : R) - 1) + ((↑u⁻¹ : R) - 1) + ((u : R) - 1) * ((↑u⁻¹ : R) - 1) = 0 by
            linear_combination (Units.mul_inv u),
          wlocal_E_zero]
      have hN1 : N * P' * M1 = 1 := by
        rw [hM1]
        exact mul_mul_mul_eq_one_of_inverses hNM hPP
      have hN2 : N * P' * wlocal_E kk kk ((u : R) - 1) * M2 = 1 := by
        rw [hM2]
        exact mul_mul_mul_eq_one_of_inverses hN1 hEE
      have hN3 : N * P' * wlocal_E kk kk ((u : R) - 1) * wlocal_L kk (fun l => M2 l kk) * M3 = 1 := by
        rw [hM3]
        exact mul_mul_mul_eq_one_of_inverses hN2 hLL
      have hM3g : wlocal_Good hn ν M3 := ih (k + 1) (by omega) M3 _ hN3 h3std
      have hM2g : wlocal_Good hn ν M2 :=
        wlocal_good_of_factor (wlocal_good_L hn ν kk (fun l => M2 l kk)) hLL (by rw [← hM3]; exact hM3g)
      have hM1g : wlocal_Good hn ν M1 :=
        wlocal_good_of_factor (wlocal_good_E hn ν kk kk ((u : R) - 1)) hEE (by rw [← hM2]; exact hM2g)
      exact wlocal_good_of_factor hP' hPP (by rw [← hM1]; exact hM1g)
    by_cases hu0 : IsUnit (M kk kk)
    · refine cont 1 1 (Matrix.one_mul 1) (wlocal_good_one hn ν) ?_ ?_
      · rw [Matrix.one_mul]
        exact hu0
      · intro l j hj
        rw [Matrix.one_mul]
        exact hstd l j hj
    · obtain ⟨i, hki, hiu⟩ := wlocal_pivot kk M N hNM (by intro i j hj; exact hstd i j (by omega))
      have hik : i ≠ kk := by
        intro h
        rw [h] at hiu
        exact hu0 hiu
      refine cont (wlocal_E kk i 1) (wlocal_E kk i (-1)) ?_ (wlocal_good_E hn ν kk i (-1)) ?_ ?_
      · rw [wlocal_E_mul_E, if_neg (Ne.symm hik), show (-1 : R) + 1 + 0 = 0 by ring, wlocal_E_zero]
      · rw [wlocal_E_mul_apply, if_pos rfl, one_mul]
        exact wlocal_unit_add hu0 hiu
      · intro l j hj
        have hij : i ≠ j := by
          intro h
          rw [← h] at hj
          omega
        rw [wlocal_E_mul_apply, hstd i j hj, if_neg hij, mul_zero, ite_self, add_zero]
        exact hstd l j hj
end Formalism.UG.P
