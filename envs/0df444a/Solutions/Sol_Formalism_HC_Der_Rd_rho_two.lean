-- Prove2me | solution 1 for Formalism.HC.Der.Rd.rho_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:21.722045+00:00
-- url     : https://prove2.me/submissions/2e36cad3-83f6-4a52-872d-60fa9798fcd6

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdBound
import Theorems.Thm_Formalism_HC_Der_Rd_card_KK
import Theorems.Thm_Formalism_HC_Der_Rd_mem_KK
import Theorems.Thm_Formalism_HC_Der_Rd_mem_ker_iff
import Theorems.Thm_Formalism_HC_Der_Rd_one_mem_KK
import Theorems.Thm_Formalism_HC_Der_Rd_rho_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ArithmeticFunction Finset
noncomputable section
namespace Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ)
private theorem coe_unitsMap_eq_cast_val_of_dvd_neZero {m n : ℕ} [NeZero m] (h : n ∣ m) (u : (ZMod m)ˣ) :
    ((ZMod.unitsMap h u : (ZMod n)ˣ) : ZMod n) = ((u : ZMod m).val : ZMod n) := by
  rw [← ZMod.cast_eq_val]; rfl
end Formalism.HC.Der.Rd
end
end

set_option autoImplicit false
open ArithmeticFunction Finset
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ)
namespace Formalism.HC.Der.Rd
theorem _root_.solution {e M i : ℕ} (hM : Nat.Coprime 2 M) (hN : 2 ^ (e + 2) * M ∣ N) (hi : i ≤ e + 2)
    (hU : ∀ u ∈ U, ZMod.unitsMap ((dvd_mul_right _ M).trans hN) u = 1 ∨ ZMod.unitsMap ((dvd_mul_right _ M).trans hN) u = -1) :
    1 - (((2 ^ i).totient : ℝ) + if i < 2 then 1 else 0) / 2 ^ (e + 1) ≤ rho U (2 ^ i * M) := by
  open Classical in
  have card_filter_mem_le_lemma_6 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) {e M i : ℕ} (hM : Nat.Coprime 2 M) (hN : 2 ^ (e + 2) * M ∣ N)
      (hi : i ≤ e + 2)
      (hU : ∀ u ∈ U, ZMod.unitsMap ((dvd_mul_right _ M).trans hN) u = 1 ∨
        ZMod.unitsMap ((dvd_mul_right _ M).trans hN) u = -1) :
      ((KK N (2 ^ i * M)).filter fun u => u ∈ U).card
        ≤ (if i < 2 then 2 else 1) * (KK N (2 ^ (e + 2) * M)).card := by
    have h2 : 2 ^ (e + 2) ∣ N := (dvd_mul_right _ M).trans hN
    have hMN : M ∣ N := (dvd_mul_left M _).trans hN
    have hcop : Nat.Coprime (2 ^ (e + 2)) M := Nat.Coprime.pow_left _ hM
    have hA : ∀ v : (ZMod N)ˣ, v ∈ (ZMod.unitsMap hMN).ker → ZMod.unitsMap h2 v = 1 →
        v ∈ KK N (2 ^ (e + 2) * M) := by
      intro v hv1 hv2
      rw [mem_KK]
      rw [mem_ker_iff] at hv1
      have hv2' := (mem_ker_iff h2 v).mp (MonoidHom.mem_ker.mpr hv2)
      exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hv2', hv1⟩
    have hKM : ∀ u ∈ KK N (2 ^ i * M), u ∈ (ZMod.unitsMap hMN).ker := by
      intro u hu
      rw [mem_ker_iff]
      exact Nat.ModEq.of_mul_left (2 ^ i) (mem_KK.mp hu)
    have hneg : 2 ≤ i → ∀ u ∈ KK N (2 ^ i * M), ZMod.unitsMap h2 u ≠ -1 := by
      intro hi2 u hu hneg1
      have hval := congrArg Units.val hneg1
      rw [coe_unitsMap_eq_cast_val_of_dvd_neZero, Units.val_neg, Units.val_one] at hval
      have h1 : (((u : ZMod N).val + 1 : ℕ) : ZMod (2 ^ (e + 2))) = 0 := by
        push_cast; rw [hval]; ring
      rw [CharP.cast_eq_zero_iff (ZMod (2 ^ (e + 2))) (2 ^ (e + 2))] at h1
      have h4 : 4 ∣ (u : ZMod N).val + 1 := by
        have h5 := (pow_dvd_pow 2 (by omega : 2 ≤ e + 2)).trans h1
        simpa using h5
      have h4' : (u : ZMod N).val ≡ 1 [MOD 4] := by
        have h6 := Nat.ModEq.of_dvd ((pow_dvd_pow 2 hi2).trans (dvd_mul_right _ M))
          (mem_KK.mp hu)
        simpa using h6
      unfold Nat.ModEq at h4'
      omega
    by_cases hi2 : i < 2
    · rw [if_pos hi2]
      by_cases hw : ∃ w ∈ (KK N (2 ^ i * M)).filter (fun u => u ∈ U),
          ZMod.unitsMap h2 w = -1
      · obtain ⟨w, hwH, hw1⟩ := hw
        rw [Finset.mem_filter] at hwH
        have hsub : (KK N (2 ^ i * M)).filter (fun u => u ∈ U) ⊆
            KK N (2 ^ (e + 2) * M) ∪
              (KK N (2 ^ (e + 2) * M)).image (fun x => w * x) := by
          intro u hu
          rw [Finset.mem_filter] at hu
          rcases hU u hu.2 with h1 | h1
          · exact Finset.mem_union_left _ (hA u (hKM u hu.1) h1)
          · apply Finset.mem_union_right
            rw [Finset.mem_image]
            refine ⟨w⁻¹ * u, hA _ ?_ ?_, mul_inv_cancel_left w u⟩
            · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKM w hwH.1)) (hKM u hu.1)
            · rw [map_mul, map_inv, hw1, h1, inv_mul_cancel]
        calc _ ≤ _ := Finset.card_le_card hsub
          _ ≤ _ := Finset.card_union_le _ _
          _ ≤ _ := Nat.add_le_add_left Finset.card_image_le _
          _ = 2 * (KK N (2 ^ (e + 2) * M)).card := by ring
      · push_neg at hw
        calc _ ≤ (KK N (2 ^ (e + 2) * M)).card := Finset.card_le_card (fun u hu => by
              rw [Finset.mem_filter] at hu
              rcases hU u hu.2 with h1 | h1
              · exact hA u (hKM u hu.1) h1
              · exact absurd h1 (hw u (Finset.mem_filter.mpr hu)))
          _ ≤ 2 * _ := by omega
    · rw [if_neg hi2]
      calc _ ≤ (KK N (2 ^ (e + 2) * M)).card := Finset.card_le_card (fun u hu => by
            rw [Finset.mem_filter] at hu
            rcases hU u hu.2 with h1 | h1
            · exact hA u (hKM u hu.1) h1
            · exact absurd h1 (hneg (by omega) u hu.1))
        _ = 1 * _ := (one_mul _).symm
  classical
  have hf : 2 ^ i * M ∣ N := (Nat.mul_dvd_mul_right (pow_dvd_pow 2 hi) M).trans hN
  have hcard := card_filter_mem_le_lemma_6 U hM hN hi hU
  have hA := card_KK (N := N) hN
  have hApos : 0 < (KK N (2 ^ (e + 2) * M)).card :=
    Finset.card_pos.mpr ⟨1, one_mem_KK hN⟩
  have hφf : (2 ^ i * M).totient = (2 ^ i).totient * M.totient :=
    Nat.totient_mul (Nat.Coprime.pow_left _ hM)
  have hφL : (2 ^ (e + 2) * M).totient = 2 ^ (e + 1) * M.totient := by
    rw [Nat.totient_mul (Nat.Coprime.pow_left _ hM), show e + 2 = e + 1 + 1 from rfl,
      Nat.totient_prime_pow_succ Nat.prime_two]
    norm_num
  have hMpos : 0 < M.totient := Nat.totient_pos.mpr
    (Nat.pos_of_dvd_of_pos ((dvd_mul_left M _).trans hN) (Nat.pos_of_ne_zero (NeZero.ne N)))
  have hT : (N.totient : ℝ) = (KK N (2 ^ (e + 2) * M)).card * (2 ^ (e + 1) * M.totient) := by
    rw [← hA, hφL]; push_cast; ring
  have hkey : (((KK N (2 ^ i * M)).filter fun u => u ∈ U).card : ℝ) * (2 ^ i).totient
      ≤ (((2 ^ i).totient : ℝ) + if i < 2 then 1 else 0) * (KK N (2 ^ (e + 2) * M)).card := by
    by_cases hi2 : i < 2
    · rw [if_pos hi2] at hcard ⊢
      have ht : (2 ^ i).totient = 1 := by interval_cases i <;> simp
      rw [ht]
      have : (((KK N (2 ^ i * M)).filter fun u => u ∈ U).card : ℝ)
          ≤ 2 * (KK N (2 ^ (e + 2) * M)).card := by exact_mod_cast hcard
      push_cast
      linarith
    · rw [if_neg hi2] at hcard ⊢
      have : (((KK N (2 ^ i * M)).filter fun u => u ∈ U).card : ℝ)
          ≤ (KK N (2 ^ (e + 2) * M)).card := by
        have := hcard; rw [one_mul] at this; exact_mod_cast this
      have ht0 : (0 : ℝ) ≤ (2 ^ i).totient := Nat.cast_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right this ht0]
  rw [rho_eq U hf, hφf, hT]
  push_cast
  have ha : (0 : ℝ) < (KK N (2 ^ (e + 2) * M)).card := by exact_mod_cast hApos
  have hs : (0 : ℝ) < M.totient := by exact_mod_cast hMpos
  have hp : (0 : ℝ) < 2 ^ (e + 1) := by positivity
  suffices h : (((KK N (2 ^ i * M)).filter fun u => u ∈ U).card : ℝ)
      * (((2 ^ i).totient : ℝ) * M.totient)
      / ((KK N (2 ^ (e + 2) * M)).card * (2 ^ (e + 1) * M.totient))
      ≤ (((2 ^ i).totient : ℝ) + if i < 2 then 1 else 0) / 2 ^ (e + 1) by linarith
  rw [div_le_div_iff₀ (mul_pos ha (mul_pos hp hs)) hp]
  nlinarith [mul_le_mul_of_nonneg_right hkey (le_of_lt (mul_pos hs hp))]
end Formalism.HC.Der.Rd
