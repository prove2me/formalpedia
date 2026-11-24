-- Prove2me | solution 1 for Formalism.HC.Der.Rd.SS_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:09.845801+00:00
-- url     : https://prove2.me/submissions/3fc2a8ca-4ead-4bb3-b02e-1f38bc535938

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdBound
import Theorems.Thm_Formalism_HC_Der_Rd_rho_le
import Theorems.Thm_Formalism_HC_Der_Rd_weight_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ArithmeticFunction Finset
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ)
namespace Formalism.HC.Der.Rd
theorem _root_.solution {q d : ℕ} (h2 : 2 ∣ N) (hq : q.Prime) (hd : d.Prime) (hqN : q ∣ N) (hdN : d ∣ N) (hq2 : ¬ 2 ∣ q)
    (hd2 : ¬ 2 ∣ d) (hqd : q ≠ d) (rq : rho U (N / q) ≤ 1 / 2) (rd : rho U (N / d) ≤ 1 / 2) :
    SS U ≤ Real.log N - Real.log 2 - Real.log q / 2 - Real.log d / 2 := by
  classical
  have hN0 : N ≠ 0 := NeZero.ne N
  have hT : (0 : ℝ) < N.totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN0)
  have hqD : q ∈ N.divisors := Nat.mem_divisors.mpr ⟨hqN, hN0⟩
  have hdD : d ∈ N.divisors.erase q :=
    Finset.mem_erase.mpr ⟨hqd.symm, Nat.mem_divisors.mpr ⟨hdN, hN0⟩⟩
  have hRsub : ∀ m ∈ (N.divisors.erase q).erase d, m ∣ N := fun m hm =>
    Nat.dvd_of_mem_divisors (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hm))
  have hterm : ∀ m ∈ (N.divisors.erase q).erase d,
      vonMangoldt m * rho U (N / m)
        ≤ vonMangoldt m - vonMangoldt m * ((N / m).totient : ℝ) / N.totient := by
    intro m hm
    have h1 := mul_le_mul_of_nonneg_left
      (rho_le U (Nat.div_dvd_of_dvd (hRsub m hm))) (vonMangoldt_nonneg (n := m))
    calc _ ≤ _ := h1
      _ = _ := by ring
  have h2sub : N.divisors.filter (fun m => 2 ∣ m) ⊆ (N.divisors.erase q).erase d := by
    intro m hm
    rw [Finset.mem_filter] at hm
    rw [Finset.mem_erase, Finset.mem_erase]
    exact ⟨fun h => hd2 (h ▸ hm.2), fun h => hq2 (h ▸ hm.2), hm.1⟩
  have h2val : ∑ m ∈ N.divisors.filter (fun m => 2 ∣ m),
      vonMangoldt m * ((N / m).totient : ℝ) / N.totient = Real.log 2 := by
    have h := weight_sum hN0 h2 (by norm_num : (2 : ℕ) ≠ 1)
    rw [vonMangoldt_apply_prime Nat.prime_two, Nat.totient_two, Nat.cast_one, div_one,
      Nat.cast_ofNat] at h
    rw [← Finset.sum_div, h, div_eq_iff hT.ne']
    ring
  have hgR : Real.log 2 ≤ ∑ m ∈ (N.divisors.erase q).erase d,
      vonMangoldt m * ((N / m).totient : ℝ) / N.totient := by
    rw [← h2val]
    apply Finset.sum_le_sum_of_subset_of_nonneg h2sub
    intro m _ _
    exact div_nonneg (mul_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hRsum : ∑ m ∈ (N.divisors.erase q).erase d, vonMangoldt m * rho U (N / m)
      ≤ ∑ m ∈ (N.divisors.erase q).erase d, vonMangoldt m
        - ∑ m ∈ (N.divisors.erase q).erase d, vonMangoldt m * ((N / m).totient : ℝ) / N.totient := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_le_sum hterm
  have hΛsum : Real.log N
      = vonMangoldt q + (vonMangoldt d + ∑ m ∈ (N.divisors.erase q).erase d, vonMangoldt m) := by
    rw [← vonMangoldt_sum, ← Finset.add_sum_erase _ _ hqD, ← Finset.add_sum_erase _ _ hdD]
  have hwsplit : SS U
      = vonMangoldt q * rho U (N / q) + (vonMangoldt d * rho U (N / d)
        + ∑ m ∈ (N.divisors.erase q).erase d, vonMangoldt m * rho U (N / m)) := by
    unfold SS
    rw [← Finset.add_sum_erase _ _ hqD, ← Finset.add_sum_erase _ _ hdD]
  have hqt : vonMangoldt q * rho U (N / q) ≤ vonMangoldt q * (1 / 2) :=
    mul_le_mul_of_nonneg_left rq vonMangoldt_nonneg
  have hdt : vonMangoldt d * rho U (N / d) ≤ vonMangoldt d * (1 / 2) :=
    mul_le_mul_of_nonneg_left rd vonMangoldt_nonneg
  have hΛq : vonMangoldt q = Real.log q := vonMangoldt_apply_prime hq
  have hΛd : vonMangoldt d = Real.log d := vonMangoldt_apply_prime hd
  linarith
end Formalism.HC.Der.Rd
