-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_sum_vM_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:31.492696+00:00
-- url     : https://prove2.me/submissions/ef794f36-8391-4579-ad11-369b03ec41a0

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
open ArithmeticFunction (vonMangoldt)
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution (N : ℕ) : ∑ n ∈ Icc 1 N, vonMangoldt n ≤ dA_KC * N := by
  have hθ : ∀ M : ℕ, ∑ n ∈ (Icc 1 M).filter Nat.Prime, vonMangoldt n ≤ M * Real.log 4 := by
    intro M
    have hsub : (Icc 1 M).filter Nat.Prime ⊆ (range (M + 1)).filter Nat.Prime := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hn ⊢
      exact ⟨by omega, hn.2⟩
    have hdvd := Finset.prod_dvd_prod_of_subset _ _ (fun n => n) hsub
    have hle : ∏ n ∈ (Icc 1 M).filter Nat.Prime, n ≤ primorial M :=
      Nat.le_of_dvd (primorial_pos M) hdvd
    have hpos : 0 < ∏ n ∈ (Icc 1 M).filter Nat.Prime, n :=
      Finset.prod_pos (fun n hn => (Finset.mem_filter.mp hn).2.pos)
    have hlog : ∑ n ∈ (Icc 1 M).filter Nat.Prime, vonMangoldt n
        = Real.log ((∏ n ∈ (Icc 1 M).filter Nat.Prime, n : ℕ) : ℝ) := by
      rw [Nat.cast_prod, Real.log_prod]
      · refine Finset.sum_congr rfl (fun n hn => ?_)
        rw [Finset.mem_filter] at hn
        exact ArithmeticFunction.vonMangoldt_apply_prime hn.2
      · intro n hn
        rw [Finset.mem_filter] at hn
        exact Nat.cast_ne_zero.mpr hn.2.ne_zero
    rw [hlog]
    calc Real.log ((∏ n ∈ (Icc 1 M).filter Nat.Prime, n : ℕ) : ℝ) ≤ Real.log (primorial M : ℝ) :=
          Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)
      _ ≤ Real.log ((4:ℝ) ^ M) :=
          Real.log_le_log (by exact_mod_cast primorial_pos M) (by exact_mod_cast primorial_le_4_pow M)
      _ = M * Real.log 4 := Real.log_pow 4 M
  have hR : ∀ M : ℕ, ∑ n ∈ (Icc 1 M).filter (fun n => ¬ n.Prime), vonMangoldt n
      ≤ ∑ n ∈ Icc 1 (M / 2), vonMangoldt n := by
    intro M
    have hinv : ∀ m ∈ (Icc 1 (M / 2)).filter IsPrimePow, m * m.minFac / (m * m.minFac).minFac = m := by
      intro m hm
      rw [Finset.mem_filter] at hm
      obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff _).mp hm.2
      rw [hp.pow_minFac hj.ne', ← pow_succ, hp.pow_minFac (show j + 1 ≠ 0 by omega), pow_succ,
        Nat.mul_div_cancel _ hp.pos]
    have hval : ∀ m ∈ (Icc 1 (M / 2)).filter IsPrimePow, vonMangoldt (m * m.minFac) = vonMangoldt m := by
      intro m hm
      rw [Finset.mem_filter] at hm
      obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff _).mp hm.2
      rw [hp.pow_minFac hj.ne', ← pow_succ,
        ArithmeticFunction.vonMangoldt_apply_pow (show j + 1 ≠ 0 by omega),
        ArithmeticFunction.vonMangoldt_apply_pow hj.ne']
    have hsub : ((Icc 1 M).filter (fun n => ¬ n.Prime)).filter IsPrimePow
        ⊆ ((Icc 1 (M / 2)).filter IsPrimePow).image (fun m => m * m.minFac) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨⟨hn1, hnM⟩, hnp⟩, hpp⟩ := hn
      rw [isPrimePow_nat_iff] at hpp
      obtain ⟨p, k, hp, hk, rfl⟩ := hpp
      have hk2 : 2 ≤ k := by
        by_contra hlt
        apply hnp
        rw [show k = 1 by omega, pow_one]
        exact hp
      rw [Finset.mem_image]
      refine ⟨p ^ (k - 1), ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨Nat.one_le_pow _ _ hp.pos, ?_⟩,
          (isPrimePow_nat_iff _).mpr ⟨p, k - 1, hp, by omega, rfl⟩⟩
        rw [Nat.le_div_iff_mul_le (by norm_num)]
        calc p ^ (k - 1) * 2 ≤ p ^ (k - 1) * p := Nat.mul_le_mul_left _ hp.two_le
          _ = p ^ k := by rw [← pow_succ]; congr 1; omega
          _ ≤ M := hnM
      · show p ^ (k - 1) * (p ^ (k - 1)).minFac = p ^ k
        rw [hp.pow_minFac (by omega), ← pow_succ]
        congr 1
        omega
    calc ∑ n ∈ (Icc 1 M).filter (fun n => ¬ n.Prime), vonMangoldt n
        = ∑ n ∈ ((Icc 1 M).filter (fun n => ¬ n.Prime)).filter IsPrimePow, vonMangoldt n :=
          (Finset.sum_filter_of_ne (fun n _ hn => not_not.mp
            (fun h => hn (ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h)))).symm
      _ ≤ ∑ n ∈ ((Icc 1 (M / 2)).filter IsPrimePow).image (fun m => m * m.minFac), vonMangoldt n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
      _ = ∑ m ∈ (Icc 1 (M / 2)).filter IsPrimePow, vonMangoldt (m * m.minFac) :=
          Finset.sum_image (fun a ha b hb h =>
            (hinv a ha).symm.trans ((congrArg (fun t => t / t.minFac) h).trans (hinv b hb)))
      _ = ∑ m ∈ (Icc 1 (M / 2)).filter IsPrimePow, vonMangoldt m := Finset.sum_congr rfl hval
      _ ≤ ∑ n ∈ Icc 1 (M / 2), vonMangoldt n :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hl4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hl4 : Real.log 4 ≤ 4 := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num)
    linarith
  simp only [dA_KC]
  refine Nat.strong_induction_on N ?_
  intro N ih
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp [Finset.Icc_eq_empty_of_lt (show (0:ℕ) < 1 by norm_num)]
  have hN2 : N / 2 < N := Nat.div_lt_self hpos (by norm_num)
  have ih2 := ih (N / 2) hN2
  have hcast : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := Nat.cast_div_le
  have hcK := mul_le_mul_of_nonneg_left hcast (show (0:ℝ) ≤ Real.log 4 + 4 by linarith)
  have hN4 := mul_le_mul_of_nonneg_left hl4 (Nat.cast_nonneg N : (0:ℝ) ≤ N)
  rw [← Finset.sum_filter_add_sum_filter_not (Icc 1 N) Nat.Prime]
  have h1 := hθ N
  have h2 := hR N
  nlinarith
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
