-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.local_estimate_second
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:20:00.985362+00:00
-- url     : https://prove2.me/submissions/ab116eea-061f-459f-9b5a-fa59879bb0d9

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CrossFactorCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_SquareSetMemExceptionalUnion
import Theorems.Thm_P2M_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_e3__nonneg_6e96a0337fe1
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_wt_caseA
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_wt_caseB
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_square_set_mem_exceptional_union
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_cube_div_fourth_sub_one_le
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_div_fourth_sub_one_le
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_wtOf_biUnion_le
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_wtOf_union_le
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8


section
open Finset Polynomial
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
section sets
variable (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L]
variable {K L}
end sets
private theorem two_pow_card_primeFactors_le_add_one (n : ℕ) : 2 ^ n.primeFactors.card ≤ n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · calc 2 ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, 2 := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ n.primeFactors, p :=
          Finset.prod_le_prod (fun _ _ => by positivity)
            (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      _ ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
      _ ≤ n + 1 := Nat.le_succ n
private theorem sum_le_wtOf_of_subset {α : Type} [Fintype α] (μ : α → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (T : Finset α) (S : Set α) (hT : ∀ x ∈ T, x ∈ S) : ∑ x ∈ T, μ x ≤ wtOf μ S := by
  unfold wtOf
  rw [← Finset.sum_indicator_subset μ (Finset.subset_univ T)]
  exact Finset.sum_le_sum fun x _ =>
    Set.indicator_le_indicator_of_subset (fun y hy => hT y hy) hμ x
private theorem sum_Icc_two_mul_pow_le_sixteen_thirds_mul_sq (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 8) (N : ℕ) :
    ∑ δ ∈ Finset.Icc 2 N, (δ : ℝ) * x ^ δ ≤ 16 / 3 * x ^ 2 := by
  have h2x0 : 0 ≤ 2 * x := by linarith
  have h2x1 : 2 * x < 1 := by linarith
  calc ∑ δ ∈ Finset.Icc 2 N, (δ : ℝ) * x ^ δ ≤ ∑ δ ∈ Finset.Ico 2 (N + 1), (2 * x) ^ δ := by
        rw [show Finset.Icc 2 N = Finset.Ico 2 (N + 1) by
          ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
        apply Finset.sum_le_sum
        intro δ _
        rw [mul_pow]
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hx0 _)
        exact_mod_cast (Nat.lt_two_pow_self).le
    _ ≤ (2 * x) ^ 2 / (1 - 2 * x) := geom_sum_Ico_le_of_lt_one h2x0 h2x1
    _ ≤ 16 / 3 * x ^ 2 := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 1 / 8 - x)]
private theorem sum_Icc_one_sq_mul_pow_le_five_mul (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ 1 / 512) (N : ℕ) :
    ∑ δ ∈ Finset.Icc 1 N, (δ : ℝ) ^ 2 * y ^ δ ≤ 5 * y := by
  have h4y0 : 0 ≤ 4 * y := by linarith
  have h4y1 : 4 * y < 1 := by linarith
  calc ∑ δ ∈ Finset.Icc 1 N, (δ : ℝ) ^ 2 * y ^ δ ≤ ∑ δ ∈ Finset.Ico 1 (N + 1), (4 * y) ^ δ := by
        rw [show Finset.Icc 1 N = Finset.Ico 1 (N + 1) by
          ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
        apply Finset.sum_le_sum
        intro δ _
        rw [mul_pow]
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hy0 _)
        have h : δ ≤ 2 ^ δ := (Nat.lt_two_pow_self).le
        have h' : δ ^ 2 ≤ 4 ^ δ := by
          calc δ ^ 2 ≤ (2 ^ δ) ^ 2 := Nat.pow_le_pow_left h 2
            _ = 4 ^ δ := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        exact_mod_cast h'
    _ ≤ (4 * y) ^ 1 / (1 - 4 * y) := geom_sum_Ico_le_of_lt_one h4y0 h4y1
    _ ≤ 5 * y := by
        rw [pow_one, div_le_iff₀ (by linarith)]
        nlinarith [mul_nonneg hy0 (by linarith : (0 : ℝ) ≤ 1 - 20 * y)]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

set_option autoImplicit false
open Finset Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : LocalEstimateII := by
  unfold LocalEstimateII
  intro K L _ _ _ _ _ N hq
  classical
  have hq' : 4096 ≤ Fintype.card K := by norm_num at hq; exact hq
  have hQ : (4096 : ℝ) ≤ (Fintype.card K : ℝ) := by exact_mod_cast hq'
  have hQ0 : (0 : ℝ) ≤ (Fintype.card K : ℝ) := by linarith
  have hLQ : 0 ≤ Real.log (Fintype.card K : ℝ) := Real.log_nonneg (by linarith)
  have hμ : ∀ c, 0 ≤ e3μ K N c := e3μ_nonneg K N
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = (Fintype.card K : ℝ) ^ (4 : ℝ)⁻¹ := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have hs4 : s ^ 4 = (Fintype.card K : ℝ) := by
    rw [hsdef, show (4 : ℝ)⁻¹ = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_inv_natCast_pow hQ0 (by norm_num)
  have hs8 : 8 ≤ s := by
    by_contra h
    push_neg at h
    have h2 : s ^ 2 < 64 := by nlinarith
    have h4 : s ^ 4 < 4096 := by
      nlinarith [mul_pos (by linarith : (0 : ℝ) < 64 - s ^ 2) (by positivity : (0 : ℝ) < 64 + s ^ 2)]
    linarith
  have hsδ : ∀ δ : ℕ, 1 ≤ δ → 2 ≤ s ^ δ := fun δ hδ => by
    calc (2 : ℝ) ≤ s ^ 1 := by rw [pow_one]; linarith
      _ ≤ s ^ δ := pow_le_pow_right₀ (by linarith) hδ
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = s⁻¹ := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [hxdef]; exact inv_nonneg.2 hs0
  have hxs : x * s = 1 := by rw [hxdef, inv_mul_cancel₀ (ne_of_gt (by linarith))]
  have hx8 : x ≤ 1 / 8 := by nlinarith [mul_le_mul_of_nonneg_left hs8 hx0]
  have hx512 : x ^ 3 ≤ 1 / 512 := by
    calc x ^ 3 ≤ (1 / 8) ^ 3 := pow_le_pow_left₀ hx0 hx8 3
      _ = 1 / 512 := by norm_num
  have hpowA : ∀ δ : ℕ, (Fintype.card K : ℝ) ^ (3 * (δ : ℝ) / 4) = (s ^ δ) ^ 3 := fun δ => by
    rw [show 3 * (δ : ℝ) / 4 = (4 : ℝ)⁻¹ * ((3 * δ : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_mul hQ0, ← hsdef, Real.rpow_natCast]
    ring
  have hpowB : ∀ δ : ℕ, (Fintype.card K : ℝ) ^ ((δ : ℝ) / 4) = s ^ δ := fun δ => by
    rw [show (δ : ℝ) / 4 = (4 : ℝ)⁻¹ * ((δ : ℕ) : ℝ) by ring,
      Real.rpow_mul hQ0, ← hsdef, Real.rpow_natCast]
  have hpowQ : ∀ δ : ℕ, (Fintype.card K : ℝ) ^ δ = (s ^ δ) ^ 4 := fun δ => by
    rw [← hs4]; ring
  have hQδ : ∀ δ : ℕ, (1 : ℝ) ≤ (Fintype.card K : ℝ) ^ δ := fun δ => one_le_pow₀ (by linarith)
  have htA : ∀ δ : ℕ, 2 ≤ δ →
      (Fintype.card K : ℝ) ^ (3 * (δ : ℝ) / 4) * ((Fintype.card K : ℝ) ^ δ - 1)⁻¹ ≤ 2 * x ^ δ := fun δ hδ => by
    rw [hpowA δ, hpowQ δ]
    calc (s ^ δ) ^ 3 * ((s ^ δ) ^ 4 - 1)⁻¹ ≤ 2 * (1 / s ^ δ) := cube_div_fourth_sub_one_le (s ^ δ) (hsδ δ (by omega))
      _ = 2 * x ^ δ := by rw [hxdef]; ring
  have htB : ∀ δ : ℕ, 1 ≤ δ →
      (Fintype.card K : ℝ) ^ ((δ : ℝ) / 4) * ((Fintype.card K : ℝ) ^ δ - 1)⁻¹ ≤ 2 * (x ^ 3) ^ δ := fun δ hδ => by
    rw [hpowB δ, hpowQ δ]
    calc s ^ δ * ((s ^ δ) ^ 4 - 1)⁻¹ ≤ 2 * (1 / (s ^ δ) ^ 3) := div_fourth_sub_one_le (s ^ δ) (hsδ δ hδ)
      _ = 2 * (x ^ 3) ^ δ := by rw [hxdef]; ring
  have hfA0 : ∀ δ : ℕ, 0 ≤ (Fintype.card K : ℝ) ^ (3 * (δ : ℝ) / 4) * ((Fintype.card K : ℝ) ^ δ - 1)⁻¹ := fun δ =>
    mul_nonneg (by positivity) (inv_nonneg.2 (by linarith [hQδ δ]))
  have hfB0 : ∀ δ : ℕ, 0 ≤ (Fintype.card K : ℝ) ^ ((δ : ℝ) / 4) * ((Fintype.card K : ℝ) ^ δ - 1)⁻¹ := fun δ =>
    mul_nonneg (by positivity) (inv_nonneg.2 (by linarith [hQδ δ]))
  have hω : ∀ d : ℕ, ((Fintype.card K ^ d - 1).primeFactors.card : ℝ) ≤ 3 / 2 * d * Real.log (Fintype.card K : ℝ) := by
    intro d
    have hpos : 1 ≤ Fintype.card K ^ d := Nat.one_le_pow _ _ Fintype.card_pos
    have h1 : 2 ^ (Fintype.card K ^ d - 1).primeFactors.card ≤ Fintype.card K ^ d :=
      (two_pow_card_primeFactors_le_add_one _).trans (Nat.sub_add_cancel hpos).le
    have h2 : (2 : ℝ) ^ (Fintype.card K ^ d - 1).primeFactors.card ≤ (Fintype.card K : ℝ) ^ d := by
      exact_mod_cast h1
    have h3 := Real.log_le_log (by positivity) h2
    rw [Real.log_pow, Real.log_pow] at h3
    have hl2 := Real.log_two_gt_d9
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card K ^ d - 1).primeFactors.card)
      (by linarith : (0 : ℝ) ≤ Real.log 2 - 2 / 3)]
  refine le_trans (sum_le_wtOf_of_subset (e3μ K N) hμ _ (e3SA K L N ∪ e3SB K L N) ?_) ?_
  · intro c hc
    obtain ⟨hc1, l, hl, hlBB, hninj⟩ := Finset.mem_filter.1 hc
    exact square_set_mem_exceptional_union hc1 hl hlBB hninj
  refine (wtOf_union_le _ hμ _ _).trans ?_
  have hA : wtOf (e3μ K N) (e3SA K L N) ≤ 3 * Real.log (Fintype.card K : ℝ) * (16 / 3 * x ^ 2) := by
    unfold e3SA
    refine (wtOf_biUnion_le _ hμ _ _).trans ?_
    calc _ ≤ ∑ δ ∈ Finset.Icc 2 N, 3 * Real.log (Fintype.card K : ℝ) * ((δ : ℝ) * x ^ δ) := by
          apply Finset.sum_le_sum
          intro δ hδ
          have hδ2 := (Finset.mem_Icc.1 hδ).1
          refine (wtOf_biUnion_le _ hμ _ _).trans ?_
          calc _ ≤ ∑ l ∈ e3PA (Fintype.card K) δ,
                (Fintype.card K : ℝ) ^ (3 * (δ : ℝ) / 4) * ((Fintype.card K : ℝ) ^ δ - 1)⁻¹ := by
                apply Finset.sum_le_sum
                intro l hl
                rw [e3PA, Finset.mem_filter, Nat.mem_primeFactors] at hl
                exact wt_caseA K L N δ l hl.1.1 hδ2 hl.2
            _ = ((e3PA (Fintype.card K) δ).card : ℝ) *
                ((Fintype.card K : ℝ) ^ (3 * (δ : ℝ) / 4) * ((Fintype.card K : ℝ) ^ δ - 1)⁻¹) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (3 / 2 * δ * Real.log (Fintype.card K : ℝ)) * (2 * x ^ δ) := by
                apply mul_le_mul _ (htA δ hδ2) (hfA0 δ) (mul_nonneg (by positivity) hLQ)
                calc ((e3PA (Fintype.card K) δ).card : ℝ)
                    ≤ ((Fintype.card K ^ δ - 1).primeFactors.card : ℝ) := by
                      exact_mod_cast Finset.card_filter_le _ _
                  _ ≤ 3 / 2 * δ * Real.log (Fintype.card K : ℝ) := hω δ
            _ = 3 * Real.log (Fintype.card K : ℝ) * ((δ : ℝ) * x ^ δ) := by ring
      _ = 3 * Real.log (Fintype.card K : ℝ) * ∑ δ ∈ Finset.Icc 2 N, (δ : ℝ) * x ^ δ := by rw [Finset.mul_sum]
      _ ≤ 3 * Real.log (Fintype.card K : ℝ) * (16 / 3 * x ^ 2) :=
          mul_le_mul_of_nonneg_left (sum_Icc_two_mul_pow_le_sixteen_thirds_mul_sq x hx0 hx8 N) (mul_nonneg (by norm_num) hLQ)
  have hB : wtOf (e3μ K N) (e3SB K L N) ≤ 6 * Real.log (Fintype.card K : ℝ) * (5 * x ^ 3) := by
    unfold e3SB
    refine (wtOf_biUnion_le _ hμ _ _).trans ?_
    calc _ ≤ ∑ δ ∈ Finset.Icc 1 N, 6 * Real.log (Fintype.card K : ℝ) * ((δ : ℝ) ^ 2 * (x ^ 3) ^ δ) := by
          apply Finset.sum_le_sum
          intro δ hδ
          have hδ1 := (Finset.mem_Icc.1 hδ).1
          refine (wtOf_biUnion_le _ hμ _ _).trans ?_
          calc _ ≤ ∑ δ' ∈ Finset.Icc 1 δ, 6 * Real.log (Fintype.card K : ℝ) * ((δ : ℝ) * (x ^ 3) ^ δ) := by
                apply Finset.sum_le_sum
                intro δ' hδ'
                have hδ'1 := (Finset.mem_Icc.1 hδ').1
                have hδ'δ := (Finset.mem_Icc.1 hδ').2
                refine (wtOf_biUnion_le _ hμ _ _).trans ?_
                calc _ ≤ ∑ l ∈ e3PB (Fintype.card K) δ δ',
                      (Fintype.card K : ℝ) ^ ((δ : ℝ) / 4) * ((Fintype.card K : ℝ) ^ δ - 1)⁻¹ := by
                      apply Finset.sum_le_sum
                      intro l hl
                      rw [e3PB, Finset.mem_filter, Finset.mem_union, Nat.mem_primeFactors,
                        Nat.mem_primeFactors] at hl
                      have hlp : l.Prime := by
                        rcases hl.1 with h | h
                        · exact h.1
                        · exact h.1
                      exact wt_caseB K L N δ δ' l hlp hδ1 hδ'1 hl.2
                  _ = ((e3PB (Fintype.card K) δ δ').card : ℝ) *
                      ((Fintype.card K : ℝ) ^ ((δ : ℝ) / 4) * ((Fintype.card K : ℝ) ^ δ - 1)⁻¹) := by
                      rw [Finset.sum_const, nsmul_eq_mul]
                  _ ≤ (3 * δ * Real.log (Fintype.card K : ℝ)) * (2 * (x ^ 3) ^ δ) := by
                      apply mul_le_mul _ (htB δ hδ1) (hfB0 δ) (mul_nonneg (by positivity) hLQ)
                      calc ((e3PB (Fintype.card K) δ δ').card : ℝ)
                          ≤ ((Fintype.card K ^ δ - 1).primeFactors.card : ℝ) +
                            ((Fintype.card K ^ δ' - 1).primeFactors.card : ℝ) := by
                            exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_union_le _ _)
                        _ ≤ 3 / 2 * δ * Real.log (Fintype.card K : ℝ) + 3 / 2 * δ' * Real.log (Fintype.card K : ℝ) := add_le_add (hω δ) (hω δ')
                        _ ≤ 3 * δ * Real.log (Fintype.card K : ℝ) := by
                            have : (δ' : ℝ) ≤ δ := by exact_mod_cast hδ'δ
                            nlinarith [mul_nonneg (sub_nonneg.2 this) hLQ]
                  _ = 6 * Real.log (Fintype.card K : ℝ) * ((δ : ℝ) * (x ^ 3) ^ δ) := by ring
            _ = 6 * Real.log (Fintype.card K : ℝ) * ((δ : ℝ) ^ 2 * (x ^ 3) ^ δ) := by
                rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
                ring
      _ = 6 * Real.log (Fintype.card K : ℝ) * ∑ δ ∈ Finset.Icc 1 N, (δ : ℝ) ^ 2 * (x ^ 3) ^ δ := by rw [Finset.mul_sum]
      _ ≤ 6 * Real.log (Fintype.card K : ℝ) * (5 * x ^ 3) :=
          mul_le_mul_of_nonneg_left (sum_Icc_one_sq_mul_pow_le_five_mul (x ^ 3) (by positivity) hx512 N)
            (mul_nonneg (by norm_num) hLQ)
  have hsq : Real.sqrt (Fintype.card K : ℝ) = s ^ 2 := by
    rw [← hs4, show s ^ 4 = (s ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hx2 : x ^ 2 = 1 / s ^ 2 := by rw [hxdef, inv_pow, one_div]
  have hx3 : x ^ 3 ≤ x ^ 2 / 8 := by nlinarith [mul_le_mul_of_nonneg_left hx8 (sq_nonneg x)]
  rw [hsq]
  calc wtOf (e3μ K N) (e3SA K L N) + wtOf (e3μ K N) (e3SB K L N)
      ≤ 3 * Real.log (Fintype.card K : ℝ) * (16 / 3 * x ^ 2) + 6 * Real.log (Fintype.card K : ℝ) * (5 * x ^ 3) := add_le_add hA hB
    _ ≤ 23 * Real.log (Fintype.card K : ℝ) * x ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hx3 hLQ, mul_nonneg hLQ (sq_nonneg x)]
    _ = 23 * Real.log (Fintype.card K : ℝ) / s ^ 2 := by rw [hx2]; ring
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
