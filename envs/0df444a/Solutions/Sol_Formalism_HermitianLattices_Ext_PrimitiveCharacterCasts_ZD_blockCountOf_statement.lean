-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.blockCountOf_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:54:18.188446+00:00
-- url     : https://prove2.me/submissions/17e41e91-27a4-4bca-ae1b-8625d5137b4e

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZBlock
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_norm_cpow_neg_le_one__4b558658281b
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_conj_natCast_cpow_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
theorem _root_.solution : BlockCountOf := by
  intro hDual hPair C hC hL Q hQ Y N U J hU hJ hsmall T ρ hT
  have hU0 : (0 : ℝ) < U := Nat.cast_pos.mpr (by omega)
  have hJ0 : (0 : ℝ) < J := Nat.cast_pos.mpr (by omega)
  have hs0 : s0 = 1 - 1 / 400 := rfl
  have hQ0 : (0 : ℝ) < Q := by linarith
  set b : ℕ → ℂ := fun n => mco Y N n * (n : ℂ) ^ (-(s0 : ℂ)) with hb
  set v : PC → ℕ → ℂ := fun p n => cv p n * (n : ℂ) ^ (-(ρ p - (s0 : ℂ))) with hv
  set Δ : ℝ := (U : ℝ) + T.card * (8 * Q ^ 3) with hΔ
  have hΔ0 : 0 ≤ Δ := by positivity
  have hcv : ∀ p n, ‖cv p n‖ ≤ 1 := fun p n => DirichletCharacter.norm_le_one _ _
  have hmemn : ∀ n ∈ Ioc U (2 * U), 0 < n := fun n hn => by
    have := (Finset.mem_Ioc.mp hn).1
    omega
  have hrow : ∀ i ∈ T, ∑ j ∈ T, ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v j n)‖ ≤ Δ := by
    intro i hi
    rw [← Finset.add_sum_erase T _ hi]
    have hdiag : ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v i n)‖ ≤ U := by
      refine (norm_sum_le _ _).trans ?_
      have hone : ∀ n ∈ Ioc U (2 * U), ‖v i n * (starRingEnd ℂ) (v i n)‖ ≤ 1 := by
        intro n hn
        rw [norm_mul, RCLike.norm_conj]
        have h1 : ‖v i n‖ ≤ 1 := by
          simp only [hv]
          rw [norm_mul]
          have h2 : ‖(n : ℂ) ^ (-(ρ i - (s0 : ℂ)))‖ ≤ 1 := by
            refine norm_cpow_neg_le_one' (hmemn n hn) ?_
            simp only [Complex.sub_re, Complex.ofReal_re]
            linarith [(hT i hi).2.2.1]
          calc ‖cv i n‖ * ‖(n : ℂ) ^ (-(ρ i - (s0 : ℂ)))‖ ≤ 1 * 1 :=
                mul_le_mul (hcv i n) h2 (norm_nonneg _) zero_le_one
            _ = 1 := one_mul 1
        calc ‖v i n‖ * ‖v i n‖ ≤ 1 * 1 := mul_le_mul h1 h1 (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      calc ∑ n ∈ Ioc U (2 * U), ‖v i n * (starRingEnd ℂ) (v i n)‖ ≤ ∑ n ∈ Ioc U (2 * U), (1 : ℝ) :=
            Finset.sum_le_sum hone
        _ = U := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one, show 2 * U - U = U by omega]
    have hoff : ∀ j ∈ T.erase i,
        ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v j n)‖ ≤ 8 * Q ^ 3 := by
      intro j hj
      obtain ⟨hji, hjT⟩ := Finset.mem_erase.mp hj
      obtain ⟨hpi, hqi, hri1, hri2, himi, -⟩ := hT i hi
      obtain ⟨hpj, hqj, hrj1, hrj2, himj, -⟩ := hT j hjT
      set w : ℂ := (ρ i - (s0 : ℂ)) + (starRingEnd ℂ) (ρ j - (s0 : ℂ)) with hw
      have hsum : ∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v j n) =
          ∑ n ∈ Ioc U (2 * U), cv i n * (starRingEnd ℂ) (cv j n) * (n : ℂ) ^ (-w) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hmemn n hn).ne'
        simp only [hv, map_mul, conj_natCast_cpow_neg]
        rw [hw, show -((ρ i - (s0 : ℂ)) + (starRingEnd ℂ) (ρ j - (s0 : ℂ))) =
            -(ρ i - (s0 : ℂ)) + -(starRingEnd ℂ) (ρ j - (s0 : ℂ)) by ring, Complex.cpow_add _ _ hn0]
        ring
      have hwre : w.re = (ρ i).re - s0 + ((ρ j).re - s0) := by
        simp [hw, Complex.conj_re]
      have hwim : w.im = (ρ i).im - (ρ j).im := by
        simp [hw, Complex.conj_im]
        ring
      have hwpos : 0 < w.re := by rw [hwre]; linarith
      have hne : i ≠ j := fun h => hji h.symm
      rw [hsum]
      refine (hPair i j hpi hpj hne w hwpos U hU).trans ?_
      have hwn : ‖w‖ ≤ 1 + 2 * Q := by
        refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
        have hre : |w.re| ≤ 1 := by
          rw [abs_le, hwre]
          constructor <;> linarith
        have him : |w.im| ≤ 2 * Q := by
          rw [hwim]
          calc |(ρ i).im - (ρ j).im| ≤ |(ρ i).im| + |(ρ j).im| := abs_sub _ _
            _ ≤ 2 * Q := by linarith
        linarith
      have hqq : (((i.1 + 1) * (j.1 + 1) : ℕ) : ℝ) ≤ Q ^ 2 := by
        push_cast at hqi hqj ⊢
        rw [sq]
        exact mul_le_mul hqi hqj (by positivity) hQ0.le
      calc 2 * (((i.1 + 1) * (j.1 + 1) : ℕ) : ℝ) * (1 + ‖w‖) ≤ 2 * Q ^ 2 * (2 + 2 * Q) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hqq (by norm_num)) (by linarith)
              (by positivity) (by positivity)
        _ ≤ 8 * Q ^ 3 := by
          nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ Q by linarith) (sq_nonneg Q)]
    calc ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v i n)‖ +
          ∑ j ∈ T.erase i, ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v j n)‖
        ≤ U + (T.erase i).card * (8 * Q ^ 3) := by
          refine add_le_add hdiag ?_
          have := Finset.sum_le_card_nsmul _ _ _ hoff
          rwa [nsmul_eq_mul] at this
      _ ≤ Δ := by
          rw [hΔ]
          have hc : ((T.erase i).card : ℝ) ≤ T.card := by exact_mod_cast Finset.card_erase_le
          nlinarith [pow_pos hQ0 3]
  have hD := hDual PC ℕ T (Ioc U (2 * U)) b v Δ hΔ0 hrow
  have hblk : ∀ i ∈ T, ∑ n ∈ Ioc U (2 * U), b n * v i n = blk Y N U i (ρ i) := by
    intro i hi
    unfold blk
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hmemn n hn).ne'
    simp only [hb, hv]
    rw [show -ρ i = -(s0 : ℂ) + -(ρ i - (s0 : ℂ)) by ring, Complex.cpow_add _ _ hn0]
    ring
  have hbn : ∑ n ∈ Ioc U (2 * U), ‖b n‖ ^ 2 ≤ C * (U : ℝ) ^ (-(197 / 200 : ℝ)) := by
    refine le_trans (le_of_eq ?_) (hL Y N U hU)
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [hb]
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (hmemn n hn)]
    simp only [Complex.neg_re, Complex.ofReal_re]
  have hlow : (T.card : ℝ) * (1 / (2 * (J : ℝ))) ^ 2 ≤
      ∑ i ∈ T, ‖∑ n ∈ Ioc U (2 * U), b n * v i n‖ ^ 2 := by
    have := Finset.card_nsmul_le_sum T (fun i => ‖∑ n ∈ Ioc U (2 * U), b n * v i n‖ ^ 2)
      ((1 / (2 * (J : ℝ))) ^ 2) (fun i hi => by
        rw [hblk i hi]
        exact pow_le_pow_left₀ (by positivity) (hT i hi).2.2.2.2.2 2)
    rwa [nsmul_eq_mul] at this
  have hup := hD.trans (mul_le_mul_of_nonneg_right hbn hΔ0)
  have hUU : (U : ℝ) ^ (-(197 / 200 : ℝ)) * U = (U : ℝ) ^ (3 / 200 : ℝ) := by
    rw [← Real.rpow_add_one hU0.ne']
    norm_num
  have ht : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  have hsm : (T.card : ℝ) * (8 * Q ^ 3 * (C * (U : ℝ) ^ (-(197 / 200 : ℝ)))) ≤
      T.card * (1 / (8 * (J : ℝ) ^ 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ ht
    calc 8 * Q ^ 3 * (C * (U : ℝ) ^ (-(197 / 200 : ℝ))) = 8 * Q ^ 3 * C * (U : ℝ) ^ (-(197 / 200 : ℝ)) := by
          ring
      _ ≤ _ := hsmall
  have key : (T.card : ℝ) * (1 / (2 * (J : ℝ))) ^ 2 ≤
      C * (U : ℝ) ^ (3 / 200 : ℝ) + T.card * (1 / (8 * (J : ℝ) ^ 2)) := by
    calc _ ≤ _ := hlow.trans hup
      _ = C * ((U : ℝ) ^ (-(197 / 200 : ℝ)) * U) +
            T.card * (8 * Q ^ 3 * (C * (U : ℝ) ^ (-(197 / 200 : ℝ)))) := by
          rw [hΔ]
          ring
      _ ≤ _ := by
          rw [hUU]
          linarith [hsm]
  have e1 : (T.card : ℝ) * (1 / (2 * (J : ℝ))) ^ 2 = 2 * ((T.card : ℝ) / (8 * (J : ℝ) ^ 2)) := by
    field_simp
    ring
  have e2 : (T.card : ℝ) * (1 / (8 * (J : ℝ) ^ 2)) = (T.card : ℝ) / (8 * (J : ℝ) ^ 2) := by
    rw [mul_one_div]
  rw [e1, e2] at key
  have h3 : (T.card : ℝ) / (8 * (J : ℝ) ^ 2) ≤ C * (U : ℝ) ^ (3 / 200 : ℝ) := by linarith
  rw [div_le_iff₀ (by positivity)] at h3
  calc (T.card : ℝ) ≤ C * (U : ℝ) ^ (3 / 200 : ℝ) * (8 * (J : ℝ) ^ 2) := h3
    _ = 8 * (J : ℝ) ^ 2 * C * (U : ℝ) ^ (3 / 200 : ℝ) := by ring
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
