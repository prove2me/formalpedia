-- Prove2me | solution 1 for BwSC.LowerBound.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T03:07:33.262305+00:00
-- url     : https://prove2.me/submissions/bf720914-5731-4155-8de1-1a704a154069

import Mathlib
import Definitions.Def_BwSC_LowerBound_Proof
import Theorems.Thm_BanditAlgorithm_bandit_minimax_lower_bound
import Theorems.Thm_BwSC_LowerBound_p59_first_term
import Theorems.Thm_BwSC_LowerBound_p59_second_term
import Theorems.Thm_BwSC_LowerBound_lemma_9
import Theorems.Thm_BwSC_LowerBound_lemma_11
import Theorems.Thm_BwSC_LowerBound_eq_46
import Theorems.Thm_BwSC_LowerBound_eq_47
import Theorems.Thm_BwSC_LowerBound_theorem_2_first_term_q0

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace BwSC.LowerBound.MainAux

lemma cube_le (n : ℕ) : n ^ 3 ≤ 6 * 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n <;> norm_num
    · have h1 : (n + 1) ^ 3 ≤ 2 * n ^ 3 := by
        have h2 : 4 * n ≤ n * n := Nat.mul_le_mul_right n h
        have h3 : 4 * (n * n) ≤ n * (n * n) := Nat.mul_le_mul_right (n * n) h
        nlinarith
      calc (n + 1) ^ 3 ≤ 2 * n ^ 3 := h1
        _ ≤ 2 * (6 * 2 ^ n) := by omega
        _ = 6 * 2 ^ (n + 1) := by ring

lemma log_T_gt_one {T : ℕ} (hT : 4 ≤ T) : 1 < Real.log T := by
  have h4 : (4 : ℝ) ≤ T := by exact_mod_cast hT
  have : Real.log 4 ≤ Real.log T := Real.log_le_log (by norm_num) h4
  have h2 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_gt_d9
  linarith

lemma cube_le_log {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T)
    (hst : (qIdx S K : ℝ) + 2 ≤ Real.logb 2 (Real.logb 2 ((T : ℝ) / K))) :
    ((qIdx S K : ℝ) + 2) ^ 3 ≤ 9 * Real.log T := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have h2 : (2 : ℝ) ≤ (T : ℝ) / K := by
    rw [le_div_iff₀ hK0]; exact_mod_cast (by omega : 2 * K ≤ T)
  have hL : 1 ≤ Real.logb 2 ((T : ℝ) / K) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    simpa using h2
  have hpow : (2 : ℝ) ^ ((qIdx S K : ℝ) + 2) ≤ Real.logb 2 ((T : ℝ) / K) :=
    (Real.le_logb_iff_rpow_le (by norm_num) (by linarith)).mp hst
  have hTK : (T : ℝ) / K ≤ T := div_le_self hT0.le (by exact_mod_cast (by omega : 1 ≤ K))
  have hLT : Real.logb 2 ((T : ℝ) / K) ≤ Real.logb 2 T :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) hTK
  have hcast : (2 : ℝ) ^ ((qIdx S K : ℝ) + 2) = ((2 ^ (qIdx S K + 2) : ℕ) : ℝ) := by
    rw [show ((qIdx S K : ℝ) + 2) = ((qIdx S K + 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    push_cast; ring
  have hcube : (((qIdx S K + 2) ^ 3 : ℕ) : ℝ) ≤ ((6 * 2 ^ (qIdx S K + 2) : ℕ) : ℝ) := by
    exact_mod_cast cube_le (qIdx S K + 2)
  have hlog2 := Real.log_two_gt_d9
  have hlogb : Real.logb 2 T = Real.log T / Real.log 2 := rfl
  have key : ((2 ^ (qIdx S K + 2) : ℕ) : ℝ) * Real.log 2 ≤ Real.log T := by
    rw [← hcast]
    have := hpow.trans hLT
    rw [hlogb, le_div_iff₀ (by linarith)] at this
    exact this
  push_cast at hcube key ⊢
  have hP : (0 : ℝ) ≤ 2 ^ (qIdx S K + 2) := by positivity
  have : 6 * (2 : ℝ) ^ (qIdx S K + 2) ≤ 9 * ((2 : ℝ) ^ (qIdx S K + 2) * Real.log 2) := by nlinarith
  linarith

lemma exists_ge_avg {K : ℕ} (hK : 0 < K) (m : ℕ) (f : ℕ → Fin K → ℝ) (c : ℝ)
    (h : c ≤ 1 / (((m : ℝ) + 2) * K) * ∑ j ∈ Finset.Icc 1 (m + 2), ∑ k : Fin K, f j k) :
    ∃ j ∈ Finset.Icc 1 (m + 2), ∃ k : Fin K, c ≤ f j k := by
  by_contra hne
  push_neg at hne
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hpos : (0 : ℝ) < ((m : ℝ) + 2) * K := by positivity
  have hne' : (Finset.Icc 1 (m + 2)).Nonempty := ⟨1, by simp⟩
  haveI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  have hlt : ∑ j ∈ Finset.Icc 1 (m + 2), ∑ k : Fin K, f j k <
      ∑ j ∈ Finset.Icc 1 (m + 2), ∑ k : Fin K, c :=
    Finset.sum_lt_sum_of_nonempty hne' (fun j hj =>
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun k _ => hne j hj k))
  have hc : ∑ j ∈ Finset.Icc 1 (m + 2), ∑ k : Fin K, c = ((m : ℝ) + 2) * K * c := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.card_Icc, nsmul_eq_mul]
    push_cast; ring
  rw [hc] at hlt
  have : 1 / (((m : ℝ) + 2) * K) * ∑ j ∈ Finset.Icc 1 (m + 2), ∑ k : Fin K, f j k < c := by
    rw [one_div_mul_eq_div, div_lt_iff₀ hpos]; linarith
  linarith

lemma final_bound (C c X R n L : ℝ) (hC : C ≤ 1 / 1000) (hL : 0 < L) (hX : 0 ≤ X)
    (hn : 0 < n) (hcube : n ^ 3 ≤ 9 * L) (hc : (2 - Real.sqrt 2) / 32 ≤ c)
    (hR : c * X / n ^ 3 ≤ R) : C / L * X ≤ R := by
  have hs : Real.sqrt 2 < 1.5 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hc9 : 1 / 1000 ≤ c / 9 := by linarith
  have hc0 : 0 ≤ c := by linarith
  have e1 : C / L * X ≤ c / 9 / L * X := by
    apply mul_le_mul_of_nonneg_right _ hX
    exact div_le_div_of_nonneg_right (hC.trans hc9) hL.le
  have e2 : c / 9 / L * X = c * X / (9 * L) := by field_simp
  have e3 : c * X / (9 * L) ≤ c * X / n ^ 3 :=
    div_le_div_of_nonneg_left (mul_nonneg hc0 hX) (by positivity) hcube
  linarith

lemma Kr_pos {S K : ℕ} (hK : 1 < K) : (0 : ℝ) < (K : ℝ) - (rIdx S K : ℝ) := by
  have h : rIdx S K ≤ (K : ℤ) - 2 := by
    unfold rIdx qIdx
    by_cases hS : S = 0
    · subst hS; simp; omega
    · rw [if_neg hS]
      have hdm := Nat.div_add_mod (S - 1) (K - 1)
      have hlt := Nat.mod_lt (S - 1) (by omega : K - 1 > 0)
      have hS1 : ((S - 1 : ℕ) : ℤ) = (S : ℤ) - 1 := by omega
      have hK1 : ((K - 1 : ℕ) : ℤ) = (K : ℤ) - 1 := by omega
      have e : (S : ℤ) - 1 - (((S - 1) / (K - 1) : ℕ) : ℤ) * ((K : ℤ) - 1) =
          (((S - 1) % (K - 1) : ℕ) : ℤ) := by
        rw [← hS1, ← hK1]; push_cast; zify at hdm; linarith
      rw [e]
      zify at hlt; push_cast at hlt ⊢; omega
  have : (rIdx S K : ℝ) ≤ (K : ℝ) - 2 := by exact_mod_cast h
  linarith

lemma rateA_nonneg {K S T : ℕ} (hK : 1 < K) : 0 ≤ rateA K S T := by
  have := Kr_pos (S := S) hK
  unfold rateA; positivity

lemma rateB_nonneg {K S T : ℕ} : 0 ≤ rateB K S T := by
  unfold rateB; positivity

lemma Rbad2_eq {K S T : ℕ} (hK : 0 < K) :
    Rbad2 S K T = rateB K S T / (4 * ((qIdx S K : ℝ) + 2)) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  unfold Rbad2 rateB
  rw [Real.div_rpow (Nat.cast_nonneg T) hK0.le, Real.rpow_sub hK0, Real.rpow_one]
  have : (0 : ℝ) < (K : ℝ) ^ aExp (qIdx S K + 1) := by positivity
  field_simp

lemma Rbad_mul_eq {K S T : ℕ} (hK : 1 < K) :
    Rbad S K T * (((K : ℝ) - (rIdx S K : ℝ)) / (((qIdx S K : ℝ) + 2) ^ 2 * K)) =
      rateA K S T / (8 * ((qIdx S K : ℝ) + 2) ^ 3) := by
  have hm := Kr_pos (S := S) hK
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  set m : ℝ := (K : ℝ) - (rIdx S K : ℝ) with hmdef
  unfold Rbad rateA
  rw [← hmdef, Real.div_rpow (Nat.cast_nonneg T) hm.le, Real.rpow_sub hm,
    show (m : ℝ) ^ (2 : ℝ) = m ^ (2 : ℕ) by exact_mod_cast Real.rpow_natCast m 2]
  have : (0 : ℝ) < m ^ aExp (qIdx S K) := by positivity
  field_simp

end BwSC.LowerBound.MainAux

open BwSC.LowerBound BwSC.LowerBound.MainAux in
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (K S T : ℕ), 1 < K → 2 * K ≤ T →
      ∀ π : BanditPolicy K, IsSwitchPolicy S T π →
        ∃ μvec : Fin K → ℝ, (∀ i j, |μvec i - μvec j| ≤ 1) ∧
          C / Real.log T * max (rateA K S T) (rateB K S T) ≤
            banditRegret (gaussianBandit μvec) π T := by
  obtain ⟨C0, hC0, H0⟩ := theorem_2_first_term_q0
  refine ⟨min C0 (1 / 1000), lt_min hC0 (by norm_num), ?_⟩
  intro K S T hK hT π hπ
  have hCC0 : min C0 (1 / 1000) ≤ C0 := min_le_left _ _
  have hC1 : min C0 (1 / 1000) ≤ 1 / 1000 := min_le_right _ _
  have hCpos : 0 < min C0 (1 / 1000) := lt_min hC0 (by norm_num)
  have hlog : 1 < Real.log T := log_T_gt_one (by omega)
  have hlog0 : 0 < Real.log T := by linarith
  have hA0 := rateA_nonneg (S := S) (T := T) hK
  have hB0 := rateB_nonneg (K := K) (S := S) (T := T)
  have hn0 : (0 : ℝ) < (qIdx S K : ℝ) + 2 := by positivity
  have hs : Real.sqrt 2 < 1.5 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  by_cases hst : (qIdx S K : ℝ) + 2 ≤ Real.logb 2 (Real.logb 2 ((T : ℝ) / K))
  · have hcube := cube_le_log hK hT hst
    rcases le_total (rateA K S T) (rateB K S T) with hAB | hAB
    · -- second class of risky events
      rw [max_eq_right hAB]
      obtain ⟨_, hspread, havg⟩ := lemma_11 hK hT π hπ hst
      have h47 := eq_47 hK hT π hπ
      obtain ⟨j, hj, k, hjk⟩ := exists_ge_avg (by omega) (qIdx S K)
        (fun j k => banditRegret (gaussianBandit (envAlt2 S K T j k)) π T) _ havg
      refine ⟨envAlt2 S K T j k, hspread j hj k, ?_⟩
      refine final_bound _ ((2 - Real.sqrt 2) / 16) (rateB K S T) _ ((qIdx S K : ℝ) + 2) _
        hC1 hlog0 hB0 hn0 hcube (by linarith [Real.sqrt_nonneg 2]) (le_trans ?_ hjk)
      rw [Rbad2_eq (by omega)]
      have hR0 : 0 ≤ rateB K S T / (4 * ((qIdx S K : ℝ) + 2)) := by positivity
      calc (2 - Real.sqrt 2) / 16 * rateB K S T / ((qIdx S K : ℝ) + 2) ^ 3
          = rateB K S T / (4 * ((qIdx S K : ℝ) + 2)) *
              ((2 - Real.sqrt 2) / 4 * (1 / ((qIdx S K : ℝ) + 2) ^ 2)) := by
            field_simp; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h47 hR0
    · rw [max_eq_left hAB]
      by_cases hq : qIdx S K = 0
      · obtain ⟨μ, hμ, hreg⟩ := H0 K S T hK hT hq hst π hπ
        refine ⟨μ, hμ, le_trans ?_ hreg⟩
        apply mul_le_mul_of_nonneg_right _ hA0
        exact div_le_div_of_nonneg_right hCC0 hlog0.le
      · -- first class of risky events
        have hq1 : 1 ≤ qIdx S K := Nat.one_le_iff_ne_zero.mpr hq
        obtain ⟨_, hspread, havg⟩ := lemma_9 hK hT π hπ hq1 hst
        have h46 := eq_46 hK hT π hπ hq1
        obtain ⟨j, hj, k, hjk⟩ := exists_ge_avg (by omega) (qIdx S K)
          (fun j k => banditRegret (gaussianBandit (envAlt1 S K T j k)) π T) _ havg
        refine ⟨envAlt1 S K T j k, hspread j hj k, ?_⟩
        refine final_bound _ ((2 - Real.sqrt 2) / 32) (rateA K S T) _ ((qIdx S K : ℝ) + 2) _
          hC1 hlog0 hA0 hn0 hcube le_rfl (le_trans ?_ hjk)
        have hRb0 : 0 ≤ Rbad S K T := by
          have := Kr_pos (S := S) hK
          unfold Rbad; positivity
        have hmul := Rbad_mul_eq (S := S) (T := T) hK
        calc (2 - Real.sqrt 2) / 32 * rateA K S T / ((qIdx S K : ℝ) + 2) ^ 3
            = (2 - Real.sqrt 2) / 4 * (rateA K S T / (8 * ((qIdx S K : ℝ) + 2) ^ 3)) := by
              field_simp; ring
          _ = Rbad S K T * ((2 - Real.sqrt 2) / 4 *
                (((K : ℝ) - (rIdx S K : ℝ)) / (((qIdx S K : ℝ) + 2) ^ 2 * K))) := by
              rw [← hmul]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left h46 hRb0
  · -- the degenerate case: the classical minimax bound suffices
    push_neg at hst
    have hA := p59_first_term hK hT hst
    have hB := p59_second_term hK hT hst
    obtain ⟨μ, hμ01, hreg⟩ := bandit_minimax_lower_bound hK (by omega : K - 1 ≤ T) π
    refine ⟨μ, fun i j => ?_, le_trans ?_ hreg⟩
    · have h1 := hμ01 i; have h2 := hμ01 j
      rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · have hmax : max (rateA K S T) (rateB K S T) ≤ 9 * Real.sqrt ((K : ℝ) * T) :=
        max_le hA (hB.trans (by nlinarith [Real.sqrt_nonneg ((K : ℝ) * T)]))
      have hKT : Real.sqrt ((K : ℝ) * T) ≤ Real.sqrt 2 * Real.sqrt (((K : ℝ) - 1) * T) := by
        rw [← Real.sqrt_mul (by norm_num)]
        apply Real.sqrt_le_sqrt
        have : (2 : ℝ) ≤ K := by exact_mod_cast hK
        have : (0 : ℝ) ≤ T := Nat.cast_nonneg T
        nlinarith
      have hCL : min C0 (1 / 1000) / Real.log T ≤ 1 / 1000 := by
        rw [div_le_iff₀ hlog0]; nlinarith
      have hmax0 : 0 ≤ max (rateA K S T) (rateB K S T) := le_max_of_le_left hA0
      have hsq0 : 0 ≤ Real.sqrt (((K : ℝ) - 1) * T) := Real.sqrt_nonneg _
      calc min C0 (1 / 1000) / Real.log T * max (rateA K S T) (rateB K S T)
          ≤ 1 / 1000 * (9 * (Real.sqrt 2 * Real.sqrt (((K : ℝ) - 1) * T))) :=
            mul_le_mul hCL (hmax.trans (by linarith)) hmax0 (by norm_num)
        _ ≤ Real.sqrt (((K : ℝ) - 1) * T) / 27 := by nlinarith
