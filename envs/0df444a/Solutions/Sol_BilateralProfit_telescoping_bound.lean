-- Prove2me | solution 1 for BilateralProfit.telescoping_bound
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-13T16:43:24.409629+00:00
-- url     : https://prove2.me/submissions/8a05f69e-dded-4f70-9f6b-22421679664c

import Definitions.Def_BilateralProfit_SellerTree
import Definitions.Def_BilateralProfit_Analysis
import Definitions.Def_BilateralProfit_OneRound
import Theorems.Thm_SinkhornHall_lemma_1_1
import Mathlib.Data.List.MinMax
import Mathlib.Data.Real.Basic
import Mathlib
import Definitions.Def_BilateralProfit_Algorithm1
import Theorems.Thm_BilateralProfit_lemma_4_6

namespace BilateralProfit.TelescopingSubmissionTradeFacts

open MeasureTheory

variable {K : ℕ}

theorem coord_mem (hK : 0 < K) (i : Fin (K + 1)) :
    (i : ℝ) / K ∈ Set.Icc (0 : ℝ) 1 := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hi : (i : ℕ) ≤ K := by omega
  constructor
  · positivity
  · apply (div_le_one hKr).mpr
    exact_mod_cast hi

theorem pt_mem (hK : 0 < K) (x : Grid K) :
    pt K x ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
  ⟨coord_mem hK x.1, coord_mem hK x.2⟩

theorem spread_mem (hK : 0 < K) (a : Act K) :
    (pt K a.1).2 - (pt K a.1).1 ∈ Set.Icc (0 : ℝ) 1 := by
  have hleft := coord_mem hK a.1.1
  have hright := coord_mem hK a.1.2
  have horder : ((a.1.1 : ℕ) : ℝ) ≤ ((a.1.2 : ℕ) : ℝ) := by exact_mod_cast a.2
  have hdiv := div_le_div_of_nonneg_right horder (by positivity : (0 : ℝ) ≤ K)
  change ((a.1.2 : ℕ) : ℝ) / K - ((a.1.1 : ℕ) : ℝ) / K ∈ Set.Icc 0 1
  exact ⟨sub_nonneg.mpr hdiv, by linarith [hleft.1, hright.2]⟩

theorem tradeBit_nonneg (v a : ℝ × ℝ) : 0 ≤ tradeBit v a := by
  unfold tradeBit
  split_ifs <;> norm_num

theorem tradeBit_le_one (v a : ℝ × ℝ) : tradeBit v a ≤ 1 := by
  unfold tradeBit
  split_ifs <;> norm_num

theorem measurableSet_trades (a : ℝ × ℝ) : MeasurableSet {v | Trades v a} := by
  change MeasurableSet (Set.Iic a.1 ×ˢ Set.Ici a.2)
  exact measurableSet_Iic.prod measurableSet_Ici

theorem Ptrade_nonneg (μ : Measure (ℝ × ℝ)) (a : ℝ × ℝ) : 0 ≤ Ptrade μ a :=
  ENNReal.toReal_nonneg

theorem Ptrade_le_one (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] (a : ℝ × ℝ) :
    Ptrade μ a ≤ 1 := by
  change μ.real {v | Trades v a} ≤ 1
  exact measureReal_le_one

theorem P0_nonneg (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a : ℝ × ℝ) :
    0 ≤ P0 ρ a := by
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (hρ.1 x) (tradeBit_nonneg _ _))

theorem P0_le_one (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a : ℝ × ℝ) :
    P0 ρ a ≤ 1 := by
  calc
    P0 ρ a ≤ ∑ x, ρ x := Finset.sum_le_sum (fun x _ => by
      simpa using mul_le_mul_of_nonneg_left (tradeBit_le_one (pt K x.1) a) (hρ.1 x))
    _ = 1 := hρ.2

theorem valProfitPt_eq_spread_mul_P0 (ρ : Grid K × Act K → ℝ) (a : ℝ × ℝ) :
    valProfitPt ρ a = (a.2 - a.1) * P0 ρ a := by
  unfold valProfitPt profit P0
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem margLaw_apply (ρ : Grid K × Act K → ℝ) (s : Set (ℝ × ℝ)) :
    margLaw ρ s = ∑ x, ENNReal.ofReal (ρ x) * Measure.dirac (pt K x.1) s := by
  classical
  simp [margLaw, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]

theorem margLaw_univ (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) :
    margLaw ρ Set.univ = 1 := by
  rw [margLaw_apply]
  simp only [measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hρ.1 x), hρ.2]
  exact ENNReal.ofReal_one

theorem margLaw_isValLaw (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) :
    IsValLaw (margLaw ρ) := by
  refine ⟨⟨margLaw_univ ρ hρ⟩, ?_⟩
  rw [margLaw_apply]
  apply Finset.sum_eq_zero
  intro x _
  have hx : pt K x.1 ∉ (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)ᶜ :=
    fun h => h (pt_mem hK x.1)
  rw [Measure.dirac_apply, Set.indicator_of_notMem hx, mul_zero]

theorem Ptrade_margLaw_eq_P0 (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a : ℝ × ℝ) : Ptrade (margLaw ρ) a = P0 ρ a := by
  classical
  unfold Ptrade
  rw [margLaw_apply, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro x _
    by_cases h : Trades (pt K x.1) a
    · simp [tradeBit, h, ENNReal.toReal_ofReal (hρ.1 x)]
    · simp [tradeBit, h]
  · intro x _
    finiteness

theorem muP_margLaw_eq_valProfitPt (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a : ℝ × ℝ) : muP (margLaw ρ) a = valProfitPt ρ a := by
  rw [muP, Ptrade_margLaw_eq_P0 ρ hρ, valProfitPt_eq_spread_mul_P0]

theorem valProfit_nonneg (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a : Act K) : 0 ≤ valProfit ρ a := by
  rw [valProfit, valProfitPt_eq_spread_mul_P0]
  exact mul_nonneg (spread_mem hK a).1 (P0_nonneg ρ hρ _)

theorem valProfit_le_one (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a : Act K) : valProfit ρ a ≤ 1 := by
  rw [valProfit, valProfitPt_eq_spread_mul_P0]
  have hs := spread_mem hK a
  have hp0 := P0_nonneg ρ hρ (pt K a.1)
  have hp1 := P0_le_one ρ hρ (pt K a.1)
  calc
    _ ≤ 1 * P0 ρ (pt K a.1) := mul_le_mul_of_nonneg_right hs.2 hp0
    _ ≤ 1 := by simpa using hp1

theorem valProfit_le_optVal (ρ : Grid K × Act K → ℝ) (a : Act K) :
    valProfit ρ a ≤ optVal ρ :=
  le_ciSup (Finite.bddAbove_range (valProfit ρ)) a

theorem optVal_nonneg (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) :
    0 ≤ optVal ρ :=
  (valProfit_nonneg hK ρ hρ default).trans (valProfit_le_optVal ρ default)

theorem optVal_le_one (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) :
    optVal ρ ≤ 1 :=
  ciSup_le (valProfit_le_one hK ρ hρ)

theorem gapStar_nonneg (ρ : Grid K × Act K → ℝ) (a : Act K) :
    0 ≤ gapStar ρ a :=
  sub_nonneg.mpr (valProfit_le_optVal ρ a)

theorem gapStar_le_one (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a : Act K) : gapStar ρ a ≤ 1 := by
  change optVal ρ - valProfit ρ a ≤ 1
  linarith [optVal_le_one hK ρ hρ, valProfit_nonneg hK ρ hρ a]

end BilateralProfit.TelescopingSubmissionTradeFacts

namespace BilateralProfit.TelescopingSubmissionInformationTable

variable {K : ℕ}

theorem marg_nonneg (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a' : Act K) :
    0 ≤ margA ρ a' := Finset.sum_nonneg (fun v _ => hρ.1 (v, a'))

theorem joint_nonneg (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a a' : Act K) (z : Bool) : 0 ≤ jointP ρ a a' z := by
  classical
  unfold jointP
  apply Finset.sum_nonneg
  intro v _
  split_ifs <;> first | exact hρ.1 _ | exact le_rfl

theorem true_add_false (ρ : Grid K × Act K → ℝ) (a a' : Act K) :
    jointP ρ a a' true + jointP ρ a a' false = margA ρ a' := by
  classical
  unfold jointP margA
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : Trades (pt K v) (pt K a.1) <;> simp [hv]

theorem row_sum (ρ : Grid K × Act K → ℝ) (a a' : Act K) :
    ∑ z : Bool, jointP ρ a a' z = margA ρ a' := by
  simpa only [Fintype.sum_bool] using true_add_false ρ a a'

theorem marg_sum (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) :
    ∑ a', margA ρ a' = 1 := by
  unfold margA
  rw [Finset.sum_comm]
  simpa only [Fintype.sum_prod_type] using hρ.2

theorem joint_sum (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a : Act K) :
    ∑ a', ∑ z : Bool, jointP ρ a a' z = 1 := by
  simp_rw [row_sum]
  exact marg_sum ρ hρ

theorem z_nonneg (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a : Act K) (z : Bool) :
    0 ≤ zP ρ a z := Finset.sum_nonneg (fun a' _ => joint_nonneg ρ hρ a a' z)

theorem z_sum (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a : Act K) :
    ∑ z : Bool, zP ρ a z = 1 := by
  unfold zP
  rw [Finset.sum_comm]
  exact joint_sum ρ hρ a

theorem joint_le_marg (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a a' : Act K) (z : Bool) : jointP ρ a a' z ≤ margA ρ a' := by
  have h := true_add_false ρ a a'
  have ht := joint_nonneg ρ hρ a a' true
  have hf := joint_nonneg ρ hρ a a' false
  cases z <;> linarith

theorem joint_le_z (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a a' : Act K) (z : Bool) : jointP ρ a a' z ≤ zP ρ a z := by
  exact Finset.single_le_sum (fun b _ => joint_nonneg ρ hρ a b z) (Finset.mem_univ a')

theorem joint_zero_of_marg_zero (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a a' : Act K) (hm : margA ρ a' = 0) (z : Bool) : jointP ρ a a' z = 0 := by
  have hn := joint_nonneg ρ hρ a a' z
  have hl := joint_le_marg ρ hρ a a' z
  linarith

theorem joint_zero_of_z_zero (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a a' : Act K) (z : Bool) (hz : zP ρ a z = 0) : jointP ρ a a' z = 0 := by
  have hn := joint_nonneg ρ hρ a a' z
  have hl := joint_le_z ρ hρ a a' z
  linarith

theorem joint_pos_marg_pos (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a a' : Act K) (z : Bool) (hj : 0 < jointP ρ a a' z) : 0 < margA ρ a' :=
  hj.trans_le (joint_le_marg ρ hρ a a' z)

theorem joint_pos_z_pos (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a a' : Act K) (z : Bool) (hj : 0 < jointP ρ a a' z) : 0 < zP ρ a z :=
  hj.trans_le (joint_le_z ρ hρ a a' z)

theorem joint_true (ρ : Grid K × Act K → ℝ) (a a' : Act K) :
    jointP ρ a a' true = ∑ v, ρ (v, a') * tradeBit (pt K v) (pt K a.1) := by
  classical
  unfold jointP
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : Trades (pt K v) (pt K a.1) <;> simp [tradeBit, hv]

theorem z_true (ρ : Grid K × Act K → ℝ) (a : Act K) :
    zP ρ a true = P0 ρ (pt K a.1) := by
  unfold zP P0
  simp_rw [joint_true]
  rw [Finset.sum_comm]
  simp only [Fintype.sum_prod_type]

theorem z_false (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a : Act K) :
    zP ρ a false = 1 - P0 ρ (pt K a.1) := by
  have h := z_sum ρ hρ a
  simp only [Fintype.sum_bool, z_true] at h
  linarith

theorem cond_true (ρ : Grid K × Act K → ℝ) (a a' : Act K) :
    jointP ρ a a' true / margA ρ a' = Pcond ρ a' (pt K a.1) := by
  rw [joint_true]
  rfl

theorem cond_false (ρ : Grid K × Act K → ℝ) (a a' : Act K) (hm : margA ρ a' ≠ 0) :
    jointP ρ a a' false / margA ρ a' = 1 - Pcond ρ a' (pt K a.1) := by
  have h := true_add_false ρ a a'
  rw [← cond_true]
  apply (div_eq_iff hm).mpr
  field_simp
  linarith

theorem cond_nonneg (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a a' : Act K) :
    0 ≤ Pcond ρ a' (pt K a.1) := by
  rw [← cond_true]
  exact div_nonneg (joint_nonneg ρ hρ a a' true) (marg_nonneg ρ hρ a')

theorem cond_le_one (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a a' : Act K) :
    Pcond ρ a' (pt K a.1) ≤ 1 := by
  rw [← cond_true]
  by_cases hm : margA ρ a' = 0
  · simp [hm]
  · exact (div_le_one (lt_of_le_of_ne (marg_nonneg ρ hρ a') (Ne.symm hm))).mpr
      (joint_le_marg ρ hρ a a' true)

theorem p0_nonneg (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a : Act K) :
    0 ≤ P0 ρ (pt K a.1) := by rw [← z_true]; exact z_nonneg ρ hρ a true

theorem p0_le_one (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a : Act K) :
    P0 ρ (pt K a.1) ≤ 1 := by
  have h := z_nonneg ρ hρ a false
  rw [z_false ρ hρ a] at h
  linarith

theorem cond_zero_of_p0_zero (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a a' : Act K) (hp : P0 ρ (pt K a.1) = 0) : Pcond ρ a' (pt K a.1) = 0 := by
  rw [← cond_true, joint_zero_of_z_zero ρ hρ a a' true (by rw [z_true, hp]), zero_div]

theorem cond_one_of_p0_one (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a a' : Act K) (hm : margA ρ a' ≠ 0) (hp : P0 ρ (pt K a.1) = 1) :
    Pcond ρ a' (pt K a.1) = 1 := by
  have hz : zP ρ a false = 0 := by rw [z_false ρ hρ a, hp]; ring
  have hj := joint_zero_of_z_zero ρ hρ a a' false hz
  have hc := cond_false ρ a a' hm
  rw [hj, zero_div] at hc
  linarith

end BilateralProfit.TelescopingSubmissionInformationTable

namespace BilateralProfit.TelescopingSubmissionOneRoundMath

open MeasureTheory

theorem nA_ge_one (K : ℕ) : (1 : ℝ) ≤ nA K := by
  have h : 0 < Fintype.card (Act K) := Fintype.card_pos_iff.mpr inferInstance
  unfold nA
  exact_mod_cast (Nat.succ_le_iff.mpr h)

theorem nA_pos (K : ℕ) : 0 < nA K := lt_of_lt_of_le zero_lt_one (nA_ge_one K)

theorem nG_eq (K : ℕ) : nG K = ((K : ℝ) + 1) ^ 2 := by
  simp [nG, Grid, Fintype.card_prod, Fintype.card_fin, pow_two]

theorem beta_nonneg (K : ℕ) : 0 ≤ beta K := by unfold beta; positivity

theorem base_ge_one (K : ℕ) : (1 : ℝ) ≤ nA K * (1 + beta K * K) := by
  have hA := nA_ge_one K
  have hβ := beta_nonneg K
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  exact le_trans hA (le_mul_of_one_le_right (by positivity) (by nlinarith))

theorem base_pos (K : ℕ) : 0 < nA K * (1 + beta K * K) :=
  zero_lt_one.trans_le (base_ge_one K)

theorem floor_pos (K : ℕ) : 0 < wFloor K := one_div_pos.mpr (base_pos K)

theorem H_ge_one (K : ℕ) : (1 : ℝ) ≤ Hpar K := by
  have hlog := Real.log_nonneg (base_ge_one K)
  unfold Hpar
  have hβ := beta_nonneg K
  nlinarith

theorem H_pos (K : ℕ) : 0 < Hpar K := zero_lt_one.trans_le (H_ge_one K)

theorem eta_pos {K : ℕ} (hK : 0 < K) : 0 < eta K := by
  unfold eta
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hH := H_pos K
  positivity

theorem eta_times_H {K : ℕ} (hK : 0 < K) :
    eta K * Hpar K = 1 / (2 * K * Hpar K) := by
  unfold eta
  field_simp [(Nat.cast_pos.mpr hK : (0 : ℝ) < K).ne', (H_pos K).ne']

theorem eta_times_H_le_half {K : ℕ} (hK : 0 < K) : eta K * Hpar K ≤ 1 / 2 := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hH := H_ge_one K
  rw [eta_times_H hK]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * K * Hpar K) (by norm_num : (0 : ℝ) < 2)).mpr
  nlinarith

theorem log_size_pos {K : ℕ} (hK : 0 < K) : 0 < Real.log (nA K * nG K) := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hA := nA_ge_one K
  have hG : (4 : ℝ) ≤ nG K := by rw [nG_eq]; nlinarith
  apply Real.log_pos
  nlinarith

theorem J_pos {K : ℕ} (hK : 0 < K) : 0 < Jpar K := by
  unfold Jpar
  apply Nat.one_le_ceil_iff.mpr
  have hlog := log_size_pos hK
  have hH := H_pos K
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  positivity

theorem regret_budget {K : ℕ} (hK : 0 < K) :
    Real.log (nA K * nG K) / (eta K * Jpar K) + eta K * Hpar K ^ 2 ≤ 1 / K := by
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hH := H_pos K
  have hη := eta_pos hK
  have hJ : (0 : ℝ) < Jpar K := Nat.cast_pos.mpr (J_pos hK)
  have hηJ : 2 * K * Real.log (nA K * nG K) ≤ eta K * Jpar K := by
    calc
      _ = eta K * (4 * (K : ℝ) ^ 2 * Hpar K ^ 2 * Real.log (nA K * nG K)) := by
        unfold eta
        field_simp [hKr.ne', hH.ne']
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.le_ceil _) hη.le
  have hdiv : Real.log (nA K * nG K) / (eta K * Jpar K) ≤ 1 / (2 * K) := by
    apply (div_le_div_iff₀ (by positivity : 0 < eta K * Jpar K) (by positivity : (0 : ℝ) < 2 * K)).mpr
    nlinarith
  have hterm : eta K * Hpar K ^ 2 = 1 / (2 * K) := by
    unfold eta
    field_simp [hKr.ne', hH.ne']
  rw [hterm]
  calc
    Real.log (nA K * nG K) / (eta K * Jpar K) + 1 / (2 * K) ≤
        1 / (2 * (K : ℝ)) + 1 / (2 * (K : ℝ)) := by linarith
    _ = 1 / (K : ℝ) := by ring

end BilateralProfit.TelescopingSubmissionOneRoundMath

namespace BilateralProfit.TelescopingSubmissionOneRoundMath

variable {K : ℕ}

noncomputable def update (ρ : Grid K × Act K → ℝ) (a : Act K) (z : Bool) (a' : Act K) : ℝ :=
  (beta K * K * (jointP ρ a a' z / zP ρ a z) + 1 / nA K) / (1 + beta K * K)

noncomputable def proposal (ρ : Grid K × Act K → ℝ) (a : Act K) : Proposal K :=
  (a, update ρ a false, update ρ a true)

noncomputable def expectedScore (w : Act K → ℝ) (ρ : Grid K × Act K → ℝ) (P : Proposal K) : ℝ :=
  ∑ x, ρ x * hScore w P x.1 x.2

theorem uniform_sum (K : ℕ) : (∑ a' : Act K, 1 / nA K) = 1 := by
  rw [Finset.sum_const, nsmul_eq_mul]
  change nA K * (1 / nA K) = 1
  field_simp [(nA_pos K).ne']

theorem update_floor (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a a' : Act K) (z : Bool) :
    wFloor K ≤ update ρ a z a' := by
  have hn : 0 ≤ beta K * K * (jointP ρ a a' z / zP ρ a z) :=
    mul_nonneg (mul_nonneg (beta_nonneg K) (Nat.cast_nonneg K))
      (div_nonneg (TelescopingSubmissionInformationTable.joint_nonneg ρ hρ a a' z) (TelescopingSubmissionInformationTable.z_nonneg ρ hρ a z))
  have hd : 0 < 1 + beta K * K := by
    have := mul_nonneg (beta_nonneg K) (Nat.cast_nonneg K)
    linarith
  have h := div_le_div_of_nonneg_right (show 1 / nA K ≤
      beta K * K * (jointP ρ a a' z / zP ρ a z) + 1 / nA K by linarith) hd.le
  unfold update
  calc
    wFloor K = 1 / nA K / (1 + beta K * K) := by simp only [wFloor, div_div]
    _ ≤ _ := h

theorem trade_at_bottom_top (hK : 0 < K) (a : Act K) :
    Trades (pt K (0, Fin.last K)) (pt K a.1) := by
  have hKr : (K : ℝ) ≠ 0 := (Nat.cast_pos.mpr hK).ne'
  have hp := (TelescopingSubmissionTradeFacts.coord_mem hK a.1.1).1
  have hq := (TelescopingSubmissionTradeFacts.coord_mem hK a.1.2).2
  simpa [Trades, pt, hKr] using And.intro hp hq

theorem not_trade_at_top_bottom (hK : 0 < K) (a : Act K) :
    ¬Trades (pt K (Fin.last K, 0)) (pt K a.1) := by
  have hKr : (K : ℝ) ≠ 0 := (Nat.cast_pos.mpr hK).ne'
  intro ht
  have horder : ((a.1.1 : ℕ) : ℝ) / K ≤ ((a.1.2 : ℕ) : ℝ) / K :=
    div_le_div_of_nonneg_right (by exact_mod_cast a.2) (Nat.cast_nonneg K)
  simp only [Trades, pt, Fin.val_last, Fin.val_zero, Nat.cast_zero, zero_div, div_self hKr] at ht
  linarith

theorem joint_pos (hK : 0 < K) (ρ : Grid K × Act K → ℝ)
    (hρpos : ∀ x, 0 < ρ x) (a a' : Act K) (z : Bool) : 0 < jointP ρ a a' z := by
  classical
  have hnonneg (v : Grid K) :
      0 ≤ if (Trades (pt K v) (pt K a.1) ↔ z = true) then ρ (v, a') else 0 := by
    split_ifs <;> first | exact (hρpos _).le | exact le_rfl
  cases z with
  | false =>
      have hmem := Finset.single_le_sum (fun v _ => hnonneg v) (Finset.mem_univ (Fin.last K, 0))
      have htrade := not_trade_at_top_bottom hK a
      simp only [Bool.false_eq_true, iff_false, if_pos htrade] at hmem
      simpa only [jointP, Bool.false_eq_true, iff_false] using (hρpos ((Fin.last K, 0), a')).trans_le hmem
  | true =>
      have hmem := Finset.single_le_sum (fun v _ => hnonneg v) (Finset.mem_univ (0, Fin.last K))
      have htrade := trade_at_bottom_top hK a
      simp only [iff_true, if_pos htrade] at hmem
      simpa only [jointP, iff_true] using (hρpos ((0, Fin.last K), a')).trans_le hmem

theorem z_pos (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (hρpos : ∀ x, 0 < ρ x) (a : Act K) (z : Bool) : 0 < zP ρ a z :=
  (joint_pos hK ρ hρpos a default z).trans_le (TelescopingSubmissionInformationTable.joint_le_z ρ hρ a default z)

theorem marg_pos (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (hρpos : ∀ x, 0 < ρ x) (a' : Act K) : 0 < margA ρ a' :=
  (joint_pos hK ρ hρpos default a' true).trans_le (TelescopingSubmissionInformationTable.joint_le_marg ρ hρ default a' true)

theorem update_isDist (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (hρpos : ∀ x, 0 < ρ x) (a : Act K) (z : Bool) : IsDist (update ρ a z) := by
  have hz := z_pos hK ρ hρ hρpos a z
  constructor
  · intro a'
    exact (floor_pos K).le.trans (update_floor ρ hρ a a' z)
  · unfold update
    rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
    change (beta K * K * (zP ρ a z / zP ρ a z) + ∑ a' : Act K, 1 / nA K) /
      (1 + beta K * K) = 1
    rw [div_self hz.ne', mul_one, uniform_sum]
    have hd : 1 + beta K * K ≠ 0 := by
      have := mul_nonneg (beta_nonneg K) (Nat.cast_nonneg K)
      positivity
    simpa only [add_comm] using div_self hd

theorem dist_le_one {A : Type} [Fintype A] (w : A → ℝ) (hw : IsDist w) (a : A) : w a ≤ 1 :=
  (Finset.single_le_sum (fun i _ => hw.1 i) (Finset.mem_univ a)).trans_eq hw.2

theorem log_weight_bounds (w : Act K → ℝ) (hw : IsDist w) (hwf : ∀ a, wFloor K ≤ w a)
    (a : Act K) :
    -Real.log (nA K * (1 + beta K * K)) ≤ Real.log (w a) ∧ Real.log (w a) ≤ 0 := by
  have hwpos := (floor_pos K).trans_le (hwf a)
  constructor
  · have h := Real.log_le_log (floor_pos K) (hwf a)
    simpa only [wFloor, Real.log_div one_ne_zero (base_pos K).ne', Real.log_one, zero_sub] using h
  · simpa only [Real.log_one] using Real.log_le_log hwpos (dist_le_one w hw a)

theorem score_abs_le (hK : 0 < K) (w : Act K → ℝ) (hw : IsDist w)
    (hwf : ∀ a, wFloor K ≤ w a) (P : Proposal K)
    (hP₀ : IsDist P.2.1) (hP₁ : IsDist P.2.2)
    (hPf₀ : ∀ a, wFloor K ≤ P.2.1 a) (hPf₁ : ∀ a, wFloor K ≤ P.2.2 a)
    (v : Grid K) (a' : Act K) : |hScore w P v a'| ≤ Hpar K := by
  have hwpos := (floor_pos K).trans_le (hwf a')
  have hwlog := log_weight_bounds w hw hwf a'
  have hQ : IsDist (Qsel P v) ∧ (∀ a, wFloor K ≤ Qsel P v a) := by
    unfold Qsel
    split_ifs <;> exact ⟨by assumption, by assumption⟩
  have hQpos := (floor_pos K).trans_le (hQ.2 a')
  have hQlog := log_weight_bounds (Qsel P v) hQ.1 hQ.2 a'
  have hlogabs : |Real.log (Qsel P v a' / w a')| ≤ Real.log (nA K * (1 + beta K * K)) := by
    rw [Real.log_div hQpos.ne' hwpos.ne']
    apply abs_le.mpr
    constructor <;> linarith [hwlog.1, hwlog.2, hQlog.1, hQlog.2]
  have hp₁ := TelescopingSubmissionTradeFacts.spread_mem hK a'
  have hp₂ := TelescopingSubmissionTradeFacts.spread_mem hK P.1
  have profit_mem (a : Act K) : profit (pt K v) (pt K a.1) ∈ Set.Icc (0 : ℝ) 1 := by
    unfold profit tradeBit
    split_ifs <;> simpa using TelescopingSubmissionTradeFacts.spread_mem hK a
  have hprofit : |profit (pt K v) (pt K a'.1) - profit (pt K v) (pt K P.1.1)| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [(profit_mem a').1, (profit_mem a').2, (profit_mem P.1).1, (profit_mem P.1).2]
  unfold hScore Hpar
  calc
    _ ≤ |profit (pt K v) (pt K a'.1) - profit (pt K v) (pt K P.1.1)| +
        |beta K * Real.log (Qsel P v a' / w a')| := abs_sub _ _
    _ ≤ _ := by
      rw [abs_mul, abs_of_nonneg (beta_nonneg K)]
      exact add_le_add hprofit (mul_le_mul_of_nonneg_left hlogabs (beta_nonneg K))

end BilateralProfit.TelescopingSubmissionOneRoundMath

namespace BilateralProfit.TelescopingSubmissionOneRoundMath

variable {K : ℕ}

theorem feedback_sum (ρ : Grid K × Act K → ℝ) (a : Act K) (f : Bool → Act K → ℝ) :
    (∑ x, ρ x * (if Trades (pt K x.1) (pt K a.1) then f true x.2 else f false x.2)) =
      ∑ a', ∑ z : Bool, jointP ρ a a' z * f z a' := by
  classical
  have hrow (a' : Act K) :
      (∑ v : Grid K, ρ (v, a') * (if Trades (pt K v) (pt K a.1) then f true a' else f false a')) =
        ∑ z : Bool, jointP ρ a a' z * f z a' := by
    rw [Fintype.sum_bool]
    unfold jointP
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : Trades (pt K v) (pt K a.1) <;> simp [h]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  exact Finset.sum_congr rfl (fun a' _ => hrow a')

theorem expected_score_eq (w : Act K → ℝ) (ρ : Grid K × Act K → ℝ) (a : Act K) :
    expectedScore w ρ (proposal ρ a) = gap ρ a - beta K *
      ∑ a', ∑ z : Bool, jointP ρ a a' z * Real.log (update ρ a z a' / w a') := by
  classical
  have hpoint (x : Grid K × Act K) : ρ x * hScore w (proposal ρ a) x.1 x.2 =
      ρ x * (profit (pt K x.1) (pt K x.2.1) - profit (pt K x.1) (pt K a.1)) -
        beta K * (ρ x * (if Trades (pt K x.1) (pt K a.1) then
          Real.log (update ρ a true x.2 / w x.2) else Real.log (update ρ a false x.2 / w x.2))) := by
    unfold hScore proposal Qsel
    split_ifs <;> ring
  unfold expectedScore
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, feedback_sum ρ a (fun z a' => Real.log (update ρ a z a' / w a'))]
  rfl

theorem marginal_kl_nonneg (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (w : Act K → ℝ) (hw : IsDist w) (hwpos : ∀ a, 0 < w a) :
    0 ≤ ∑ a, margA ρ a * Real.log (margA ρ a / w a) := by
  have h := SinkhornHall.lemma_1_1 (margA ρ) w (TelescopingSubmissionInformationTable.marg_nonneg ρ hρ) hw.1
    ((TelescopingSubmissionInformationTable.marg_sum ρ hρ).trans hw.2.symm)
  have hnot : ¬∃ a, w a = 0 ∧ 0 < margA ρ a := by
    rintro ⟨a, ha, _⟩
    exact (hwpos a).ne' ha
  rw [SinkhornHall.klDiv, if_neg hnot, EReal.coe_le_coe_iff, TelescopingSubmissionInformationTable.marg_sum ρ hρ] at h
  exact (by positivity : (0 : ℝ) ≤ (∑ a, |margA ρ a - w a|) ^ 2 / (2 * 1)).trans h

noncomputable def mixFactor (K : ℕ) : ℝ := beta K * K / (1 + beta K * K)

theorem mixFactor_pos (hK : 0 < K) (hβ : 0 < beta K) : 0 < mixFactor K := by
  unfold mixFactor
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  positivity

theorem update_log_lower (hK : 0 < K) (hβ : 0 < beta K)
    (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (hρpos : ∀ x, 0 < ρ x)
    (w : Act K → ℝ) (hwpos : ∀ a, 0 < w a) (a a' : Act K) (z : Bool) :
    Real.log (jointP ρ a a' z / (margA ρ a' * zP ρ a z)) +
        Real.log (margA ρ a' / w a') + Real.log (mixFactor K) ≤
      Real.log (update ρ a z a' / w a') := by
  have hj := joint_pos hK ρ hρpos a a' z
  have hm := marg_pos hK ρ hρ hρpos a'
  have hz := z_pos hK ρ hρ hρpos a z
  have hMix := mixFactor_pos hK hβ
  have hw := hwpos a'
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hd : 0 < 1 + beta K * K := by positivity
  have hQ : mixFactor K * (jointP ρ a a' z / zP ρ a z) ≤ update ρ a z a' := by
    unfold mixFactor update
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hd.le
    have hA := nA_pos K
    have hnonneg : 0 ≤ 1 / nA K := by positivity
    linarith
  have hQratio := div_le_div_of_nonneg_right hQ hw.le
  have hratio : 0 < mixFactor K * (jointP ρ a a' z / zP ρ a z) / w a' := by positivity
  have hlog := Real.log_le_log hratio hQratio
  have hid : mixFactor K * (jointP ρ a a' z / zP ρ a z) / w a' =
      (jointP ρ a a' z / (margA ρ a' * zP ρ a z)) * (margA ρ a' / w a') * mixFactor K := by
    field_simp [hm.ne', hz.ne', hw.ne']
  have hI : 0 < jointP ρ a a' z / (margA ρ a' * zP ρ a z) := by positivity
  have hM : 0 < margA ρ a' / w a' := by positivity
  rw [hid, Real.log_mul (mul_ne_zero hI.ne' hM.ne') hMix.ne', Real.log_mul hI.ne' hM.ne'] at hlog
  exact hlog

theorem joint_weighted (ρ : Grid K × Act K → ℝ) (a : Act K) (g : Act K → ℝ) :
    (∑ a', ∑ z : Bool, jointP ρ a a' z * g a') = ∑ a', margA ρ a' * g a' := by
  apply Finset.sum_congr rfl
  intro a' _
  rw [← Finset.sum_mul, TelescopingSubmissionInformationTable.row_sum]

theorem joint_constant (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a : Act K) (c : ℝ) :
    (∑ a', ∑ z : Bool, jointP ρ a a' z * c) = c := by
  rw [joint_weighted, ← Finset.sum_mul, TelescopingSubmissionInformationTable.marg_sum ρ hρ, one_mul]

theorem expected_log_lower (hK : 0 < K) (hβ : 0 < beta K)
    (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (hρpos : ∀ x, 0 < ρ x)
    (w : Act K → ℝ) (hw : IsDist w) (hwpos : ∀ a, 0 < w a) (a : Act K) :
    info ρ a + Real.log (mixFactor K) ≤
      ∑ a', ∑ z : Bool, jointP ρ a a' z * Real.log (update ρ a z a' / w a') := by
  have hpoint := Finset.sum_le_sum (fun a' (_ : a' ∈ Finset.univ) =>
    Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (update_log_lower hK hβ ρ hρ hρpos w hwpos a a' z)
        (TelescopingSubmissionInformationTable.joint_nonneg ρ hρ a a' z)))
  have heq : (∑ a', ∑ z : Bool, jointP ρ a a' z *
      (Real.log (jointP ρ a a' z / (margA ρ a' * zP ρ a z)) +
        Real.log (margA ρ a' / w a') + Real.log (mixFactor K))) =
      info ρ a + (∑ a', margA ρ a' * Real.log (margA ρ a' / w a')) + Real.log (mixFactor K) := by
    simp only [mul_add, Finset.sum_add_distrib, joint_weighted, joint_constant ρ hρ a]
    rfl
  rw [heq] at hpoint
  have hkl := marginal_kl_nonneg ρ hρ w hw hwpos
  linarith

theorem smoothing_penalty (hK : 0 < K) (hβ : 0 < beta K) :
    -(1 / (K : ℝ)) ≤ beta K * Real.log (mixFactor K) := by
  have hMix := mixFactor_pos hK hβ
  have h := Real.one_sub_inv_le_log_of_pos hMix
  have hm := mul_le_mul_of_nonneg_left h hβ.le
  have hKr : (K : ℝ) ≠ 0 := (Nat.cast_pos.mpr hK).ne'
  have heq : beta K * (1 - (mixFactor K)⁻¹) = -(1 / (K : ℝ)) := by
    unfold mixFactor
    field_simp [hβ.ne', hKr]
    ring
  rw [heq] at hm
  exact hm

theorem candidate_expected_bound (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (hρpos : ∀ x, 0 < ρ x) (w : Act K → ℝ) (hw : IsDist w)
    (hwf : ∀ a, wFloor K ≤ w a) (a : Act K) :
    expectedScore w ρ (proposal ρ a) ≤ gap ρ a - beta K * info ρ a + 1 / K := by
  rw [expected_score_eq]
  by_cases hβ0 : beta K = 0
  · simp only [hβ0, zero_mul, sub_zero]
    exact le_add_of_nonneg_right (by positivity)
  · have hβ : 0 < beta K := lt_of_le_of_ne (beta_nonneg K) (Ne.symm hβ0)
    have hlog := expected_log_lower hK hβ ρ hρ hρpos w hw
      (fun a => (floor_pos K).trans_le (hwf a)) a
    have hmul := mul_le_mul_of_nonneg_left hlog hβ.le
    have hpen := smoothing_penalty hK hβ
    nlinarith

end BilateralProfit.TelescopingSubmissionOneRoundMath

namespace BilateralProfit.TelescopingSubmissionProgramFacts

open CapacitatedAssort.General

variable {α β : Type}

/-- The returned value is independent of the initial operation counter. -/
def Value (m : Work α) (v : α) : Prop := ∀ s, (m.run s).1 = v

theorem value_pure (v : α) : Value (pure v : Work α) v := by
  intro s
  rfl

theorem value_charge (n : ℕ) : Value (charge n) () := by
  intro s
  rfl

theorem value_bind {m : Work α} {v : α} {f : α → Work β} {w : β}
    (hm : Value m v) (hf : Value (f v) w) : Value (m >>= f) w := by
  intro s
  change ((f (m.run s).1).run (m.run s).2).1 = w
  rw [hm s]
  exact hf _

/-- A list loop with deterministic yield values has the corresponding pure fold value. -/
theorem forIn_value (l : List α) (f : α → β → Work (ForInStep β))
    (g : α → β → β)
    (hf : ∀ x ∈ l, ∀ b, Value (f x b) (.yield (g x b))) (b : β) :
    Value (forIn l b f) (l.foldl (fun b x => g x b) b) := by
  induction l generalizing b with
  | nil =>
      intro s
      rfl
  | cons x l ih =>
      rw [List.forIn_cons]
      intro s
      change ((match (f x b).run s |>.1 with
        | .done b => pure b
        | .yield b => forIn l b f).run ((f x b).run s).2).1 = _
      rw [hf x (by simp) b s]
      exact ih (fun y hy => hf y (by simp [hy])) (g x b) _

theorem foldl_add_value (l : List α) (v : α → ℝ) (s : ℝ) :
    l.foldl (fun s x => s + v x) s = s + (l.map v).sum := by
  induction l generalizing s with
  | nil => simp
  | cons x l ih => simp [ih, add_assoc]

theorem sumW_value (l : List α) (f : α → Work ℝ) (v : α → ℝ)
    (hf : ∀ x ∈ l, Value (f x) (v x)) : Value (sumW l f) ((l.map v).sum) := by
  unfold sumW
  apply value_bind (value_charge 1)
  change Value (forIn l (0 : ℝ) (fun x s => do
    charge 2
    let y ← f x
    pure (ForInStep.yield (s + y)))) _
  have h := forIn_value l (fun x s => do
      charge 2
      let y ← f x
      pure (ForInStep.yield (s + y))) (fun x s => s + v x) (by
    intro x hx s
    apply value_bind (value_charge 2)
    exact value_bind (hf x hx) (value_pure _)) 0
  simpa only [foldl_add_value, zero_add] using h

theorem lookup_foldl_cons [DecidableEq α] (l : List α) (v : α → ℝ)
    (acc : List (α × ℝ)) (x : α) :
    (l.foldl (fun acc y => (y, v y) :: acc) acc).lookup x =
      if x ∈ l then some (v x) else acc.lookup x := by
  induction l generalizing acc with
  | nil => simp
  | cons y l ih =>
      rw [List.foldl_cons, ih]
      by_cases hx : x ∈ l
      · simp [hx]
      · by_cases hxy : y = x
        · subst y
          simp [hx]
        · have hbeq : (x == y) = false := beq_eq_false_iff_ne.mpr (Ne.symm hxy)
          simp [hx, hxy, Ne.symm hxy, List.lookup_cons, hbeq]

theorem tab_value [DecidableEq α] (l : List α) (f : α → Work ℝ) (v : α → ℝ)
    (hf : ∀ x ∈ l, Value (f x) (v x)) :
    Value (tab l f) (fun x => if x ∈ l then v x else 0) := by
  unfold tab
  apply value_bind (value_charge 1)
  have h := forIn_value l (fun x acc => do
      charge 2
      let y ← f x
      pure (ForInStep.yield ((x, y) :: acc)))
    (fun x acc => (x, v x) :: acc) (by
      intro x hx acc
      apply value_bind (value_charge 2)
      exact value_bind (hf x hx) (value_pure _)) []
  have hh := value_bind (f := fun acc : List (α × ℝ) =>
    pure (fun x => (acc.lookup x).getD 0)) h (value_pure _)
  convert hh using 1
  funext x
  rw [lookup_foldl_cons l v [] x]
  split_ifs <;> rfl

theorem tab_value_total [DecidableEq α] (l : List α) (hl : ∀ x, x ∈ l)
    (f : α → Work ℝ) (v : α → ℝ) (hf : ∀ x ∈ l, Value (f x) (v x)) :
    Value (tab l f) v := by
  simpa only [if_pos (hl _)] using tab_value l f v hf

theorem mem_gridList (K : ℕ) (x : Grid K) : x ∈ gridList K := by
  rcases x with ⟨i,j⟩
  simp [gridList]

theorem mem_actList (K : ℕ) (a : Act K) : a ∈ actList K := by
  classical
  simp only [actList, List.mem_filterMap]
  refine ⟨a.1, mem_gridList K a.1, ?_⟩
  simp [a.2]

theorem mem_tableList (K : ℕ) (x : Grid K × Act K) : x ∈ tableList K := by
  simp only [tableList, List.mem_flatMap, List.mem_map]
  exact ⟨x.1, mem_gridList K x.1, x.2, mem_actList K x.2, rfl⟩

theorem nodup_gridList (K : ℕ) : (gridList K).Nodup := by
  change ((List.finRange (K + 1)).product (List.finRange (K + 1))).Nodup
  exact (List.nodup_finRange _).product (List.nodup_finRange _)

theorem nodup_actList (K : ℕ) : (actList K).Nodup := by
  classical
  apply List.Nodup.filterMap ?_ (nodup_gridList K)
  intro x y a hx hy
  split_ifs at hx with hp
  · split_ifs at hy with hq
    · simp only [Option.mem_def, Option.some.injEq] at hx hy
      exact congrArg Subtype.val (hx.trans hy.symm)
    · simp at hy
  · simp at hx

theorem nodup_tableList (K : ℕ) : (tableList K).Nodup := by
  change ((gridList K).product (actList K)).Nodup
  exact (nodup_gridList K).product (nodup_actList K)

theorem sum_list_total [Fintype α] [DecidableEq α] (l : List α)
    (hn : l.Nodup) (hc : ∀ x, x ∈ l) (v : α → ℝ) :
    (l.map v).sum = ∑ x, v x := by
  have hset : l.toFinset = Finset.univ := by
    ext x
    simp [hc x]
  have h := List.sum_toFinset v hn
  rw [hset] at h
  exact h.symm

theorem sum_gridList (K : ℕ) (v : Grid K → ℝ) :
    ((gridList K).map v).sum = ∑ x, v x :=
  sum_list_total _ (nodup_gridList K) (mem_gridList K) v

theorem sum_actList (K : ℕ) (v : Act K → ℝ) :
    ((actList K).map v).sum = ∑ x, v x :=
  sum_list_total _ (nodup_actList K) (mem_actList K) v

theorem sum_tableList (K : ℕ) (v : Grid K × Act K → ℝ) :
    ((tableList K).map v).sum = ∑ x, v x :=
  sum_list_total _ (nodup_tableList K) (mem_tableList K) v

end BilateralProfit.TelescopingSubmissionProgramFacts

namespace BilateralProfit.TelescopingSubmissionSelectionFacts

noncomputable def pick {β : Type} (candidate : β × ℝ)
    (best : Option (β × ℝ)) : Option (β × ℝ) :=
  match best with
  | none => some candidate
  | some old => if candidate.2 < old.2 then some candidate else some old

lemma fold_pick_eq_argmin {α β : Type} (c : α → β × ℝ) (l : List α) :
    l.foldl (fun best x => pick (c x) best) none = (l.map c).argmin Prod.snd := by
  rw [List.argmin, List.foldl_map]
  congr 1
  funext best x
  cases best <;> rfl

lemma fold_pick_min {α β : Type} (c : α → β × ℝ) (l : List α) (hl : l ≠ []) :
    ∃ a ∈ l,
      l.foldl (fun best x => pick (c x) best) none = some (c a) ∧
        ∀ b ∈ l, (c a).2 ≤ (c b).2 := by
  classical
  have hne : (l.map c).argmin Prod.snd ≠ none := by
    intro h
    have hnil : l.map c = [] := List.argmin_eq_none.mp h
    exact hl (List.map_eq_nil_iff.mp hnil)
  rcases harg : (l.map c).argmin Prod.snd with _ | chosen
  · exact (hne harg).elim
  have hmem : chosen ∈ l.map c := List.argmin_mem harg
  obtain ⟨a, ha, hac⟩ := List.mem_map.mp hmem
  refine ⟨a, ha, ?_, ?_⟩
  · rw [fold_pick_eq_argmin, harg, hac]
  · intro b hb
    have hcb : c b ∈ l.map c := List.mem_map.mpr ⟨b, hb, rfl⟩
    simpa [hac] using List.le_of_mem_argmin hcb harg

lemma fold_pick_getD_min {α β : Type} (c : α → β × ℝ) (l : List α) (hl : l ≠ [])
    (fallback : β × ℝ) :
    ∃ a ∈ l,
      (l.foldl (fun best x => pick (c x) best) none).getD fallback = c a ∧
        ∀ b ∈ l, (c a).2 ≤ (c b).2 := by
  obtain ⟨a, ha, hfold, hmin⟩ := fold_pick_min c l hl
  exact ⟨a, ha, by rw [hfold]; rfl, hmin⟩

end BilateralProfit.TelescopingSubmissionSelectionFacts

namespace BilateralProfit.TelescopingSubmissionOneRoundMath

open TelescopingSubmissionProgramFacts CapacitatedAssort.General

variable {K : ℕ}

theorem candidate_value (w : Act K → ℝ) (ρ : Grid K × Act K → ℝ) (a : Act K) :
    Value (candidate K w ρ a) (update ρ a false, update ρ a true,
      expectedScore w ρ (proposal ρ a)) := by
  classical
  have hj (z : Bool) (a' : Act K) :
      (∑ v : Grid K, ρ (v,a') * (if z then tradeBit (pt K v) (pt K a.1)
        else 1 - tradeBit (pt K v) (pt K a.1))) = jointP ρ a a' z := by
    apply Finset.sum_congr rfl
    intro v _
    cases z <;> by_cases h : Trades (pt K v) (pt K a.1) <;> simp [tradeBit, jointP, h]
  have ht1 : Value (tab (actList K) fun a' => sumW (gridList K) fun v => do
      charge 6; pure (ρ (v,a') * tradeBit (pt K v) (pt K a.1))) (fun a' => jointP ρ a a' true) := by
    apply tab_value_total _ (mem_actList K)
    intro a' _
    have h := sumW_value (gridList K) (fun v => do charge 6; pure (ρ (v,a') * tradeBit (pt K v) (pt K a.1))) (fun v => ρ (v,a') * tradeBit (pt K v) (pt K a.1))
      (fun v _ => value_bind (value_charge 6) (value_pure _))
    simpa only [sum_gridList, ← hj true a', ↓reduceIte] using h
  have ht0 : Value (tab (actList K) fun a' => sumW (gridList K) fun v => do
      charge 7; pure (ρ (v,a') * (1 - tradeBit (pt K v) (pt K a.1)))) (fun a' => jointP ρ a a' false) := by
    apply tab_value_total _ (mem_actList K)
    intro a' _
    have h := sumW_value (gridList K) (fun v => do charge 7; pure (ρ (v,a') * (1-tradeBit (pt K v) (pt K a.1)))) (fun v => ρ (v,a') * (1-tradeBit (pt K v) (pt K a.1)))
      (fun v _ => value_bind (value_charge 7) (value_pure _))
    simpa only [sum_gridList, ← hj false a', Bool.false_eq_true, ↓reduceIte] using h
  unfold candidate
  apply value_bind ht1
  apply value_bind ht0
  apply value_bind (show Value (sumW (actList K) fun a' => do
      charge 1; pure (jointP ρ a a' true)) (zP ρ a true) from by
    simpa only [sum_actList, zP] using sumW_value (actList K) _ (fun a' => jointP ρ a a' true)
      (fun a' _ => value_bind (value_charge 1) (value_pure _)))
  apply value_bind (show Value (sumW (actList K) fun a' => do
      charge 1; pure (jointP ρ a a' false)) (zP ρ a false) from by
    simpa only [sum_actList, zP] using sumW_value (actList K) _ (fun a' => jointP ρ a a' false)
      (fun a' _ => value_bind (value_charge 1) (value_pure _)))
  apply value_bind (tab_value_total (actList K) (mem_actList K) _ (update ρ a true)
    (fun a' _ => value_bind (value_charge 9) (value_pure _)))
  apply value_bind (tab_value_total (actList K) (mem_actList K) _ (update ρ a false)
    (fun a' _ => value_bind (value_charge 9) (value_pure _)))
  apply value_bind (show Value (sumW (tableList K) fun x => do
      charge 20; pure (ρ x * hScore w (proposal ρ a) x.1 x.2))
      (expectedScore w ρ (proposal ρ a)) from by
    simpa only [sum_tableList, expectedScore] using sumW_value (tableList K) _
      (fun x => ρ x * hScore w (proposal ρ a) x.1 x.2)
      (fun x _ => value_bind (value_charge 20) (value_pure _)))
  exact value_pure _

noncomputable def selected (w : Act K → ℝ) (ρ : Grid K × Act K → ℝ) : Proposal K × ℝ :=
  ((actList K).foldl (fun best a => TelescopingSubmissionSelectionFacts.pick
    (proposal ρ a, expectedScore w ρ (proposal ρ a)) best) none).getD (default,0)

noncomputable def nextTable (w : Act K → ℝ) (ρ : Grid K × Act K → ℝ) : Grid K × Act K → ℝ :=
  fun x => ρ x * (1 + eta K * hScore w (selected w ρ).1 x.1 x.2) / (1+eta K*(selected w ρ).2)

theorem oneStep_value (w : Act K → ℝ) (ρ : Grid K × Act K → ℝ) :
    Value (oneStep K w ρ) ((selected w ρ).1, nextTable w ρ) := by
  classical
  unfold oneStep
  have hloop := forIn_value (actList K) (fun a best => do
      charge 1
      let (Q0,Q1,sc) ← candidate K w ρ a
      match best with
      | none => pure (.yield (some ((a,Q0,Q1),sc)))
      | some (_,bsc) => do
        charge 1
        if sc < bsc then pure (.yield (some ((a,Q0,Q1),sc)))
        else pure (.yield best))
    (fun a best => TelescopingSubmissionSelectionFacts.pick (proposal ρ a, expectedScore w ρ (proposal ρ a)) best) (by
      intro a ha best
      apply value_bind (value_charge 1)
      apply value_bind (candidate_value w ρ a)
      cases best with
      | none => exact value_pure _
      | some b =>
        apply value_bind (value_charge 1)
        by_cases h : expectedScore w ρ (proposal ρ a) < b.2
        · simp only [h, ↓reduceIte, TelescopingSubmissionSelectionFacts.pick]
          exact value_pure _
        · simp only [h, ↓reduceIte, TelescopingSubmissionSelectionFacts.pick]
          exact value_pure _) none
  apply value_bind hloop
  apply value_bind (value_charge 1)
  apply value_bind (tab_value_total (tableList K) (mem_tableList K) _ (nextTable w ρ)
    (fun x _ => value_bind (value_charge 22) (value_pure _)))
  exact value_pure _

theorem selected_spec (w : Act K → ℝ) (ρ : Grid K × Act K → ℝ) :
    ∃ a : Act K, selected w ρ = (proposal ρ a, expectedScore w ρ (proposal ρ a)) ∧
      ∀ b : Act K, (selected w ρ).2 ≤ expectedScore w ρ (proposal ρ b) := by
  have hl : actList K ≠ [] := by
    have h := mem_actList K (default : Act K)
    intro he
    simpa only [he, List.not_mem_nil] using h
  obtain ⟨a, ha, he, hmin⟩ := TelescopingSubmissionSelectionFacts.fold_pick_getD_min
    (fun a => (proposal ρ a, expectedScore w ρ (proposal ρ a))) (actList K) hl (default,0)
  refine ⟨a, he, ?_⟩
  intro b
  unfold selected
  rw [he]
  exact hmin b (mem_actList K b)

end BilateralProfit.TelescopingSubmissionOneRoundMath

namespace BilateralProfit.TelescopingSubmissionOneRoundMath

open TelescopingSubmissionProgramFacts CapacitatedAssort.General

variable {K : ℕ}

theorem selected_updates (hK : 0<K) (w : Act K → ℝ) (ρ : Grid K × Act K → ℝ)
    (hρ : IsDist ρ) (hp : ∀ x, 0<ρ x) :
    IsDist (selected w ρ).1.2.1 ∧ IsDist (selected w ρ).1.2.2 ∧
      (∀ a, wFloor K ≤ (selected w ρ).1.2.1 a) ∧
      (∀ a, wFloor K ≤ (selected w ρ).1.2.2 a) := by
  obtain ⟨a, ha, _⟩ := selected_spec w ρ
  rw [ha]
  exact ⟨update_isDist hK ρ hρ hp a false, update_isDist hK ρ hρ hp a true,
    fun a' => update_floor ρ hρ a a' false, fun a' => update_floor ρ hρ a a' true⟩

theorem selected_score (w : Act K → ℝ) (ρ : Grid K × Act K → ℝ) :
    (selected w ρ).2 = expectedScore w ρ (selected w ρ).1 := by
  obtain ⟨a, ha, _⟩ := selected_spec w ρ
  rw [ha]

theorem selected_score_abs (hK : 0<K) (w : Act K → ℝ) (hw : IsDist w)
    (hwf : ∀ a, wFloor K ≤ w a) (ρ : Grid K × Act K → ℝ)
    (hρ : IsDist ρ) (hp : ∀ x, 0<ρ x) (x : Grid K × Act K) :
    |hScore w (selected w ρ).1 x.1 x.2| ≤ Hpar K := by
  obtain ⟨h0,h1,hf0,hf1⟩ := selected_updates hK w ρ hρ hp
  exact score_abs_le hK w hw hwf _ h0 h1 hf0 hf1 _ _

theorem selected_mean_abs (hK : 0<K) (w : Act K → ℝ) (hw : IsDist w)
    (hwf : ∀ a, wFloor K ≤ w a) (ρ : Grid K × Act K → ℝ)
    (hρ : IsDist ρ) (hp : ∀ x, 0<ρ x) : |(selected w ρ).2| ≤ Hpar K := by
  rw [selected_score, expectedScore]
  calc
    _ ≤ ∑ x, |ρ x * hScore w (selected w ρ).1 x.1 x.2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, ρ x * Hpar K := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul, abs_of_nonneg (hρ.1 x)]
      exact mul_le_mul_of_nonneg_left (selected_score_abs hK w hw hwf ρ hρ hp x) (hρ.1 x)
    _ = _ := by rw [← Finset.sum_mul, hρ.2, one_mul]

theorem nextTable_invariant (hK : 0<K) (w : Act K → ℝ) (hw : IsDist w)
    (hwf : ∀ a, wFloor K ≤ w a) (ρ : Grid K × Act K → ℝ)
    (hρ : IsDist ρ) (hp : ∀ x, 0<ρ x) :
    IsDist (nextTable w ρ) ∧ ∀ x, 0<nextTable w ρ x := by
  have hη := eta_pos hK
  have hηH := eta_times_H_le_half hK
  have hnum (x : Grid K × Act K) : 0 < 1+eta K*hScore w (selected w ρ).1 x.1 x.2 := by
    have h := mul_le_mul_of_nonneg_left (abs_le.mp (selected_score_abs hK w hw hwf ρ hρ hp x)).1 hη.le
    nlinarith
  have hden : 0 < 1+eta K*(selected w ρ).2 := by
    have h := mul_le_mul_of_nonneg_left (abs_le.mp (selected_mean_abs hK w hw hwf ρ hρ hp)).1 hη.le
    nlinarith
  have hpos (x : Grid K × Act K) : 0 < nextTable w ρ x := by
    exact div_pos (mul_pos (hp x) (hnum x)) hden
  refine ⟨⟨fun x => (hpos x).le, ?_⟩, hpos⟩
  unfold nextTable
  rw [← Finset.sum_div]
  have heq : (∑ x, ρ x * (1+eta K*hScore w (selected w ρ).1 x.1 x.2)) =
      1+eta K*(selected w ρ).2 := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, hρ.2, selected_score, expectedScore]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [heq, div_self hden.ne']

theorem selected_mean_le (hK : 0<K) (C : ℝ)
    (hC : ∀ ρ : Grid K × Act K → ℝ, IsDist ρ → ∃ a : Act K,
      gap ρ a-beta K*info ρ a ≤ C/K)
    (w : Act K → ℝ) (hw : IsDist w) (hwf : ∀ a, wFloor K ≤ w a)
    (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (hp : ∀ x, 0<ρ x) :
    (selected w ρ).2 ≤ (C+1)/K := by
  obtain ⟨a, ha⟩ := hC ρ hρ
  obtain ⟨b, hb, hmin⟩ := selected_spec w ρ
  have hc := candidate_expected_bound hK ρ hρ hp w hw hwf a
  have hm := hmin a
  calc
    _ ≤ gap ρ a-beta K*info ρ a+1/K := hm.trans hc
    _ ≤ C/K+1/K := by linarith
    _ = _ := by ring

noncomputable def evolve (w : Act K → ℝ) : ℕ → (Grid K × Act K → ℝ) → (Grid K × Act K → ℝ)
  | 0, ρ => ρ
  | n+1, ρ => evolve w n (nextTable w ρ)

theorem evolve_succ (w : Act K → ℝ) (n : ℕ) (ρ : Grid K × Act K → ℝ) :
    evolve w (n+1) ρ = nextTable w (evolve w n ρ) := by
  induction n generalizing ρ with
  | zero => rfl
  | succ n ih => exact ih (nextTable w ρ)

noncomputable def tableAt (w : Act K → ℝ) (n : ℕ) : Grid K × Act K → ℝ :=
  evolve w n (fun _ => 1/(nA K*nG K))

noncomputable def proposalAt (w : Act K → ℝ) (n : ℕ) : Proposal K :=
  (selected w (tableAt w n)).1

theorem tableAt_invariant (hK : 0<K) (w : Act K → ℝ) (hw : IsDist w)
    (hwf : ∀ a, wFloor K ≤ w a) (n : ℕ) :
    IsDist (tableAt w n) ∧ ∀ x, 0<tableAt w n x := by
  have hden : 0<nA K*nG K := mul_pos (nA_pos K) (by rw [nG_eq]; positivity)
  induction n with
  | zero =>
    refine ⟨⟨fun _ => (one_div_pos.mpr hden).le, ?_⟩, fun _ => one_div_pos.mpr hden⟩
    change (∑ _x : Grid K × Act K, 1/(nA K*nG K)) = 1
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.card_univ, Fintype.card_prod, Nat.cast_mul]
    change nG K*nA K*(1/(nA K*nG K))=1
    rw [← div_eq_mul_one_div, mul_comm (nG K) (nA K), div_self hden.ne']
  | succ n ih =>
    change IsDist (evolve w (n+1) _) ∧ ∀ x, 0<evolve w (n+1) _ x
    rw [evolve_succ]
    exact nextTable_invariant hK w hw hwf _ ih.1 ih.2

theorem oneRoundLoop_value (w : Act K → ℝ) (n : ℕ) (ρ : Grid K × Act K → ℝ) :
    Value (oneRoundLoop K w n ρ) (selected w (evolve w n ρ)).1 := by
  induction n generalizing ρ with
  | zero => exact value_bind (oneStep_value w ρ) (value_pure _)
  | succ n ih => exact value_bind (oneStep_value w ρ) (ih (nextTable w ρ))

theorem oneRound_value_at (w : Act K → ℝ) (j : Fin (Jpar K)) :
    Value (oneRound K w j) (proposalAt w j.val) := by
  unfold oneRound
  apply value_bind (value_charge 40)
  apply value_bind (tab_value_total (tableList K) (mem_tableList K) _
    (fun _ => 1/(nA K*nG K)) (fun _ _ => value_bind (value_charge 3) (value_pure _)))
  exact oneRoundLoop_value w j.val _

theorem oneRoundVal_eq (w : Act K → ℝ) (j : Fin (Jpar K)) :
    oneRoundVal K w j = proposalAt w j.val := oneRound_value_at w j 0

theorem oneRound_value (w : Act K → ℝ) (j : Fin (Jpar K)) :
    Value (oneRound K w j) (oneRoundVal K w j) := by
  rw [oneRoundVal_eq]
  exact oneRound_value_at w j

theorem oneRound_updates (hK : 0<K) (w : Act K → ℝ) (hw : IsDist w)
    (hwf : ∀ a, wFloor K ≤ w a) (j : Fin (Jpar K)) :
    IsDist (oneRoundVal K w j).2.1 ∧ IsDist (oneRoundVal K w j).2.2 ∧
      (∀ a, wFloor K ≤ (oneRoundVal K w j).2.1 a) ∧
      (∀ a, wFloor K ≤ (oneRoundVal K w j).2.2 a) := by
  rw [oneRoundVal_eq]
  exact selected_updates hK w _ (tableAt_invariant hK w hw hwf j.val).1
    (tableAt_invariant hK w hw hwf j.val).2

end BilateralProfit.TelescopingSubmissionOneRoundMath

namespace BilateralProfit.TelescopingSubmissionUniformDraws

open scoped BigOperators

variable {I A : Type} [Fintype I] [Fintype A] [DecidableEq I]

/-- Exchange one coordinate of a complete draw path with an additional fresh draw. -/
def exchange (i : I) : ((I → A) × A) ≃ ((I → A) × A) where
  toFun p := (Function.update p.1 i p.2, p.1 i)
  invFun p := (Function.update p.1 i p.2, p.1 i)
  left_inv p := by
    apply Prod.ext
    · funext k
      by_cases hk : k = i
      · subst k; simp
      · simp [Function.update_of_ne hk]
    · simp
  right_inv p := by
    apply Prod.ext
    · funext k
      by_cases hk : k = i
      · subst k; simp
      · simp [Function.update_of_ne hk]
    · simp

/-- Finite-product conditioning on a fresh coordinate, expressed as an exact
identity between uniform averages. -/
lemma expect_update [Nonempty A] (i : I) (f : (I → A) → ℝ) :
    (𝔼 ω, f ω) = 𝔼 ω, 𝔼 j, f (Function.update ω i j) := by
  have h := Fintype.expect_equiv (exchange (A := A) i)
    (fun p : (I → A) × A => f (Function.update p.1 i p.2))
    (fun p : (I → A) × A => f p.1) (fun _ => rfl)
  have hprod (g : (I → A) × A → ℝ) :
      (𝔼 p, g p) = 𝔼 ω, 𝔼 j, g (ω, j) := by
    simpa only [Finset.univ_product_univ] using
      (Finset.expect_product (Finset.univ : Finset (I → A)) (Finset.univ : Finset A) g)
  rw [hprod, hprod] at h
  simpa only [Fintype.expect_const] using h.symm

/-- A function determined before a coordinate is drawn is unchanged by replacing
that coordinate. -/
lemma expect_fresh_bound [Nonempty A] (i : I) (f : (I → A) → ℝ) (B : ℝ)
    (h : ∀ ω, (𝔼 j, f (Function.update ω i j)) ≤ B) : (𝔼 ω, f ω) ≤ B := by
  rw [expect_update i f]
  exact (Finset.expect_le Finset.univ_nonempty (fun ω _ => h ω))

end BilateralProfit.TelescopingSubmissionUniformDraws

namespace BilateralProfit.TelescopingSubmissionOuterHistory

open CapacitatedAssort.General
open TelescopingSubmissionProgramFacts

abbrev State (K : ℕ) := (Act K → ℝ) × Array (Act K) × Array (Act K → ℝ)

noncomputable def initial (K : ℕ) : State K :=
  (fun _ => 1 / nA K, #[], #[fun _ => 1 / nA K])

noncomputable def step {K T : ℕ} (S : Fin T → ℝ × ℝ)
    (ω : Fin T → Fin (Jpar K)) (b : State K) (t : Fin T) : State K :=
  let P := oneRoundVal K b.1 (ω t)
  let w := if Trades (S t) (pt K P.1.1) then P.2.2 else P.2.1
  (w, b.2.1.push P.1, b.2.2.push w)

noncomputable def history {K T : ℕ} (S : Fin T → ℝ × ℝ)
    (ω : Fin T → Fin (Jpar K)) (n : ℕ) : State K :=
  ((List.finRange T).take n).foldl (step S ω) (initial K)

noncomputable def weights {K T : ℕ} (S : Fin T → ℝ × ℝ)
    (ω : Fin T → Fin (Jpar K)) (n : ℕ) : Act K → ℝ := (history S ω n).1

noncomputable def proposal {K T : ℕ} (S : Fin T → ℝ × ℝ)
    (ω : Fin T → Fin (Jpar K)) (t : Fin T) : Proposal K :=
  oneRoundVal K (weights S ω t) (ω t)

@[simp] theorem history_zero {K T : ℕ} (S : Fin T → ℝ × ℝ)
    (ω : Fin T → Fin (Jpar K)) : history S ω 0 = initial K := by
  simp [history]

theorem history_succ {K T : ℕ} (S : Fin T → ℝ × ℝ)
    (ω : Fin T → Fin (Jpar K)) (n : ℕ) (hn : n < T) :
    history S ω (n+1) = step S ω (history S ω n) ⟨n,hn⟩ := by
  unfold history
  rw [List.take_succ_eq_append_getElem (by simpa using hn)]
  simp

@[simp] theorem weights_zero {K T : ℕ} (S : Fin T → ℝ × ℝ)
    (ω : Fin T → Fin (Jpar K)) : weights S ω 0 = fun _ => 1 / nA K := rfl

theorem weights_succ {K T : ℕ} (S : Fin T → ℝ × ℝ)
    (ω : Fin T → Fin (Jpar K)) (t : Fin T) :
    weights S ω (t.val+1) =
      if Trades (S t) (pt K (proposal S ω t).1.1)
      then (proposal S ω t).2.2 else (proposal S ω t).2.1 := by
  simp only [weights, history_succ S ω t t.isLt, step, proposal]
  rfl

theorem history_causal {K T : ℕ} (S : Fin T → ℝ × ℝ)
    (ω ω' : Fin T → Fin (Jpar K)) (n : ℕ) (hn : n ≤ T)
    (heq : ∀ t : Fin T, t.val < n → ω t = ω' t) :
    history S ω n = history S ω' n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hnT : n < T := by omega
      rw [history_succ S ω n hnT, history_succ S ω' n hnT,
        ih (by omega) (fun t ht => heq t (by omega))]
      unfold step
      rw [heq ⟨n,hnT⟩ (by simp)]

theorem weights_update {K T : ℕ} (S : Fin T → ℝ × ℝ)
    (ω : Fin T → Fin (Jpar K)) (t : Fin T) (j : Fin (Jpar K)) :
    weights S (Function.update ω t j) t = weights S ω t := by
  unfold weights
  apply congrArg Prod.fst
  apply history_causal S _ _ t t.isLt.le
  intro s hs
  exact Function.update_of_ne (by intro h; subst s; omega) _ _

theorem history_sizes {K T : ℕ} (S : Fin T → ℝ × ℝ)
    (ω : Fin T → Fin (Jpar K)) (n : ℕ) (hn : n ≤ T) :
    (history S ω n).2.1.size = n ∧ (history S ω n).2.2.size = n+1 := by
  induction n with
  | zero => simp [initial]
  | succ n ih =>
      have h := ih (by omega)
      rw [history_succ S ω n (by omega)]
      simpa [step] using h

theorem recorded_weights {K T : ℕ} (S : Fin T → ℝ × ℝ)
    (ω : Fin T → Fin (Jpar K)) (n : ℕ) (hn : n ≤ T) :
    ∀ i, i ≤ n → (history S ω n).2.2.getD i (fun _ => 0) = weights S ω i := by
  induction n with
  | zero =>
      intro i hi
      have : i = 0 := by omega
      subst i
      simp [initial]
  | succ n ih =>
      intro i hi
      have hs := (history_sizes S ω n (by omega)).2
      by_cases hin : i ≤ n
      · rw [history_succ S ω n (by omega)]
        simpa only [step, Array.getD_eq_getD_getElem?, Array.getElem?_push,
          if_neg (by omega : i ≠ (history S ω n).2.2.size)] using ih (by omega) i hin
      · have hie : i = n+1 := by omega
        subst i
        rw [history_succ S ω n (by omega)]
        simp only [step, Array.getD_eq_getD_getElem?, Array.getElem?_push, hs, if_true,
          Option.getD_some]
        exact (weights_succ S ω ⟨n,by omega⟩).symm

theorem recorded_actions {K T : ℕ} (S : Fin T → ℝ × ℝ)
    (ω : Fin T → Fin (Jpar K)) (n : ℕ) (hn : n ≤ T) :
    ∀ t : Fin T, t.val < n → (history S ω n).2.1.getD t default = (proposal S ω t).1 := by
  induction n with
  | zero => intro t ht; omega
  | succ n ih =>
      intro t ht
      have hs := (history_sizes S ω n (by omega)).1
      by_cases htn : t.val < n
      · rw [history_succ S ω n (by omega)]
        simpa only [step, Array.getD_eq_getD_getElem?, Array.getElem?_push,
          if_neg (by omega : t.val ≠ (history S ω n).2.1.size)] using ih (by omega) t htn
      · have hte : t.val = n := by omega
        have htEq : t = (⟨n,by omega⟩ : Fin T) := Fin.ext hte
        rw [htEq]
        rw [history_succ S ω n (by omega)]
        simp only [step, Array.getD_eq_getD_getElem?, Array.getElem?_push, hs,
          if_true, Option.getD_some, proposal, weights]

theorem alg1_value (K T : ℕ) (S : Fin T → ℝ × ℝ)
    (ω : Fin T → Fin (Jpar K))
    (hval : ∀ w j, Value (oneRound K w j) (oneRoundVal K w j)) :
    Value (alg1 K T S ω) ((history S ω T).2.1, (history S ω T).2.2) := by
  unfold alg1
  apply value_bind (tab_value_total (actList K) (mem_actList K) _ (fun _ => 1/nA K) (by
    intro a ha
    exact value_bind (value_charge 2) (value_pure _)))
  have hloop := forIn_value (List.finRange T)
    (fun t (b : State K) => do
      charge 2
      let P ← oneRound K b.1 (ω t)
      charge 6
      let w := if Trades (S t) (pt K P.1.1) then P.2.2 else P.2.1
      charge (actList K).length
      pure (ForInStep.yield (w,b.2.1.push P.1,b.2.2.push w)))
    (fun t b => step S ω b t) (by
      intro t ht b
      apply value_bind (value_charge 2)
      apply value_bind (hval b.1 (ω t))
      apply value_bind (value_charge 6)
      exact value_bind (value_charge _) (value_pure _)) (initial K)
  have hret := value_bind (f := fun b : State K => pure (b.2.1,b.2.2)) hloop (value_pure
    (((List.finRange T).foldl (step S ω) (initial K)).2.1,
      ((List.finRange T).foldl (step S ω) (initial K)).2.2))
  simpa only [history, List.take_of_length_le (by simp : (List.finRange T).length ≤ T), initial] using hret

theorem alg1W_eq (K T : ℕ) (S : Fin T → ℝ × ℝ)
    (ω : Fin T → Fin (Jpar K))
    (hval : ∀ w j, Value (oneRound K w j) (oneRoundVal K w j))
    (n : ℕ) (hn : n ≤ T) : alg1W K T S ω n = weights S ω n := by
  unfold alg1W runW
  rw [alg1_value K T S ω hval 0]
  exact recorded_weights S ω T le_rfl n hn

theorem alg1Act_eq (K T : ℕ) (S : Fin T → ℝ × ℝ)
    (ω : Fin T → Fin (Jpar K))
    (hval : ∀ w j, Value (oneRound K w j) (oneRoundVal K w j))
    (t : Fin T) : alg1Act K T S ω t = (proposal S ω t).1 := by
  unfold alg1Act runW
  rw [alg1_value K T S ω hval 0]
  exact recorded_actions S ω T le_rfl t t.isLt

end BilateralProfit.TelescopingSubmissionOuterHistory

namespace BilateralProfit.TelescopingSubmissionOuterHistory

open scoped BigOperators

def Valid {K : ℕ} (w : Act K → ℝ) : Prop := IsDist w ∧ ∀ a, wFloor K ≤ w a

theorem initial_valid (K : ℕ) : Valid (fun _ : Act K => 1 / nA K) := by
  have hA := TelescopingSubmissionOneRoundMath.nA_pos K
  have hβ := TelescopingSubmissionOneRoundMath.beta_nonneg K
  have hbase := TelescopingSubmissionOneRoundMath.base_pos K
  constructor
  · constructor
    · intro a; positivity
    · simp [nA, div_eq_mul_inv]
  · intro a
    unfold wFloor
    apply one_div_le_one_div_of_le hA
    nlinarith [mul_nonneg hA.le (mul_nonneg hβ (Nat.cast_nonneg (α := ℝ) K))]

theorem weights_valid (K T : ℕ) (S : Fin T → ℝ × ℝ)
    (ω : Fin T → Fin (Jpar K))
    (hnext : ∀ w, Valid w → ∀ j,
      Valid (oneRoundVal K w j).2.1 ∧ Valid (oneRoundVal K w j).2.2)
    (n : ℕ) (hn : n ≤ T) : Valid (weights S ω n) := by
  induction n with
  | zero => simpa using initial_valid K
  | succ n ih =>
      rw [weights_succ S ω (⟨n,by omega⟩ : Fin T)]
      have h := hnext (weights S ω n) (ih (by omega)) (ω ⟨n,by omega⟩)
      split
      · exact h.2
      · exact h.1

theorem expectAlg_eq_expect (K T : ℕ) (f : (Fin T → Fin (Jpar K)) → ℝ) :
    expectAlg K T f = 𝔼 ω, f ω := (Fintype.expect_eq_sum_div_card f).symm

theorem score_expect_le (K T : ℕ) (hK : 0 < K) (S : Fin T → ℝ × ℝ)
    (v : Fin T → Grid K)
    (ωValid : ∀ (ω : Fin T → Fin (Jpar K)) n, n ≤ T → Valid (weights S ω n))
    (B : ℝ)
    (hscore : ∀ w, Valid w → ∀ x : Grid K, ∀ a : Act K,
      (∑ j : Fin (Jpar K), hScore w (oneRoundVal K w j) x a) / Jpar K ≤ B)
    (t : Fin T) (a : Act K) :
    (𝔼 ω, hScore (weights S ω t) (proposal S ω t) (v t) a) ≤ B := by
  letI : Nonempty (Fin (Jpar K)) := ⟨⟨0,TelescopingSubmissionOneRoundMath.J_pos hK⟩⟩
  apply TelescopingSubmissionUniformDraws.expect_fresh_bound t
  intro ω
  simpa only [proposal, weights_update, Function.update_self,
    Fintype.expect_eq_sum_div_card, Fintype.card_fin] using
    hscore (weights S ω t) (ωValid ω t t.isLt.le) (v t) a

theorem sum_log_weights (K T : ℕ) (S : Fin T → ℝ × ℝ)
    (ω : Fin T → Fin (Jpar K)) (a : Act K)
    (hv : ∀ n, n ≤ T → Valid (weights S ω n)) :
    (∑ t : Fin T, Real.log (weights S ω (t.val+1) a / weights S ω t a)) =
      Real.log (weights S ω T a / weights S ω 0 a) := by
  have hp (n : ℕ) (hn : n ≤ T) : 0 < weights S ω n a :=
    (TelescopingSubmissionOneRoundMath.floor_pos K).trans_le ((hv n hn).2 a)
  calc
    _ = ∑ t : Fin T, (Real.log (weights S ω (t.val+1) a) - Real.log (weights S ω t a)) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact Real.log_div (hp _ (by omega)).ne' (hp _ t.isLt.le).ne'
    _ = Real.log (weights S ω T a) - Real.log (weights S ω 0 a) := by
      change (∑ t : Fin T, (fun n : ℕ => Real.log (weights S ω (n+1) a) -
        Real.log (weights S ω n a)) t.val) = _
      rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => Real.log (weights S ω (n+1) a) -
        Real.log (weights S ω n a)) T]
      exact Finset.sum_range_sub (fun n => Real.log (weights S ω n a)) T
    _ = _ := (Real.log_div (hp T le_rfl).ne' (hp 0 (by omega)).ne').symm

theorem sum_scores (K T : ℕ) (v : Fin T → Grid K)
    (ω : Fin T → Fin (Jpar K)) (a : Act K)
    (hv : ∀ n, n ≤ T → Valid (weights (fun s => pt K (v s)) ω n)) :
    (∑ t : Fin T, hScore (weights (fun s => pt K (v s)) ω t)
      (proposal (fun s => pt K (v s)) ω t) (v t) a) =
      (∑ t, profit (pt K (v t)) (pt K a.1)) -
        (∑ t, profit (pt K (v t)) (pt K (proposal (fun s => pt K (v s)) ω t).1.1)) -
        beta K * Real.log (weights (fun s => pt K (v s)) ω T a /
          weights (fun s => pt K (v s)) ω 0 a) := by
  have hstep (t : Fin T) :
      Qsel (proposal (fun s => pt K (v s)) ω t) (v t) a =
        weights (fun s => pt K (v s)) ω (t.val+1) a := by
    rw [weights_succ]
    rfl
  simp only [hScore, hstep, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_log_weights K T _ ω a hv]

theorem log_weights_le (K T : ℕ) (S : Fin T → ℝ × ℝ)
    (ω : Fin T → Fin (Jpar K)) (a : Act K)
    (hv : Valid (weights S ω T)) :
    Real.log (weights S ω T a / weights S ω 0 a) ≤ Real.log (nA K) := by
  have hpos : 0 < weights S ω T a := (TelescopingSubmissionOneRoundMath.floor_pos K).trans_le (hv.2 a)
  have hle : weights S ω T a ≤ 1 := by
    calc
      _ ≤ ∑ b : Act K, weights S ω T b :=
        Finset.single_le_sum (fun b _ => hv.1.1 b) (Finset.mem_univ a)
      _ = 1 := hv.1.2
  simp only [weights_zero]
  have hA := TelescopingSubmissionOneRoundMath.nA_pos K
  apply Real.log_le_log (by positivity)
  simpa only [div_eq_mul_inv, inv_inv, one_mul] using mul_le_mul_of_nonneg_right hle hA.le

theorem pure_telescoping (K T : ℕ) (hK : 0 < K) (v : Fin T → Grid K) (B : ℝ)
    (hnext : ∀ w, Valid w → ∀ j,
      Valid (oneRoundVal K w j).2.1 ∧ Valid (oneRoundVal K w j).2.2)
    (hscore : ∀ w, Valid w → ∀ x : Grid K, ∀ a : Act K,
      (∑ j : Fin (Jpar K), hScore w (oneRoundVal K w j) x a) / Jpar K ≤ B)
    (a : Act K) :
    (∑ t, profit (pt K (v t)) (pt K a.1)) -
      (𝔼 ω, ∑ t, profit (pt K (v t)) (pt K (proposal (fun s => pt K (v s)) ω t).1.1)) ≤
      B * T + beta K * (𝔼 ω, Real.log (weights (fun s => pt K (v s)) ω T a /
        weights (fun s => pt K (v s)) ω 0 a)) ∧
    B * T + beta K * (𝔼 ω, Real.log (weights (fun s => pt K (v s)) ω T a /
        weights (fun s => pt K (v s)) ω 0 a)) ≤ B * T + beta K * Real.log (nA K) := by
  letI : Nonempty (Fin (Jpar K)) := ⟨⟨0,TelescopingSubmissionOneRoundMath.J_pos hK⟩⟩
  have hv := weights_valid K T (fun s => pt K (v s))
  have hscoreSum : (𝔼 ω, ∑ t : Fin T,
      hScore (weights (fun s => pt K (v s)) ω t)
        (proposal (fun s => pt K (v s)) ω t) (v t) a) ≤ B*T := by
    rw [Finset.expect_sum_comm]
    calc
      _ ≤ ∑ t : Fin T, B := Finset.sum_le_sum (fun t _ =>
        score_expect_le K T hK (fun s => pt K (v s)) v
          (fun ω n hn => hv ω hnext n hn) B hscore t a)
      _ = _ := by simp; ring
  have hid : (𝔼 ω, ∑ t : Fin T,
      hScore (weights (fun s => pt K (v s)) ω t)
        (proposal (fun s => pt K (v s)) ω t) (v t) a) =
      (∑ t, profit (pt K (v t)) (pt K a.1)) -
        (𝔼 ω, ∑ t, profit (pt K (v t)) (pt K (proposal (fun s => pt K (v s)) ω t).1.1)) -
        beta K * (𝔼 ω, Real.log (weights (fun s => pt K (v s)) ω T a /
          weights (fun s => pt K (v s)) ω 0 a)) := by
    simp_rw [sum_scores K T v _ a (fun n hn => hv _ hnext n hn)]
    rw [Finset.expect_sub_distrib, Finset.expect_sub_distrib, Fintype.expect_const,
      ← Finset.mul_expect]
  constructor
  · linarith
  · apply add_le_add_right
    apply mul_le_mul_of_nonneg_left _ (TelescopingSubmissionOneRoundMath.beta_nonneg K)
    calc
      _ ≤ 𝔼 ω, Real.log (nA K) := Finset.expect_le_expect
        (fun ω _ => log_weights_le K T _ ω a (hv ω hnext T le_rfl))
      _ = _ := Fintype.expect_const _

theorem telescoping_of_round (K : ℕ) (hK : 0 < K) (C₀ : ℝ)
    (hval : ∀ w j, TelescopingSubmissionProgramFacts.Value (oneRound K w j) (oneRoundVal K w j))
    (hnext : ∀ w, Valid w → ∀ j,
      Valid (oneRoundVal K w j).2.1 ∧ Valid (oneRoundVal K w j).2.2)
    (hscore : ∀ w, Valid w → ∀ x : Grid K, ∀ a : Act K,
      (∑ j : Fin (Jpar K), hScore w (oneRoundVal K w j) x a) / Jpar K ≤ (C₀+2)/K)
    (T : ℕ) (v : Fin T → Grid K) :
    (∀ ω : Fin T → Fin (Jpar K), ∀ t, t ≤ T →
      IsDist (alg1W K T (fun s => pt K (v s)) ω t) ∧
        ∀ a', wFloor K ≤ alg1W K T (fun s => pt K (v s)) ω t a') ∧
    ∀ a' : Act K,
      ∑ t, profit (pt K (v t)) (pt K a'.1) -
          expectAlg K T (fun ω => ∑ t, profit (pt K (v t))
            (pt K (alg1Act K T (fun s => pt K (v s)) ω t).1)) ≤
        (C₀ + 2) * T / K + beta K * expectAlg K T (fun ω =>
          Real.log (alg1W K T (fun s => pt K (v s)) ω T a' /
            alg1W K T (fun s => pt K (v s)) ω 0 a')) ∧
      (C₀ + 2) * T / K + beta K * expectAlg K T (fun ω =>
          Real.log (alg1W K T (fun s => pt K (v s)) ω T a' /
            alg1W K T (fun s => pt K (v s)) ω 0 a')) ≤
        (C₀ + 2) * T / K + beta K * Real.log (nA K) := by
  constructor
  · intro ω n hn
    rw [alg1W_eq K T _ ω hval n hn]
    exact weights_valid K T _ ω hnext n hn
  · intro a
    have h := pure_telescoping K T hK v ((C₀+2)/K) hnext hscore a
    simpa only [alg1Act_eq K T _ _ hval, alg1W_eq K T _ _ hval T le_rfl,
      alg1W_eq K T _ _ hval 0 (Nat.zero_le T), expectAlg_eq_expect,
      div_mul_eq_mul_div] using h

end BilateralProfit.TelescopingSubmissionOuterHistory

namespace BilateralProfit

/-- **The telescoping bound in the proof of Theorem 4.1**, Brüstle, di Gregorio, Fusco, Leonardi
(manuscript, sha256 e91e8127…), §4.2.2, pp.22–23 (PDF 24–25).

Let `C0` be a constant for which the information inequality (Theorem 4.2) holds at resolution
`K`, and run Algorithm 1 on a valuation sequence `v_1, …, v_T ∈ G_K`. Then
1. every weight vector `w_1, …, w_{T+1}` of every run is a probability vector with entries at least
   `1/(|𝒜|(1 + βK))` (the lower-bound condition of Lemma 4.6 "holds initially and is preserved by
   each update prescribed as in Equation (5)");
2. for every comparison price `a′ ∈ 𝒜`,
   `Σ_t Profit(v_t, a′) − E[Σ_t Profit(v_t, a_t)] ≤ (C0 + 2)T/K + β E[log(w_{T+1}(a′)/w_1(a′))]
     ≤ (C0 + 2)T/K + β log|𝒜|`.

**Formalization Note.** `w_{t+1}` is `alg1W … t` (`t = 0, …, T`); the expectation is over the
uniform draws `ω`. -/
theorem cert_telescoping_payload (K : ℕ) (hK : 0 < K) (C₀ : ℝ)
    (hC₀ : ∀ ρ : Grid K × Act K → ℝ, IsDist ρ →
      ∃ a : Act K, gap ρ a - beta K * info ρ a ≤ C₀ / K)
    (T : ℕ) (v : Fin T → Grid K) :
    (∀ ω : Fin T → Fin (Jpar K), ∀ t, t ≤ T →
      IsDist (alg1W K T (fun s => pt K (v s)) ω t) ∧
        ∀ a', wFloor K ≤ alg1W K T (fun s => pt K (v s)) ω t a') ∧
    ∀ a' : Act K,
      ∑ t, profit (pt K (v t)) (pt K a'.1) -
          expectAlg K T (fun ω => ∑ t, profit (pt K (v t))
            (pt K (alg1Act K T (fun s => pt K (v s)) ω t).1)) ≤
        (C₀ + 2) * T / K + beta K * expectAlg K T (fun ω =>
          Real.log (alg1W K T (fun s => pt K (v s)) ω T a' /
            alg1W K T (fun s => pt K (v s)) ω 0 a')) ∧
      (C₀ + 2) * T / K + beta K * expectAlg K T (fun ω =>
          Real.log (alg1W K T (fun s => pt K (v s)) ω T a' /
            alg1W K T (fun s => pt K (v s)) ω 0 a')) ≤
        (C₀ + 2) * T / K + beta K * Real.log (nA K)  := by
  apply TelescopingSubmissionOuterHistory.telescoping_of_round K hK C₀
    (fun w j => TelescopingSubmissionOneRoundMath.oneRound_value w j)
  · intro w hw j
    obtain ⟨h0,h1,hf0,hf1⟩ := TelescopingSubmissionOneRoundMath.oneRound_updates hK w hw.1 hw.2 j
    exact ⟨⟨h0,hf0⟩,⟨h1,hf1⟩⟩
  · intro w hw x a
    exact lemma_4_6 K hK C₀ hC₀ w hw.1 hw.2 x a

end BilateralProfit

open BilateralProfit

theorem solution (K : ℕ) (hK : 0 < K) (C₀ : ℝ)
    (hC₀ : ∀ ρ : Grid K × Act K → ℝ, IsDist ρ →
      ∃ a : Act K, gap ρ a - beta K * info ρ a ≤ C₀ / K)
    (T : ℕ) (v : Fin T → Grid K) :
    (∀ ω : Fin T → Fin (Jpar K), ∀ t, t ≤ T →
      IsDist (alg1W K T (fun s => pt K (v s)) ω t) ∧
        ∀ a', wFloor K ≤ alg1W K T (fun s => pt K (v s)) ω t a') ∧
    ∀ a' : Act K,
      ∑ t, profit (pt K (v t)) (pt K a'.1) -
          expectAlg K T (fun ω => ∑ t, profit (pt K (v t))
            (pt K (alg1Act K T (fun s => pt K (v s)) ω t).1)) ≤
        (C₀ + 2) * T / K + beta K * expectAlg K T (fun ω =>
          Real.log (alg1W K T (fun s => pt K (v s)) ω T a' /
            alg1W K T (fun s => pt K (v s)) ω 0 a')) ∧
      (C₀ + 2) * T / K + beta K * expectAlg K T (fun ω =>
          Real.log (alg1W K T (fun s => pt K (v s)) ω T a' /
            alg1W K T (fun s => pt K (v s)) ω 0 a')) ≤
        (C₀ + 2) * T / K + beta K * Real.log (nA K) := by exact BilateralProfit.cert_telescoping_payload K hK C₀ hC₀ T v

