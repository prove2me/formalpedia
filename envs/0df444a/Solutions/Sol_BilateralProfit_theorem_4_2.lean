-- Prove2me | solution 1 for BilateralProfit.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-13T15:41:11.623562+00:00
-- url     : https://prove2.me/submissions/6b22175a-1589-40dc-b93a-181cb8be3cf4

import Definitions.Def_BilateralProfit_SellerTree
import Mathlib
import Definitions.Def_BilateralProfit_Analysis
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Theorems.Thm_BilateralProfit_eq_12
import Theorems.Thm_BilateralProfit_lemma_4_5

namespace BilateralProfit.Theorem42SubmissionTradeFacts

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

end BilateralProfit.Theorem42SubmissionTradeFacts

namespace BilateralProfit.Theorem42Submission

open MeasureTheory

variable {K : ℕ}

/-- The expected profit when the action may depend on the valuation through rho. -/
noncomputable def coupledValue (ρ : Grid K × Act K → ℝ) : ℝ :=
  ∑ x, ρ x * profit (pt K x.1) (pt K x.2.1)

/-- The gain from the coupling over the best fixed reference action. -/
noncomputable def couplingGain (ρ : Grid K × Act K → ℝ) : ℝ :=
  coupledValue ρ - optVal ρ

lemma gap_eq_gain_add_gapStar (ρ : Grid K × Act K → ℝ) (a : Act K) :
    gap ρ a = couplingGain ρ + gapStar ρ a := by
  unfold gap couplingGain coupledValue gapStar gapStarPt valProfitPt
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

lemma grid_profit_mem (hK : 0 < K) (v : ℝ × ℝ) (a : Act K) :
    profit v (pt K a.1) ∈ Set.Icc (0 : ℝ) 1 := by
  have hs := Theorem42SubmissionTradeFacts.spread_mem hK a
  unfold profit tradeBit
  split_ifs <;> simpa using hs

lemma coupledValue_mem (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) :
    coupledValue ρ ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg (fun x _ =>
      mul_nonneg (hρ.1 x) (grid_profit_mem hK (pt K x.1) x.2).1)
  · calc
      coupledValue ρ ≤ ∑ x, ρ x := Finset.sum_le_sum (fun x _ => by
        simpa using mul_le_mul_of_nonneg_left
          (grid_profit_mem hK (pt K x.1) x.2).2 (hρ.1 x))
      _ = 1 := hρ.2

lemma couplingGain_le_one (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) :
    couplingGain ρ ≤ 1 := by
  unfold couplingGain
  linarith [(coupledValue_mem hK ρ hρ).2, Theorem42SubmissionTradeFacts.optVal_nonneg hK ρ hρ]

lemma gap_le_one (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a : Act K) :
    gap ρ a ≤ 1 := by
  have hgap : gap ρ a = coupledValue ρ - valProfit ρ a := by
    rw [gap_eq_gain_add_gapStar]
    unfold couplingGain gapStar gapStarPt valProfit
    ring
  rw [hgap]
  linarith [(coupledValue_mem hK ρ hρ).2, Theorem42SubmissionTradeFacts.valProfit_nonneg hK ρ hρ a]

lemma exists_optimal (ρ : Grid K × Act K → ℝ) :
    ∃ a : Act K, valProfit ρ a = optVal ρ := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image (Finset.univ : Finset (Act K))
    (valProfit ρ) (Finset.univ_nonempty)
  refine ⟨a, le_antisymm (Theorem42SubmissionTradeFacts.valProfit_le_optVal ρ a) ?_⟩
  exact ciSup_le (fun b => ha b (Finset.mem_univ b))

lemma optimal_gapStar {ρ : Grid K × Act K → ℝ} {a : Act K}
    (ha : valProfit ρ a = optVal ρ) : gapStar ρ a = 0 := by
  change optVal ρ - valProfit ρ a = 0
  rw [ha, sub_self]

lemma beta_nonneg (K : ℕ) : 0 ≤ beta K := by
  unfold beta
  positivity

end BilateralProfit.Theorem42Submission

namespace BilateralProfit.Theorem42Submission

variable {A B : Type} [Fintype A] [Fintype B]

/-- The mass of an event under finite nonnegative weights. -/
noncomputable def eventMass (p : B → ℝ) (E : B → Prop) : ℝ := by
  classical
  exact ∑ b, if E b then p b else 0

lemma eventMass_nonneg (p : B → ℝ) (hp : ∀ b, 0 ≤ p b) (E : B → Prop) :
    0 ≤ eventMass p E := by
  classical
  exact Finset.sum_nonneg (fun b _ => by split_ifs <;> simp [hp])

lemma eventMass_le_one (p : B → ℝ) (hp : ∀ b, 0 ≤ p b) (hpsum : ∑ b, p b = 1)
    (E : B → Prop) : eventMass p E ≤ 1 := by
  classical
  calc
    _ ≤ ∑ b, p b := Finset.sum_le_sum (fun b _ => by split_ifs <;> simp [hp])
    _ = 1 := hpsum

/-- Average a pointwise detection certificate, including zero-weight rows,
and exchange the two finite sums. -/
lemma eventMass_le_energy (p : B → ℝ) (hp : ∀ b, 0 ≤ p b) (E : B → Prop)
    (n : A → ℝ) (hn : ∀ a, 0 ≤ n a) (e : B → A → ℝ)
    (hsep : ∀ b, 0 < p b → E b → 1 ≤ ∑ a, n a * (e b a) ^ 2) :
    eventMass p E ≤ ∑ a, n a * ∑ b, p b * (e b a) ^ 2 := by
  classical
  calc
    _ ≤ ∑ b, p b * ∑ a, n a * (e b a) ^ 2 := by
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : E b
      · simp only [if_pos hb]
        by_cases hp0 : p b = 0
        · simp [hp0]
        · have hpos : 0 < p b := lt_of_le_of_ne (hp b) (Ne.symm hp0)
          simpa using mul_le_mul_of_nonneg_left (hsep b hpos hb) (hp b)
      · simp only [if_neg hb]
        exact mul_nonneg (hp b) (Finset.sum_nonneg (fun a _ => mul_nonneg (hn a) (sq_nonneg _)))
    _ = ∑ a, n a * ∑ b, p b * (e b a) ^ 2 := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring

lemma detection_cost_comparison (n g : A → ℝ) (hn : ∀ a, 0 ≤ n a)
    (hg : ∀ a, 0 ≤ g a) (d x : ℝ) (hd : d ≤ 2 * x) :
    (∑ a, n a * (d + g a)) ≤ 2 * ∑ a, n a * (g a + x) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have hpoint : d + g a ≤ 2 * (g a + x) := by linarith [hg a]
  nlinarith [mul_le_mul_of_nonneg_left hpoint (hn a)]

end BilateralProfit.Theorem42Submission

namespace BilateralProfit.Theorem42SubmissionTable

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

end BilateralProfit.Theorem42SubmissionTable

namespace BilateralProfit.Theorem42SubmissionConditionalLaws

open MeasureTheory

variable {K : ℕ}

noncomputable def rowTable (ρ : Grid K × Act K → ℝ) (a' : Act K) :
    Grid K × Act K → ℝ := by
  classical
  exact fun x => if x.2 = a' then ρ (x.1, a') / margA ρ a' else 0

lemma rowTable_expect (ρ : Grid K × Act K → ℝ) (a' : Act K) (f : Grid K → ℝ) :
    (∑ x, rowTable ρ a' x * f x.1) = (∑ v, ρ (v, a') * f v) / margA ρ a' := by
  classical
  simp [rowTable, Fintype.sum_prod_type, div_mul_eq_mul_div, Finset.sum_div]

lemma rowTable_isDist (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a' : Act K)
    (hm : 0 < margA ρ a') : IsDist (rowTable ρ a') := by
  classical
  constructor
  · intro x
    dsimp [rowTable]
    split_ifs
    · exact div_nonneg (hρ.1 _) hm.le
    · exact le_rfl
  · have h := rowTable_expect ρ a' (fun _ => 1)
    simp only [mul_one] at h
    change (∑ x, rowTable ρ a' x) = margA ρ a' / margA ρ a' at h
    simpa only [div_self hm.ne'] using h

noncomputable def condTable (ρ : Grid K × Act K → ℝ) (a' : Act K) :
    Grid K × Act K → ℝ :=
  if 0 < margA ρ a' then rowTable ρ a' else ρ

lemma condTable_isDist (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a' : Act K) :
    IsDist (condTable ρ a') := by
  classical
  unfold condTable
  split_ifs with hm
  · exact rowTable_isDist ρ hρ a' hm
  · exact hρ

noncomputable def condLaw (ρ : Grid K × Act K → ℝ) (a' : Act K) : Measure (ℝ × ℝ) :=
  margLaw (condTable ρ a')

theorem condLaw_isValLaw (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a' : Act K) : IsValLaw (condLaw ρ a') :=
  Theorem42SubmissionTradeFacts.margLaw_isValLaw hK _ (condTable_isDist ρ hρ a')

theorem Ptrade_condLaw (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a' : Act K) (hm : 0 < margA ρ a') (x : ℝ × ℝ) :
    Ptrade (condLaw ρ a') x = Pcond ρ a' x := by
  rw [condLaw, Theorem42SubmissionTradeFacts.Ptrade_margLaw_eq_P0 _ (condTable_isDist ρ hρ a')]
  simp only [condTable, if_pos hm]
  exact rowTable_expect ρ a' (fun v => tradeBit (pt K v) x)

lemma row_zero (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a' : Act K) (hm : margA ρ a' = 0) (v : Grid K) : ρ (v, a') = 0 := by
  have hle : ρ (v, a') ≤ margA ρ a' :=
    Finset.single_le_sum (fun w _ => hρ.1 (w, a')) (Finset.mem_univ v)
  exact le_antisymm (by linarith) (hρ.1 _)

lemma weighted_cond_profit (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a' a : Act K) :
    margA ρ a' * muP (condLaw ρ a') (pt K a.1) =
      ∑ v, ρ (v, a') * profit (pt K v) (pt K a.1) := by
  by_cases hm : 0 < margA ρ a'
  · rw [condLaw, Theorem42SubmissionTradeFacts.muP_margLaw_eq_valProfitPt _ (condTable_isDist ρ hρ a')]
    simp only [condTable, if_pos hm]
    change margA ρ a' * (∑ x, rowTable ρ a' x * profit (pt K x.1) (pt K a.1)) = _
    rw [rowTable_expect ρ a' (fun v => profit (pt K v) (pt K a.1))]
    field_simp
  · have hz : margA ρ a' = 0 := le_antisymm (le_of_not_gt hm) (Theorem42SubmissionTable.marg_nonneg ρ hρ a')
    simp only [hz, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro v _
    rw [row_zero ρ hρ a' hz v, zero_mul]

theorem sum_marg_cond_profit (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) :
    (∑ a', margA ρ a' * muP (condLaw ρ a') (pt K a'.1)) =
      Theorem42Submission.coupledValue ρ := by
  simp_rw [weighted_cond_profit hK ρ hρ]
  rw [Finset.sum_comm]
  simp only [Theorem42Submission.coupledValue, Fintype.sum_prod_type]

end BilateralProfit.Theorem42SubmissionConditionalLaws

namespace BilateralProfit.Theorem42Submission

open MeasureTheory

variable {K : ℕ}

noncomputable def conditionalImprovement (ρ : Grid K × Act K → ℝ) (b : Act K) : ℝ :=
  muP (Theorem42SubmissionConditionalLaws.condLaw ρ b) (pt K b.1) - optVal ρ

lemma conditionalImprovement_le_one (hK : 0 < K) (ρ : Grid K × Act K → ℝ)
    (hρ : IsDist ρ) (b : Act K) : conditionalImprovement ρ b ≤ 1 := by
  letI : IsProbabilityMeasure (Theorem42SubmissionConditionalLaws.condLaw ρ b) :=
    (Theorem42SubmissionConditionalLaws.condLaw_isValLaw hK ρ hρ b).1
  have hs := Theorem42SubmissionTradeFacts.spread_mem hK b
  have hp := Theorem42SubmissionTradeFacts.Ptrade_le_one (Theorem42SubmissionConditionalLaws.condLaw ρ b) (pt K b.1)
  have hp0 := Theorem42SubmissionTradeFacts.Ptrade_nonneg (Theorem42SubmissionConditionalLaws.condLaw ρ b) (pt K b.1)
  unfold conditionalImprovement muP
  have hopt := Theorem42SubmissionTradeFacts.optVal_nonneg hK ρ hρ
  have hmul := mul_le_mul_of_nonneg_right hs.2 hp0
  nlinarith

lemma sum_conditionalImprovement (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) :
    ∑ b, margA ρ b * conditionalImprovement ρ b = couplingGain ρ := by
  unfold conditionalImprovement couplingGain
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Theorem42SubmissionTable.marg_sum ρ hρ,
    Theorem42SubmissionConditionalLaws.sum_marg_cond_profit hK ρ hρ, one_mul]

end BilateralProfit.Theorem42Submission

namespace BilateralProfit.Theorem42Submission

open MeasureTheory

variable {K : ℕ}

/-- The inexpensive-detection weights bound each conditional improvement tail. -/
lemma conditional_tail_bound_from_quadratic (hK : 2 ≤ K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (C : ℝ)
    (hdetect : ∀ x : ℝ, 0 < x → x ≤ 1 →
      ∃ n : Act K → ℝ, (∀ a, 0 ≤ n a) ∧
        ∑ a, n a * (gapStar ρ a + x) ≤
          C * Real.log K ^ 3 * ((K : ℝ) / x + Real.log K ^ 3 / x ^ 2) ∧
        ∀ μ : Measure (ℝ × ℝ), IsValLaw μ →
          (∃ a : Act K, optVal ρ + x ≤ muP μ (pt K a.1)) →
            1 ≤ ∑ a, n a * (Ptrade μ (pt K a.1) - P0 ρ (pt K a.1)) ^ 2)
    (hquad : ∀ a : Act K, 2 * beta K * (∑ b, margA ρ b *
      (Pcond ρ b (pt K a.1) - P0 ρ (pt K a.1)) ^ 2) ≤ gap ρ a)
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) (hdx : couplingGain ρ ≤ 2 * x) :
    eventMass (margA ρ) (fun b => x ≤ conditionalImprovement ρ b) ≤
      C / beta K * Real.log K ^ 3 * ((K : ℝ) / x + Real.log K ^ 3 / x ^ 2) := by
  classical
  have hK0 : 0 < K := by omega
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK0
  have hlog : 0 < Real.log (K : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < K by omega))
  have hβ : 0 < beta K := by unfold beta; positivity
  obtain ⟨n, hn, hcost, hsep⟩ := hdetect x hx hx1
  let e := fun (b a : Act K) => Pcond ρ b (pt K a.1) - P0 ρ (pt K a.1)
  have htail := eventMass_le_energy (margA ρ) (Theorem42SubmissionTable.marg_nonneg ρ hρ)
    (fun b => x ≤ conditionalImprovement ρ b) n hn e (by
      intro b hb himprove
      have hμ := Theorem42SubmissionConditionalLaws.condLaw_isValLaw hK0 ρ hρ b
      have hyes : ∃ a : Act K, optVal ρ + x ≤
          muP (Theorem42SubmissionConditionalLaws.condLaw ρ b) (pt K a.1) := by
        refine ⟨b, ?_⟩
        change x ≤ muP (Theorem42SubmissionConditionalLaws.condLaw ρ b) (pt K b.1) - optVal ρ at himprove
        linarith
      have hh := hsep (Theorem42SubmissionConditionalLaws.condLaw ρ b) hμ hyes
      simpa only [e, Theorem42SubmissionConditionalLaws.Ptrade_condLaw hK0 ρ hρ b hb] using hh)
  have henergy : 2 * beta K * (∑ a, n a * ∑ b, margA ρ b * (e b a) ^ 2) ≤
      ∑ a, n a * gap ρ a := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    have h := mul_le_mul_of_nonneg_left (hquad a) (hn a)
    convert h using 1 <;> dsimp [e] <;> ring
  have hcostcomp : (∑ a, n a * gap ρ a) ≤ 2 * ∑ a, n a * (gapStar ρ a + x) := by
    simp_rw [gap_eq_gain_add_gapStar]
    exact detection_cost_comparison n (gapStar ρ) hn (Theorem42SubmissionTradeFacts.gapStar_nonneg ρ)
      (couplingGain ρ) x hdx
  have hmul : 2 * beta K * eventMass (margA ρ) (fun b => x ≤ conditionalImprovement ρ b) ≤
      2 * (C * Real.log K ^ 3 * ((K : ℝ) / x + Real.log K ^ 3 / x ^ 2)) :=
    (mul_le_mul_of_nonneg_left htail (by positivity)).trans
      (henergy.trans (hcostcomp.trans (mul_le_mul_of_nonneg_left hcost (by norm_num))))
  have hhalf : beta K * eventMass (margA ρ) (fun b => x ≤ conditionalImprovement ρ b) ≤
      C * Real.log K ^ 3 * ((K : ℝ) / x + Real.log K ^ 3 / x ^ 2) := by linarith
  have hdiv : eventMass (margA ρ) (fun b => x ≤ conditionalImprovement ρ b) ≤
      (C * Real.log K ^ 3 * ((K : ℝ) / x + Real.log K ^ 3 / x ^ 2)) / beta K :=
    (le_div_iff₀ hβ).mpr (by nlinarith [hhalf])
  convert hdiv using 1 <;> ring

end BilateralProfit.Theorem42Submission

namespace BilateralProfit.Theorem42Submission

lemma log_grid_lower (K : ℕ) (hK : 2 ≤ K) : (1 / 2 : ℝ) ≤ Real.log (K : ℝ) := by
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  exact h2.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hK))

/-- The scalar contradiction after integrating the detection-tail bound.
The constant is deliberately generous because the theorem leaves it universal. -/
lemma information_scalar_contradiction (C : ℝ) (hC : 0 ≤ C) (K : ℕ) (hK : 2 ≤ K)
    (d : ℝ) (hd : 0 < d)
    (hlower : 64 * (C + 1) / K < d)
    (htail : d / 2 ≤ C / beta K * Real.log K ^ 3 *
      ((K : ℝ) * Real.log (2 / d) + 2 * Real.log K ^ 3 / d)) : False := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  let L := Real.log (K : ℝ)
  let u := (K : ℝ) * d
  have hL : (1 / 2 : ℝ) ≤ L := log_grid_lower K hK
  have hLpos : 0 < L := by linarith
  have hu : 64 * (C + 1) < u := by
    dsimp [u]
    nlinarith [(div_lt_iff₀ hKr).mp hlower]
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hprod : (1 : ℝ) ≤ d * K := by dsimp [u] at hu; nlinarith
  have hratio : 2 / d ≤ 2 * (K : ℝ) := (div_le_iff₀ hd).mpr (by nlinarith)
  have hlog2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by exact_mod_cast hK)
  have hlog : Real.log (2 / d) ≤ 2 * L := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 / d) hratio
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hKr.ne'] at h
    dsimp [L] at hlog2 ⊢
    linarith
  have hβ : 0 < beta K := by unfold beta; positivity
  have hscaled := mul_le_mul_of_nonneg_left htail (show 0 ≤ beta K * d by positivity)
  have hquad : u ^ 2 * L ^ 6 / 2 ≤ C * L ^ 3 * (u * Real.log (2 / d) + 2 * L ^ 3) := by
    calc
      _ = (beta K * d) * (d / 2) := by dsimp [u, L, beta]; ring
      _ ≤ (beta K * d) * (C / beta K * Real.log K ^ 3 *
          ((K : ℝ) * Real.log (2 / d) + 2 * Real.log K ^ 3 / d)) := hscaled
      _ = _ := by dsimp [u, L]; field_simp [hβ.ne', hd.ne'] <;> ring
  have hqlog : u ^ 2 * L ^ 6 / 2 ≤ 2 * C * u * L ^ 4 + 2 * C * L ^ 6 := by
    calc
      _ ≤ C * L ^ 3 * (u * (2 * L) + 2 * L ^ 3) := by
        apply hquad.trans
        gcongr
      _ = _ := by ring
  have hLsq : (1 / 4 : ℝ) ≤ L ^ 2 := by nlinarith
  have hpow : 2 * L ^ 4 ≤ 8 * L ^ 6 := by
    have hm := mul_le_mul_of_nonneg_left hLsq (show 0 ≤ 8 * L ^ 4 by positivity)
    nlinarith [show L ^ 6 = L ^ 4 * L ^ 2 by ring]
  have hquad' : u ^ 2 / 2 ≤ 8 * C * u + 2 * C := by
    apply (mul_le_mul_iff_right₀ (show 0 < L ^ 6 by positivity)).mp
    calc
      L ^ 6 * (u ^ 2 / 2) = u ^ 2 * L ^ 6 / 2 := by ring
      _ ≤ 2 * C * u * L ^ 4 + 2 * C * L ^ 6 := hqlog
      _ ≤ L ^ 6 * (8 * C * u + 2 * C) := by
        have hm := mul_le_mul_of_nonneg_left hpow (show 0 ≤ C * u by positivity)
        nlinarith
  have hmul := mul_lt_mul_of_pos_right hu hu0
  have hCu : 0 ≤ C * u := mul_nonneg hC hu0.le
  have hCu' : C ≤ u := by linarith
  nlinarith

end BilateralProfit.Theorem42Submission

namespace BilateralProfit.Theorem42Submission

open MeasureTheory Set

variable {X : Type} [Fintype X]

lemma integral_tail_atom (a y c : ℝ) (hy : y ≤ 1) :
    (∫ x in Ioc a 1, if x ≤ y then c else 0) = c * max (y - a) 0 := by
  classical
  have hfun : (fun x : ℝ => if x ≤ y then c else 0) = (Iic y).indicator (fun _ => c) := rfl
  rw [hfun, setIntegral_indicator measurableSet_Iic]
  have hset : Ioc a 1 ∩ Iic y = Ioc a y := by
    ext x
    simp only [mem_inter_iff, mem_Ioc, mem_Iic]
    constructor
    · rintro ⟨⟨ha,h1⟩,hy⟩; exact ⟨ha,hy⟩
    · rintro ⟨ha,hxy⟩; exact ⟨⟨ha,hxy.trans hy⟩,hxy⟩
  rw [hset, integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc, smul_eq_mul,
    ENNReal.toReal_ofReal']
  ring

lemma integrable_tail_atom (a y c : ℝ) :
    IntegrableOn (fun x : ℝ => if x ≤ y then c else 0) (Ioc a 1) := by
  have hint : IntegrableOn (fun _ : ℝ => c) (Ioc a 1) := integrableOn_const (by simp [Real.volume_Ioc])
  exact hint.indicator measurableSet_Iic

lemma integral_eventMass_tail (p y : X → ℝ) (a : ℝ) (hy : ∀ i, y i ≤ 1) :
    (∫ x in Ioc a 1, eventMass p (fun i => x ≤ y i)) =
      ∑ i, p i * max (y i - a) 0 := by
  classical
  unfold eventMass
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_tail_atom a (y i) (p i))]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_tail_atom a (y i) (p i) (hy i)

lemma integral_one_div_sq (a : ℝ) (ha : 0 < a) :
    (∫ x in a..1, (1 : ℝ) / x ^ 2) = 1 / a - 1 := by
  have h := integral_zpow (a := a) (b := 1) (n := (-2 : ℤ))
    (Or.inr ⟨by norm_num, notMem_uIcc_of_lt ha (by norm_num : (0 : ℝ) < 1)⟩)
  norm_num at h
  rw [show (1 - a⁻¹) / (-1 : ℝ) = a⁻¹ - 1 by ring] at h
  simpa only [zpow_neg, zpow_natCast, one_div, inv_pow] using h

/-- Finite weighted layer cake above half of the positive mean, followed by
the exact integrals of `1/x` and `1/x²`. The observations `y` may be negative. -/
theorem weighted_tail_bound (p y : X → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hy : ∀ i, y i ≤ 1) (d A B : ℝ) (hd : d = ∑ i, p i * y i)
    (hd0 : 0 < d) (hd1 : d ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (htail : ∀ x : ℝ, d / 2 ≤ x → x ≤ 1 →
      eventMass p (fun i => x ≤ y i) ≤ A / x + B / x ^ 2) :
    d / 2 ≤ A * Real.log (2 / d) + 2 * B / d := by
  classical
  let a := d / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have htailInt : IntegrableOn (fun x => eventMass p (fun i => x ≤ y i)) (Ioc a 1) := by
    unfold eventMass
    exact integrable_finsetSum _ (fun i _ => integrable_tail_atom a (y i) (p i))
  have hmean : d ≤ a + ∫ x in Ioc a 1, eventMass p (fun i => x ≤ y i) := by
    rw [hd, integral_eventMass_tail p y a hy]
    calc
      _ ≤ ∑ i, p i * (a + max (y i - a) 0) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (hp i)
        linarith [le_max_left (y i - a) 0]
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hpsum, one_mul]
  have hnonzero : ∀ x ∈ Icc a 1, x ≠ 0 := by
    intro x hx
    linarith [hx.1]
  have hint1 : IntervalIntegrable (fun x : ℝ => 1 / x) volume a 1 :=
    (continuousOn_const.div continuousOn_id hnonzero).intervalIntegrable_of_Icc ha1
  have hint2 : IntervalIntegrable (fun x : ℝ => 1 / x ^ 2) volume a 1 :=
    (continuousOn_const.div (continuousOn_id.pow 2) (fun x hx => pow_ne_zero 2 (hnonzero x hx))).intervalIntegrable_of_Icc ha1
  have hrhsInt : IntegrableOn (fun x : ℝ => A / x + B / x ^ 2) (Ioc a 1) := by
    have hh := (hint1.const_mul A).add (hint2.const_mul B)
    have heq : (fun x : ℝ => A * (1 / x) + B * (1 / x ^ 2)) =
        (fun x : ℝ => A / x + B / x ^ 2) := by funext x; ring
    rw [heq] at hh
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).mp hh
  have hcompare : (∫ x in Ioc a 1, eventMass p (fun i => x ≤ y i)) ≤
      ∫ x in Ioc a 1, A / x + B / x ^ 2 := by
    apply setIntegral_mono_on htailInt hrhsInt measurableSet_Ioc
    intro x hx
    exact htail x hx.1.le hx.2
  have hcalc : (∫ x in Ioc a 1, A / x + B / x ^ 2) =
      A * Real.log (1 / a) + B * (1 / a - 1) := by
    rw [← intervalIntegral.integral_of_le ha1]
    have heq : (fun x : ℝ => A / x + B / x ^ 2) =
        (fun x : ℝ => A * (1 / x) + B * (1 / x ^ 2)) := by funext x; ring
    rw [heq, intervalIntegral.integral_add (hint1.const_mul A) (hint2.const_mul B),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_one_div_of_pos ha (by norm_num : (0 : ℝ) < 1), integral_one_div_sq a ha]
  have hinv : 1 / a = 2 / d := by dsimp [a]; ring
  rw [hcalc, hinv] at hcompare
  have hlow : d / 2 ≤ ∫ x in Ioc a 1, eventMass p (fun i => x ≤ y i) := by
    dsimp [a] at hmean
    linarith
  calc
    _ ≤ A * Real.log (2 / d) + B * (2 / d - 1) := hlow.trans hcompare
    _ ≤ _ := by
      rw [show B * (2 / d - 1) = 2 * B / d - B by ring]
      linarith

theorem finite_tail_integral_bound (p : X → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (y : X → ℝ) (hy : ∀ i, y i ≤ 1) (d : ℝ) (hd : 0 < d) (hd1 : d ≤ 1)
    (hmean : ∑ i, p i * y i = d) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (htail : ∀ x : ℝ, d / 2 ≤ x → x ≤ 1 →
      eventMass p (fun i => x ≤ y i) ≤ A / x + B / x ^ 2) :
    d / 2 ≤ A * Real.log (2 / d) + 2 * B / d :=
  weighted_tail_bound p y hp hpsum hy d A B hmean.symm hd hd1 hA hB htail

end BilateralProfit.Theorem42Submission

namespace BilateralProfit.Theorem42Submission

open MeasureTheory

variable {K : ℕ}

lemma information_quadratic (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a : Act K) :
    2 * ∑ b, margA ρ b * (Pcond ρ b (pt K a.1) - P0 ρ (pt K a.1)) ^ 2 ≤ info ρ a := by
  have h := eq_12 K hK ρ hρ a
  exact h.2.2.trans_eq (h.1.trans h.2.1).symm

lemma information_nonneg (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a : Act K) : 0 ≤ info ρ a := by
  apply le_trans _ (information_quadratic hK ρ hρ a)
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun b _ =>
    mul_nonneg (Theorem42SubmissionTable.marg_nonneg ρ hρ b) (sq_nonneg _)))

lemma gain_lower_of_contradiction (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (C₀ : ℝ) (hall : ∀ a : Act K, C₀ / K < gap ρ a - beta K * info ρ a) :
    C₀ / K < couplingGain ρ := by
  obtain ⟨a, ha⟩ := exists_optimal ρ
  have hgap := gap_eq_gain_add_gapStar ρ a
  rw [optimal_gapStar ha, add_zero] at hgap
  have hinfo := mul_nonneg (beta_nonneg K) (information_nonneg hK ρ hρ a)
  have hstrict := hall a
  rw [hgap] at hstrict
  exact hstrict.trans_le (sub_le_self _ hinfo)

lemma quadratic_control (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hall : ∀ a : Act K, C₀ / K < gap ρ a - beta K * info ρ a) (a : Act K) :
    2 * beta K * (∑ b, margA ρ b *
      (Pcond ρ b (pt K a.1) - P0 ρ (pt K a.1)) ^ 2) ≤ gap ρ a := by
  have hquad := mul_le_mul_of_nonneg_left (information_quadratic hK ρ hρ a) (beta_nonneg K)
  have hpos : 0 ≤ C₀ / K := div_nonneg hC₀ (Nat.cast_nonneg K)
  have hstrict := hall a
  nlinarith

end BilateralProfit.Theorem42Submission

namespace BilateralProfit

open MeasureTheory Theorem42Submission

/-- The information inequality of Theorem 4.2, including the direct `K = 1` case. -/
theorem cert_theorem_4_2 :
    ∃ C₀ : ℝ, ∀ K : ℕ, 0 < K → ∀ ρ : Grid K × Act K → ℝ, IsDist ρ →
      ∃ a : Act K, gap ρ a - beta K * info ρ a ≤ C₀ / K := by
  classical
  obtain ⟨C, hdetect⟩ := lemma_4_5
  refine ⟨64 * (max C 0 + 1), ?_⟩
  intro K hK ρ hρ
  have hC : 0 ≤ max C 0 := le_max_right C 0
  by_cases hK2 : 2 ≤ K
  · by_contra hnone
    push_neg at hnone
    let d := couplingGain ρ
    have hC₀ : 0 ≤ 64 * (max C 0 + 1) := by positivity
    have hlower : 64 * (max C 0 + 1) / K < d :=
      gain_lower_of_contradiction hK ρ hρ _ hnone
    have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
    have hd : 0 < d := (div_pos (by positivity : 0 < 64 * (max C 0 + 1)) hKr).trans hlower
    have hd1 : d ≤ 1 := couplingGain_le_one hK ρ hρ
    have hlog : 0 ≤ Real.log (K : ℝ) := (log_grid_lower K hK2).trans' (by norm_num)
    have hβ : 0 < beta K := by
      unfold beta
      have hlogpos : 0 < Real.log (K : ℝ) := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
        (log_grid_lower K hK2)
      positivity
    let A := max C 0 / beta K * Real.log K ^ 3 * (K : ℝ)
    let B := max C 0 / beta K * Real.log K ^ 6
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have htail : ∀ x : ℝ, d / 2 ≤ x → x ≤ 1 →
        eventMass (margA ρ) (fun b => x ≤ conditionalImprovement ρ b) ≤ A / x + B / x ^ 2 := by
      intro x hxd hx1
      have hx : 0 < x := (half_pos hd).trans_le hxd
      have hbound := conditional_tail_bound_from_quadratic hK2 ρ hρ (max C 0)
        (fun ε hε hε1 => by
          obtain ⟨n, hn, hcost, hsep⟩ := hdetect K hK2 ρ hρ ε hε hε1
          refine ⟨n, hn, hcost.trans ?_, hsep⟩
          gcongr
          exact le_max_left C 0)
        (fun a => quadratic_control hK ρ hρ _ hC₀ hnone a) x hx hx1 (by dsimp [d] at hxd; linarith)
      convert hbound using 1 <;> dsimp [A, B] <;> ring
    have hmean : ∑ b, margA ρ b * conditionalImprovement ρ b = d :=
      sum_conditionalImprovement hK ρ hρ
    have hint := finite_tail_integral_bound (margA ρ) (Theorem42SubmissionTable.marg_nonneg ρ hρ)
      (Theorem42SubmissionTable.marg_sum ρ hρ) (conditionalImprovement ρ)
      (conditionalImprovement_le_one hK ρ hρ) d hd hd1 hmean A B hA hB htail
    have hsource : d / 2 ≤ max C 0 / beta K * Real.log K ^ 3 *
        ((K : ℝ) * Real.log (2 / d) + 2 * Real.log K ^ 3 / d) := by
      convert hint using 1 <;> dsimp [A, B] <;> ring
    exact information_scalar_contradiction (max C 0) hC K hK2 d hd hlower hsource
  · have hKeq : K = 1 := by omega
    subst K
    refine ⟨default, ?_⟩
    have hg := gap_le_one (by decide : 0 < 1) ρ hρ default
    simp only [beta, Nat.cast_one, Real.log_one, zero_pow (by decide : 6 ≠ 0),
      mul_zero, zero_mul, sub_zero, div_one]
    linarith

end BilateralProfit

open BilateralProfit

/-- **Theorem 4.2 (Information Inequality)**, Brüstle, di Gregorio, Fusco, Leonardi
(manuscript, sha256 e91e8127…), p.19 (PDF 21): there is a universal constant `C0` such that for
every distribution `ρ` over `G_K × 𝒜`, with `β = K² log⁶ K`,
`min_{a ∈ 𝒜} {Δ_ρ(a) − β ℐ_ρ(a)} ≤ C0/K`.

**Formalization Note.** `C0` is chosen before `K` and `ρ`. The minimum over the finite nonempty
`𝒜` is written as the existence of a minimizing action. `0 < K` is the grid's step size `1/K`. -/
theorem solution :
    ∃ C₀ : ℝ, ∀ K : ℕ, 0 < K → ∀ ρ : Grid K × Act K → ℝ, IsDist ρ →
      ∃ a : Act K, gap ρ a - beta K * info ρ a ≤ C₀ / K := by exact BilateralProfit.cert_theorem_4_2
