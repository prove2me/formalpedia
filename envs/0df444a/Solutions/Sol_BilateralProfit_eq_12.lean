-- Prove2me | solution 1 for BilateralProfit.eq_12
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-13T15:39:35.240202+00:00
-- url     : https://prove2.me/submissions/af505f30-4bf3-4048-9db3-89f39966339c

import Mathlib
import Definitions.Def_BilateralProfit_Analysis
import Definitions.Def_RegretBandits_Stochastic_klBernoulli
import Theorems.Thm_InformationTheory_klDiv_compProd_self_eq_lintegral
import Theorems.Thm_InformationTheory_categorical_toReal_klDiv_eq_sum
import Theorems.Thm_RegretBandits_Stochastic_kl_bernoulli_bounds

namespace BilateralProfit.Eq12SubmissionTable

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

end BilateralProfit.Eq12SubmissionTable

namespace BilateralProfit.Eq12SubmissionFinite

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

noncomputable def atomic {A : Type*} [Fintype A] [MeasurableSpace A] (p : A → ℝ) : Measure A :=
  ∑ a, ENNReal.ofReal (p a) • Measure.dirac a

theorem atomic_apply {A : Type*} [Fintype A] [MeasurableSpace A]
    (p : A → ℝ) (s : Set A) :
    atomic p s = ∑ a, ENNReal.ofReal (p a) * Measure.dirac a s := by
  simp [atomic, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]

theorem atomic_singleton {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (p : A → ℝ) (a : A) : atomic p {a} = ENNReal.ofReal (p a) := by
  classical
  rw [atomic_apply]
  simp [Measure.dirac_apply', Set.indicator_apply, eq_comm]

theorem atomic_real_singleton {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (a : A) :
    (atomic p).real {a} = p a := by
  rw [Measure.real, atomic_singleton, ENNReal.toReal_ofReal (hp a)]

theorem atomic_probability {A : Type*} [Fintype A] [MeasurableSpace A]
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) :
    IsProbabilityMeasure (atomic p) := by
  constructor
  rw [atomic_apply]
  simp only [measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hp a), hs, ENNReal.ofReal_one]

instance atomicFinite {A : Type*} [Fintype A] [MeasurableSpace A] (p : A → ℝ) :
    IsFiniteMeasure (atomic p) := by
  constructor
  rw [atomic_apply]
  simp only [measure_univ, mul_one]
  exact ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.ofReal_lt_top)

theorem atomic_lintegral {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (p : A → ℝ) (f : A → ℝ≥0∞) :
    ∫⁻ a, f a ∂(atomic p) = ∑ a, ENNReal.ofReal (p a) * f a := by
  simp only [atomic, lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

theorem atomic_ac {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (p q : A → ℝ) (hq : ∀ a, 0 ≤ q a) (hzero : ∀ a, q a = 0 → p a = 0) :
    atomic p ≪ atomic q := by
  classical
  intro s hs
  rw [atomic_apply] at hs ⊢
  apply Finset.sum_eq_zero
  intro a _
  have hterm := (Finset.sum_eq_zero_iff.mp hs) a (Finset.mem_univ a)
  by_cases ha : a ∈ s
  · have hdirac : Measure.dirac a s = 1 := Measure.dirac_apply_of_mem ha
    rw [hdirac, mul_one, ENNReal.ofReal_eq_zero] at hterm
    have hqzero : q a = 0 := le_antisymm hterm (hq a)
    rw [hzero a hqzero, ENNReal.ofReal_zero, zero_mul]
  · have hdirac : Measure.dirac a s = 0 := by simp [Measure.dirac_apply, ha]
    rw [hdirac, mul_zero]

noncomputable def atomicKernel {A B : Type*} [Fintype A] [Fintype B]
    [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B]
    (p : A → B → ℝ) : Kernel A B :=
  Kernel.ofFunOfCountable (fun a => atomic (p a))

theorem atomicKernel_probability {A B : Type*} [Fintype A] [Fintype B]
    [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B]
    (p : A → B → ℝ) (hp : ∀ a b, 0 ≤ p a b) (hs : ∀ a, ∑ b, p a b = 1) :
    IsMarkovKernel (atomicKernel p) := by
  constructor
  intro a
  exact atomic_probability (p a) (hp a) (hs a)

theorem compProd_atomic_singleton {A B : Type*} [Fintype A] [Fintype B]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (p : A → ℝ) (κ : Kernel A B) [IsSFiniteKernel κ] (a : A) (b : B) :
    (atomic p ⊗ₘ κ) {(a, b)} = ENNReal.ofReal (p a) * κ a {b} := by
  have hset : ({(a, b)} : Set (A × B)) = ({a} : Set A) ×ˢ ({b} : Set B) := by ext x; simp
  rw [hset, Measure.compProd_apply_prod (measurableSet_singleton a) (measurableSet_singleton b)]
  rw [lintegral_singleton]
  rw [atomic_singleton, mul_comm]

end BilateralProfit.Eq12SubmissionFinite

namespace BilateralProfit.Eq12SubmissionFinite

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

theorem klDiv_map_equiv {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (e : A ≃ᵐ B) (μ ν : Measure A) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  apply le_antisymm (InformationTheory.klDiv_map_le μ ν e.measurable)
  have h := InformationTheory.klDiv_map_le (μ.map e) (ν.map e) e.symm.measurable
  simpa only [Measure.map_map e.symm.measurable e.measurable,
    e.symm_comp_self, Measure.map_id] using h

/-- Extend the published categorical KL expansion from `Fin k` to an arbitrary
nonempty finite measurable type by a measurable equivalence. -/
theorem finite_toReal_klDiv_eq_sum {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ ν : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν) :
    (klDiv μ ν).toReal = ∑ a, μ.real {a} * Real.log (μ.real {a} / ν.real {a}) := by
  classical
  let e : A ≃ᵐ Fin (Fintype.card A) :=
    { Fintype.equivFin A with
      measurable_toFun := measurable_of_countable _
      measurable_invFun := measurable_of_countable _ }
  letI : NeZero (Fintype.card A) := ⟨Fintype.card_ne_zero⟩
  letI : IsProbabilityMeasure (μ.map e) := Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  letI : IsProbabilityMeasure (ν.map e) := Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  have h := InformationTheory.categorical_toReal_klDiv_eq_sum (μ.map e) (ν.map e) (hac.map e.measurable)
  rw [klDiv_map_equiv e μ ν] at h
  have hsingle (r : Measure A) (i : Fin (Fintype.card A)) :
      (r.map e).real {i} = r.real {e.symm i} := by
    have hset : e ⁻¹' ({i} : Set (Fin (Fintype.card A))) = {e.symm i} := by
      ext a
      change e a = i ↔ a = e.symm i
      constructor
      · intro ha
        simpa only [e.symm_apply_apply] using congrArg e.symm ha
      · rintro rfl
        exact e.apply_symm_apply i
    rw [Measure.real, Measure.real, Measure.map_apply e.measurable (measurableSet_singleton i)]
    rw [hset]
  simp_rw [hsingle] at h
  exact h.trans (e.toEquiv.symm.sum_comp
    (fun a => μ.real {a} * Real.log (μ.real {a} / ν.real {a})))

theorem finite_klDiv_ne_top {A : Type*} [Finite A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ ν : Measure A) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hac : μ ≪ ν) :
    klDiv μ ν ≠ ⊤ := InformationTheory.klDiv_ne_top hac Integrable.of_finite

end BilateralProfit.Eq12SubmissionFinite

namespace BilateralProfit.Eq12SubmissionTable

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

variable {K : ℕ}

/-- On a null conditioning row, use the feedback marginal as a probability law.
This only completes a kernel and does not change any weighted conditional sum. -/
noncomputable def completedRow (ρ : Grid K × Act K → ℝ) (a a' : Act K) (z : Bool) : ℝ :=
  if margA ρ a' = 0 then zP ρ a z else jointP ρ a a' z / margA ρ a'

theorem completedRow_nonneg (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a a' : Act K) (z : Bool) : 0 ≤ completedRow ρ a a' z := by
  unfold completedRow
  split_ifs
  · exact z_nonneg ρ hρ a z
  · exact div_nonneg (joint_nonneg ρ hρ a a' z) (marg_nonneg ρ hρ a')

theorem completedRow_sum (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a a' : Act K) :
    ∑ z : Bool, completedRow ρ a a' z = 1 := by
  classical
  unfold completedRow
  split_ifs with hm
  · exact z_sum ρ hρ a
  · rw [← Finset.sum_div, row_sum, div_self hm]

theorem completedRow_factor (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a a' : Act K) (z : Bool) : margA ρ a' * completedRow ρ a a' z = jointP ρ a a' z := by
  unfold completedRow
  split_ifs with hm
  · rw [hm, zero_mul, joint_zero_of_marg_zero ρ hρ a a' hm]
  · exact mul_div_cancel₀ _ hm

theorem completedRow_zero (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a a' : Act K) (z : Bool) (hz : zP ρ a z = 0) : completedRow ρ a a' z = 0 := by
  unfold completedRow
  split_ifs with hm
  · exact hz
  · rw [joint_zero_of_z_zero ρ hρ a a' z hz, zero_div]

/-- Equation (12)'s alternative definition is obtained by specializing the
published common-marginal conditional-KL identity to the finite joint table.
The finite categorical expansion is also inherited from a published theorem. -/
theorem info_eq_conditional_average (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a : Act K) :
    info ρ a = ∑ a', margA ρ a' * ∑ z : Bool,
      (jointP ρ a a' z / margA ρ a') *
        Real.log ((jointP ρ a a' z / margA ρ a') / zP ρ a z) := by
  classical
  letI : MeasurableSpace (Act K) := ⊤
  letI : MeasurableSingletonClass (Act K) := ⟨fun _ => trivial⟩
  let μ := Eq12SubmissionFinite.atomic (margA ρ)
  let ν := Eq12SubmissionFinite.atomic (zP ρ a)
  let κ := Eq12SubmissionFinite.atomicKernel (completedRow ρ a)
  let η : Kernel (Act K) Bool := Kernel.const (Act K) ν
  letI : IsProbabilityMeasure μ := Eq12SubmissionFinite.atomic_probability _ (marg_nonneg ρ hρ) (marg_sum ρ hρ)
  letI : IsProbabilityMeasure ν := Eq12SubmissionFinite.atomic_probability _ (z_nonneg ρ hρ a) (z_sum ρ hρ a)
  letI : IsMarkovKernel κ := Eq12SubmissionFinite.atomicKernel_probability _
    (completedRow_nonneg ρ hρ a) (completedRow_sum ρ hρ a)
  have hac (a' : Act K) : κ a' ≪ η a' :=
    Eq12SubmissionFinite.atomic_ac _ _ (z_nonneg ρ hρ a) (completedRow_zero ρ hρ a a')
  have hacprod : μ ⊗ₘ κ ≪ μ ⊗ₘ η :=
    Measure.AbsolutelyContinuous.compProd_right (.of_forall hac)
  have hjoint (a' : Act K) (z : Bool) : (μ ⊗ₘ κ) {(a', z)} = ENNReal.ofReal (jointP ρ a a' z) := by
    rw [Eq12SubmissionFinite.compProd_atomic_singleton]
    change ENNReal.ofReal (margA ρ a') * Eq12SubmissionFinite.atomic (completedRow ρ a a') {z} = _
    rw [Eq12SubmissionFinite.atomic_singleton, ← ENNReal.ofReal_mul (marg_nonneg ρ hρ a'),
      completedRow_factor ρ hρ]
  have hproduct (a' : Act K) (z : Bool) : (μ ⊗ₘ η) {(a', z)} =
      ENNReal.ofReal (margA ρ a' * zP ρ a z) := by
    rw [Eq12SubmissionFinite.compProd_atomic_singleton]
    change ENNReal.ofReal (margA ρ a') * Eq12SubmissionFinite.atomic (zP ρ a) {z} = _
    rw [Eq12SubmissionFinite.atomic_singleton, ← ENNReal.ofReal_mul (marg_nonneg ρ hρ a')]
  have hjointReal (a' : Act K) (z : Bool) : (μ ⊗ₘ κ).real {(a', z)} = jointP ρ a a' z := by
    rw [Measure.real, hjoint, ENNReal.toReal_ofReal (joint_nonneg ρ hρ a a' z)]
  have hproductReal (a' : Act K) (z : Bool) : (μ ⊗ₘ η).real {(a', z)} = margA ρ a' * zP ρ a z := by
    rw [Measure.real, hproduct, ENNReal.toReal_ofReal
      (mul_nonneg (marg_nonneg ρ hρ a') (z_nonneg ρ hρ a z))]
  have hleft := Eq12SubmissionFinite.finite_toReal_klDiv_eq_sum (μ ⊗ₘ κ) (μ ⊗ₘ η) hacprod
  rw [Fintype.sum_prod_type] at hleft
  simp_rw [hjointReal, hproductReal] at hleft
  change (klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)).toReal = info ρ a at hleft
  have hrow (a' : Act K) : (klDiv (κ a') (η a')).toReal =
      ∑ z : Bool, completedRow ρ a a' z * Real.log (completedRow ρ a a' z / zP ρ a z) := by
    rw [Eq12SubmissionFinite.finite_toReal_klDiv_eq_sum (κ a') (η a') (hac a')]
    apply Finset.sum_congr rfl
    intro z _
    change (Eq12SubmissionFinite.atomic (completedRow ρ a a')).real {z} *
      Real.log ((Eq12SubmissionFinite.atomic (completedRow ρ a a')).real {z} /
        (Eq12SubmissionFinite.atomic (zP ρ a)).real {z}) = _
    rw [Eq12SubmissionFinite.atomic_real_singleton _ (completedRow_nonneg ρ hρ a a'),
      Eq12SubmissionFinite.atomic_real_singleton _ (z_nonneg ρ hρ a)]
  have hchain := InformationTheory.klDiv_compProd_self_eq_lintegral μ κ η hac
  have hright : (∫⁻ a', klDiv (κ a') (η a') ∂μ).toReal =
      ∑ a', margA ρ a' * ∑ z : Bool,
        completedRow ρ a a' z * Real.log (completedRow ρ a a' z / zP ρ a z) := by
    change (∫⁻ a', klDiv (κ a') (η a') ∂(Eq12SubmissionFinite.atomic (margA ρ))).toReal = _
    rw [Eq12SubmissionFinite.atomic_lintegral]
    have hfinite (a' : Act K) : ENNReal.ofReal (margA ρ a') * klDiv (κ a') (η a') ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Eq12SubmissionFinite.finite_klDiv_ne_top _ _ (hac a'))
    rw [ENNReal.toReal_sum (fun a' _ => hfinite a')]
    apply Finset.sum_congr rfl
    intro a' _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (marg_nonneg ρ hρ a'), hrow]
  calc
    info ρ a = (klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)).toReal := hleft.symm
    _ = (∫⁻ a', klDiv (κ a') (η a') ∂μ).toReal := congrArg ENNReal.toReal hchain
    _ = _ := hright
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a' _
      by_cases hm : margA ρ a' = 0
      · simp [hm]
      · simp only [completedRow, if_neg hm]

end BilateralProfit.Eq12SubmissionTable

namespace BilateralProfit.Eq12SubmissionTable

open RegretBandits.Stochastic (klBern)

variable {K : ℕ}

/-- The conditional feedback table is Bernoulli on every row of positive mass;
rows of zero mass contribute zero to both sides. -/
theorem conditional_sum_eq_bernoulli (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a : Act K) :
    ∑ a', margA ρ a' * ∑ z : Bool,
      (jointP ρ a a' z / margA ρ a') *
        Real.log ((jointP ρ a a' z / margA ρ a') / zP ρ a z) =
      ∑ a', margA ρ a' * klBern (Pcond ρ a' (pt K a.1)) (P0 ρ (pt K a.1)) := by
  apply Finset.sum_congr rfl
  intro a' _
  by_cases hm : margA ρ a' = 0
  · simp [hm]
  · rw [Fintype.sum_bool, cond_true, cond_false ρ a a' hm, z_true, z_false ρ hρ a]
    rfl

/-- Apply the published Bernoulli Pinsker bound on its interior domain; at
boundary marginal probabilities the positive-mass conditionals agree exactly. -/
theorem bernoulli_weighted_pinsker (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a : Act K) :
    2 * ∑ a', margA ρ a' * (Pcond ρ a' (pt K a.1) - P0 ρ (pt K a.1)) ^ 2 ≤
      ∑ a', margA ρ a' * klBern (Pcond ρ a' (pt K a.1)) (P0 ρ (pt K a.1)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a' _
  by_cases hm : margA ρ a' = 0
  · simp [hm]
  · have hp : Pcond ρ a' (pt K a.1) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨cond_nonneg ρ hρ a a', cond_le_one ρ hρ a a'⟩
    have hq0 := p0_nonneg ρ hρ a
    have hq1 := p0_le_one ρ hρ a
    by_cases hqzero : P0 ρ (pt K a.1) = 0
    · rw [cond_zero_of_p0_zero ρ hρ a a' hqzero, hqzero]
      norm_num [klBern]
    · by_cases hqone : P0 ρ (pt K a.1) = 1
      · rw [cond_one_of_p0_one ρ hρ a a' hm hqone, hqone]
        norm_num [klBern]
      · have hq : P0 ρ (pt K a.1) ∈ Set.Ioo (0 : ℝ) 1 :=
          ⟨lt_of_le_of_ne hq0 (Ne.symm hqzero), lt_of_le_of_ne hq1 hqone⟩
        have h := (RegretBandits.Stochastic.kl_bernoulli_bounds
          (Pcond ρ a' (pt K a.1)) (P0 ρ (pt K a.1)) hp hq).1
        have hmnonneg := marg_nonneg ρ hρ a'
        nlinarith [mul_le_mul_of_nonneg_left h hmnonneg]

end BilateralProfit.Eq12SubmissionTable

open BilateralProfit RegretBandits.Stochastic

theorem solution (K : ℕ) (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a : Act K) :
    info ρ a = ∑ a', margA ρ a' * ∑ z : Bool,
        (jointP ρ a a' z / margA ρ a') *
          Real.log ((jointP ρ a a' z / margA ρ a') / zP ρ a z) ∧
      ∑ a', margA ρ a' * ∑ z : Bool,
        (jointP ρ a a' z / margA ρ a') *
          Real.log ((jointP ρ a a' z / margA ρ a') / zP ρ a z) =
        ∑ a', margA ρ a' * klBern (Pcond ρ a' (pt K a.1)) (P0 ρ (pt K a.1)) ∧
      2 * ∑ a', margA ρ a' * (Pcond ρ a' (pt K a.1) - P0 ρ (pt K a.1)) ^ 2 ≤
        ∑ a', margA ρ a' * klBern (Pcond ρ a' (pt K a.1)) (P0 ρ (pt K a.1)) := by
  exact ⟨Eq12SubmissionTable.info_eq_conditional_average ρ hρ a,
    Eq12SubmissionTable.conditional_sum_eq_bernoulli ρ hρ a,
    Eq12SubmissionTable.bernoulli_weighted_pinsker ρ hρ a⟩

