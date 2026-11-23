-- Prove2me | solution 1 for CalibeatBandit.integral_periodHits_average_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T18:47:37.233562+00:00
-- url     : https://prove2.me/submissions/9bfa7412-f0c7-41f9-ba83-2b78eba5f48b

import Mathlib
import Definitions.Def_CalibeatBandit_lower_bound_models
import Definitions.Def_CalibeatBandit_IsColStochastic
import Definitions.Def_CalibeatBandit_fixedPointSol
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Definitions.Def_CalibeatBandit_pseudoSwapRegret
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_hard_tree_environment
import Definitions.Def_CalibeatBandit_hard_tree_analysis
import Theorems.Thm_CalibeatBandit_lemma_4_7

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory InformationTheory ProbabilityTheory Set
open scoped ENNReal

/-- Binary relative entropy, written using the continuous extension of
`x log x` at zero. The second parameter is in the open unit interval. -/
noncomputable def binaryEntropy (p q : ℝ) : ℝ :=
  p * Real.log p + (1 - p) * Real.log (1 - p)
    - p * Real.log q - (1 - p) * Real.log (1 - q)

/-- The binary form of Pinsker's inequality, including endpoint values of p. -/
theorem binaryEntropy_ge {p q : ℝ} (hp : p ∈ Icc 0 1) (hq : q ∈ Ioo 0 1) :
    2 * (p - q) ^ 2 ≤ binaryEntropy p q := by
  let f (x : ℝ) := binaryEntropy x q - 2 * (x - q) ^ 2
  let f' (x : ℝ) := Real.log x - Real.log (1 - x) - Real.log q + Real.log (1 - q) - 4 * (x - q)
  let f'' (x : ℝ) := x⁻¹ + (1 - x)⁻¹ - 4
  have ha : Continuous (fun x : ℝ => 1 - x) := continuous_const.sub continuous_id
  have hf : Continuous f :=
    (((Real.continuous_mul_log.add (Real.continuous_mul_log.comp ha)).sub (continuous_id.mul_const _)).sub
      (ha.mul_const _)).sub (((continuous_id.sub continuous_const).pow 2).const_mul 2)
  have hd (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt f (f' x) x := by
    have h1 := Real.hasDerivAt_mul_log hx.1.ne'
    have h2 := (Real.hasDerivAt_mul_log (sub_pos.mpr hx.2).ne').comp x
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x))
    have h3 := (hasDerivAt_id x).mul_const (Real.log q)
    have h4 := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).mul_const (Real.log (1 - q))
    have h5 := (((hasDerivAt_id x).sub_const q).pow 2).const_mul 2
    convert (((h1.add h2).sub h3).sub h4).sub h5 using 1 <;>
      first | rfl | (dsimp [f']; norm_num; ring)
  have hdd (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt f' (f'' x) x := by
    have h1 := Real.hasDerivAt_log hx.1.ne'
    have h2 := (Real.hasDerivAt_log (sub_pos.mpr hx.2).ne').comp x
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x))
    have h3 := ((hasDerivAt_id x).sub_const q).const_mul 4
    convert (((h1.sub h2).sub_const (Real.log q)).add_const (Real.log (1 - q))).sub h3 using 1 <;>
      first | rfl | (dsimp [f'']; norm_num)
  have hpos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 ≤ f'' x := by
    have h1 : 0 < x := hx.1
    have h2 : 0 < 1 - x := sub_pos.mpr hx.2
    dsimp [f'']
    apply (le_of_mul_le_mul_right _ (mul_pos h1 h2))
    field_simp [h1.ne', h2.ne']
    nlinarith [sq_nonneg (2 * x - 1)]
  have hc : ConvexOn ℝ (Icc 0 1) f := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (f' := f') (f'' := f'') (convex_Icc _ _) hf.continuousOn
    · rw [interior_Icc]
      exact fun x hx => (hd x hx).hasDerivWithinAt
    · rw [interior_Icc]
      exact fun x hx => (hdd x hx).hasDerivWithinAt
    · rw [interior_Icc]
      exact hpos
  have hq' : q ∈ Icc 0 1 := ⟨hq.1.le, hq.2.le⟩
  have hz : f q = 0 := by dsimp [f, binaryEntropy]; ring
  have hdq : HasDerivAt f 0 q := by
    convert hd q hq using 1
    dsimp [f']
    ring
  apply sub_nonneg.mp
  change 0 ≤ f p
  rcases lt_trichotomy p q with h | rfl | h
  · have hs := hc.slope_le_of_hasDerivAt hp hq' h hdq
    rw [slope_def_field, hz] at hs
    exact sub_nonneg.mp (by simpa using (div_le_iff₀ (sub_pos.mpr h)).mp hs)
  · exact hz.ge
  · have hs := hc.le_slope_of_hasDerivAt hq' hp h hdq
    rw [slope_def_field, hz, sub_zero] at hs
    exact by simpa using (le_div_iff₀ (sub_pos.mpr h)).mp hs

private theorem mul_log_div_eq (p : ℝ) {q : ℝ} (hq : 0 < q) :
    p * Real.log (p / q) = p * Real.log p - p * Real.log q := by
  by_cases h : p = 0
  · simp [h]
  · rw [Real.log_div h hq.ne', mul_sub]

private theorem toReal_klDiv_bool (μ ν : Measure Bool) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hac : μ ≪ ν) (hq : ν.real {true} ∈ Ioo 0 1) :
    (klDiv μ ν).toReal = binaryEntropy (μ.real {true}) (ν.real {true}) := by
  have hcomp : ({true} : Set Bool)ᶜ = {false} := by ext b; cases b <;> simp
  have hfalse (ρ : Measure Bool) [IsProbabilityMeasure ρ] :
      ρ.real {false} = 1 - ρ.real {true} := by
    rw [← hcomp, measureReal_compl (measurableSet_singleton true), probReal_univ]
  have hν (b : Bool) : 0 < ν.real {b} := by
    cases b
    · rw [hfalse]
      exact sub_pos.mpr hq.2
    · exact hq.1
  have hrn (b : Bool) : (μ.rnDeriv ν b).toReal = μ.real {b} / ν.real {b} := by
    have h := Measure.setIntegral_toReal_rnDeriv hac {b}
    rw [integral_singleton, smul_eq_mul] at h
    apply (eq_div_iff (hν b).ne').mpr
    simpa only [mul_comm] using h
  have hsets : ({true} : Set Bool) ∪ {false} = univ := by ext b; cases b <;> simp
  have hInt : Integrable (llr μ ν) μ := by
    rw [← integrableOn_univ, ← hsets, integrableOn_union]
    exact ⟨integrableOn_singleton, integrableOn_singleton⟩
  rw [toReal_klDiv_of_measure_eq hac ((measure_univ : μ univ = 1).trans (measure_univ : ν univ = 1).symm), integral_fintype hInt, Fintype.univ_bool]
  simp only [Finset.sum_insert, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
    Finset.sum_singleton, smul_eq_mul, llr, hrn]
  rw [mul_log_div_eq _ (hν true), mul_log_div_eq _ (hν false), hfalse μ, hfalse ν]
  unfold binaryEntropy
  ring

/-- For any measurable event, twice the squared difference of its
probabilities is at most the relative entropy of the two laws. -/
theorem event_difference_sq_le_klDiv {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {s : Set Ω} (hs : MeasurableSet s) :
    ENNReal.ofReal (2 * (μ.real s - ν.real s) ^ 2) ≤ klDiv μ ν := by
  classical
  by_cases htop : klDiv μ ν = ⊤
  · simp [htop]
  have hac := (klDiv_ne_top_iff.mp htop).1
  let p := μ.real s
  let q := ν.real s
  have hp : p ∈ Icc 0 1 :=
    ⟨measureReal_nonneg, (measureReal_mono (subset_univ s)).trans_eq probReal_univ⟩
  have hq : q ∈ Icc 0 1 :=
    ⟨measureReal_nonneg, (measureReal_mono (subset_univ s)).trans_eq probReal_univ⟩
  have hzero (h : q = 0) : p = q := by
    rw [h]
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mpr (hac ((measureReal_eq_zero_iff (measure_ne_top _ _)).mp h))
  have hone (h : q = 1) : p = q := by
    have hν : ν.real sᶜ = 0 := by rw [measureReal_compl hs, probReal_univ]; exact sub_eq_zero.mpr h.symm
    have hμ : μ.real sᶜ = 0 := (measureReal_eq_zero_iff (measure_ne_top _ _)).mpr (hac ((measureReal_eq_zero_iff (measure_ne_top _ _)).mp hν))
    rw [measureReal_compl hs, probReal_univ] at hμ
    exact (sub_eq_zero.mp hμ).symm.trans h.symm
  change ENNReal.ofReal (2 * (p - q) ^ 2) ≤ _
  by_cases hqi : q ∈ Ioo 0 1
  swap
  · have he : p = q := by
      rcases lt_or_eq_of_le hq.1 with h₀ | h₀
      · exact hone (le_antisymm hq.2 (le_of_not_gt (fun h => hqi ⟨h₀, h⟩)))
      · exact hzero h₀.symm
    simp [he]
  let b (x : Ω) := if x ∈ s then true else false
  have hbm : Measurable b := Measurable.ite hs measurable_const measurable_const
  have _ : IsProbabilityMeasure (μ.map b) := Measure.isProbabilityMeasure_map hbm.aemeasurable
  have _ : IsProbabilityMeasure (ν.map b) := Measure.isProbabilityMeasure_map hbm.aemeasurable
  have hb : b ⁻¹' ({true} : Set Bool) = s := by ext x; simp [b]
  have hmap (ρ : Measure Ω) : (ρ.map b).real {true} = ρ.real s := by
    rw [measureReal_def, Measure.map_apply hbm (measurableSet_singleton true), hb, measureReal_def]
  have hle := klDiv_map_le μ ν hbm
  have hfin : klDiv (μ.map b) (ν.map b) ≠ ⊤ := ne_of_lt (hle.trans_lt (lt_top_iff_ne_top.mpr htop))
  have hbin := toReal_klDiv_bool (μ.map b) (ν.map b) (hac.map hbm)
    (by rwa [hmap])
  rw [hmap, hmap] at hbin
  exact ((ENNReal.ofReal_le_ofReal (binaryEntropy_ge hp hqi)).trans_eq
    (by rw [← hbin, ENNReal.ofReal_toReal hfin])).trans hle

/-- Appending an observation adds relative entropy only on the histories
where the learner queries the auxiliary action whose response law changed. -/
theorem klDiv_compProd_changed_on {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {s : Set α} (hs : MeasurableSet s) [DecidablePred (· ∈ s)]
    (Q Q' : Measure β) [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
    (hac : Q ≪ Q') (other : Kernel α β) [IsMarkovKernel other] :
    klDiv (μ ⊗ₘ Kernel.piecewise hs (Kernel.const α Q) other)
        (ν ⊗ₘ Kernel.piecewise hs (Kernel.const α Q') other) =
      klDiv μ ν + klDiv Q Q' * μ s := by
  let κ := Kernel.piecewise hs (Kernel.const α Q) other
  let κ' := Kernel.piecewise hs (Kernel.const α Q') other
  let d (p : α × β) := if p.1 ∈ s then Q.rnDeriv Q' p.2 else 1
  have hm : Measurable d := Measurable.ite (measurable_fst hs)
    ((Measure.measurable_rnDeriv Q Q').comp measurable_snd) measurable_const
  have hDensity : (μ ⊗ₘ κ').withDensity d = μ ⊗ₘ κ := by
    ext z hz
    rw [withDensity_apply _ hz, ← lintegral_indicator hz, Measure.lintegral_compProd (hm.indicator hz),
      Measure.compProd_apply hz]
    apply lintegral_congr
    intro a
    have hz' : MeasurableSet (Prod.mk a ⁻¹' z) := measurable_prodMk_left hz
    have he : (fun b => z.indicator d (a, b)) =
        (Prod.mk a ⁻¹' z).indicator (fun b => d (a, b)) := rfl
    rw [he, lintegral_indicator hz']
    by_cases ha : a ∈ s
    · simpa [d, κ, κ', Kernel.piecewise_apply, ha] using
        Measure.setLIntegral_rnDeriv hac (Prod.mk a ⁻¹' z)
    · simp [d, κ, κ', Kernel.piecewise_apply, ha]
  have hJoint : μ ⊗ₘ κ ≪ μ ⊗ₘ κ' := by
    rw [← hDensity]
    exact withDensity_absolutelyContinuous _ _
  have hrn : (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ κ') =ᵐ[μ ⊗ₘ κ'] d := by
    rw [← hDensity]
    exact Measure.rnDeriv_withDensity _ hm
  have hKL : klDiv (μ ⊗ₘ κ) (μ ⊗ₘ κ') = klDiv Q Q' * μ s := by
    rw [klDiv_eq_lintegral_klFun_of_ac hJoint]
    have he : (∫⁻ x, ENNReal.ofReal (klFun ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ κ') x).toReal) ∂(μ ⊗ₘ κ')) =
        ∫⁻ x, ENNReal.ofReal (klFun (d x).toReal) ∂(μ ⊗ₘ κ') := by
      apply lintegral_congr_ae
      filter_upwards [hrn] with x hx
      rw [hx]
    rw [he, Measure.lintegral_compProd (by fun_prop : Measurable (fun x => ENNReal.ofReal (klFun (d x).toReal)))]
    rw [← lintegral_indicator_const hs, klDiv_eq_lintegral_klFun_of_ac hac]
    apply lintegral_congr
    intro a
    by_cases ha : a ∈ s
    · simp [d, κ', Kernel.piecewise_apply, ha]
    · simp [d, κ', Kernel.piecewise_apply, ha, klFun]
  rw [show klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ') =
    klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ κ') from klDiv_compProd_eq_add μ ν κ κ', hKL]

/-- Compare the expected numbers of plays of one action in two worlds.
Each event records whether the learner played that action in one round. -/
theorem expected_hits_le_of_klDiv {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : ι → Set Ω) (hs : ∀ i, MeasurableSet (s i))
    {D : ℝ} (hD : 0 ≤ D) (hkl : klDiv μ ν ≤ ENNReal.ofReal D) :
    (∑ i, ν.real (s i)) ≤ (∑ i, μ.real (s i)) + Fintype.card ι * Real.sqrt (D / 2) := by
  have hstep (i : ι) : ν.real (s i) ≤ μ.real (s i) + Real.sqrt (D / 2) := by
    have h := (event_difference_sq_le_klDiv μ ν (hs i)).trans hkl
    have hsq := (ENNReal.ofReal_le_ofReal_iff hD).mp h
    have hsqrt : ν.real (s i) - μ.real (s i) ≤ Real.sqrt (D / 2) :=
      Real.le_sqrt_of_sq_le (by nlinarith only [hsq])
    linarith only [hsqrt]
  simpa [Finset.sum_add_distrib] using Finset.sum_le_sum (s := (Finset.univ : Finset ι))
    (fun i _ => hstep i)

/-- The one-period count transfer in Lemma 4.8. Once the history divergence has
been bounded by the baseline count, this is the required comparison of play counts. -/
theorem expected_auxiliary_hits_le {Ω : Type*} [MeasurableSpace Ω] {R : ℕ}
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : Fin R → Set Ω) (hs : ∀ i, MeasurableSet (s i))
    {η : ℝ} (hη : 0 ≤ η)
    (hkl : klDiv μ ν ≤ ENNReal.ofReal (η ^ 2 / 3 * ∑ i, μ.real (s i))) :
    let baseline := ∑ i, μ.real (s i)
    (∑ i, ν.real (s i)) ≤ baseline + η * R * Real.sqrt (baseline / 6) := by
  intro baseline
  have hbase : 0 ≤ baseline := Finset.sum_nonneg fun _ _ => measureReal_nonneg
  have hD : 0 ≤ η ^ 2 / 3 * baseline := by positivity
  have h := expected_hits_le_of_klDiv μ ν s hs hD hkl
  rw [show η ^ 2 / 3 * baseline / 2 = η ^ 2 * (baseline / 6) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hη, Fintype.card_fin] at h
  linarith only [h, show (R : ℝ) * (η * Real.sqrt (baseline / 6)) =
    η * R * Real.sqrt (baseline / 6) by ring]

end CalibeatBandit

end

section

set_option autoImplicit false
set_option maxHeartbeats 150000

open Matrix MeasureTheory
open scoped BigOperators

namespace CalibeatBandit

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}

theorem measurable_select {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {a : Ω → α} (ha : Measurable a)
    {f : α → Ω → ℝ} (hf : ∀ i, Measurable (f i)) :
    Measurable (fun ω => f (a ω) ω) := by
  classical
  have heq : (fun ω => f (a ω) ω) =
      fun ω => ∑ i, if a ω = i then f i ω else 0 := by
    funext ω
    simp
  rw [heq]
  exact Finset.measurable_sum _ fun i _ => Measurable.ite (ha (measurableSet_singleton i)) (hf i) measurable_const

end Measurability

end CalibeatBandit

end

section

set_option autoImplicit false

open Filter MeasureTheory Matrix
open scoped BigOperators

namespace CalibeatBandit

/-- Averaging the one-period comparison between the baseline world and the
worlds with a selected auxiliary action. Here `baseline j` is the expected
number of plays of action j under the baseline law. -/
theorem auxiliary_average_le {M : ℕ} (hM : 0 < M) {period η : ℝ}
    (hperiod : 0 ≤ period) (hη : 0 ≤ η)
    (baseline selected : Fin M → ℝ) (hbase : ∀ j, 0 ≤ baseline j)
    (hcounts : (∑ j, baseline j) ≤ period)
    (hcompare : ∀ j, selected j ≤ baseline j + η * period * Real.sqrt (baseline j / 6)) :
    (∑ j, selected j) / M ≤ period / M + η * period * Real.sqrt (period / (6 * M)) := by
  have hM' : 0 < (M : ℝ) := by exact_mod_cast hM
  have hs : (∑ j, Real.sqrt (baseline j)) ≤ Real.sqrt (M * period) := by
    have h := Real.sum_sqrt_mul_sqrt_le (s := (Finset.univ : Finset (Fin M)))
      (f := baseline) (g := fun _ => 1) hbase (fun _ => zero_le_one)
    simp only [Real.sqrt_one, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at h
    calc
      _ ≤ Real.sqrt (∑ j, baseline j) * Real.sqrt M := by simpa only [mul_one] using h
      _ ≤ Real.sqrt period * Real.sqrt M :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hcounts) (Real.sqrt_nonneg _)
      _ = _ := by rw [mul_comm, ← Real.sqrt_mul hM'.le]
  have hall := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin M))) fun j _ => hcompare j
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, Real.sqrt_div (hbase _),
    ← Finset.sum_div] at hall
  calc
    _ ≤ (period + η * period * (Real.sqrt (M * period) / Real.sqrt 6)) / M := by
      apply div_le_div_of_nonneg_right _ hM'.le
      exact hall.trans (add_le_add hcounts (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hs (Real.sqrt_nonneg _)) (mul_nonneg hη hperiod)))
    _ = _ := by
      rw [add_div, mul_div_assoc, div_div, Real.sqrt_mul hM'.le,
        Real.sqrt_div hperiod, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6)]
      have hsM : (Real.sqrt M) ^ 2 = M := Real.sq_sqrt hM'.le
      have hpM : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM'
      have hp6 : 0 < Real.sqrt (6 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
      rw [← hsM]
      rw [Real.sqrt_sq hpM.le]
      field_simp

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal Function

/-- A one-period experiment for a designated auxiliary action. The query
event is determined by the transcript, and the two worlds use the same
observation kernel whenever this action is not queried. -/
structure AuxiliaryExperiment where
  query : (t : ℕ) → Set (FeedbackHistory t)
  measurable_query : ∀ t, MeasurableSet (query t)
  other : (t : ℕ) → Kernel (FeedbackHistory t) ℝ
  markov_other : ∀ t, IsMarkovKernel (other t)

namespace AuxiliaryExperiment

noncomputable def step (X : AuxiliaryExperiment) (Q : Measure ℝ) (t : ℕ) :
    Kernel (FeedbackHistory t) ℝ := by
  classical
  exact Kernel.piecewise (X.measurable_query t) (Kernel.const _ Q) (X.other t)

instance markov_step (X : AuxiliaryExperiment) (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (t : ℕ) : IsMarkovKernel (X.step Q t) := by
  classical
  let _ : IsMarkovKernel (X.other t) := X.markov_other t
  unfold step
  infer_instance

noncomputable def law (X : AuxiliaryExperiment) (Q : Measure ℝ) :
    (t : ℕ) → Measure (FeedbackHistory t)
  | 0 => Measure.dirac ()
  | t + 1 => X.law Q t ⊗ₘ X.step Q t

instance probability_law (X : AuxiliaryExperiment) (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (t : ℕ) : IsProbabilityMeasure (X.law Q t) := by
  induction t with
  | zero => change IsProbabilityMeasure (Measure.dirac ()); infer_instance
  | succ t ih =>
    let _ := ih
    change IsProbabilityMeasure (X.law Q t ⊗ₘ X.step Q t)
    infer_instance

/-- In a transcript of length r, this event records the learner's action
in round i, which depends only on the observations before round i. -/
def hit (X : AuxiliaryExperiment) : (r : ℕ) → Fin r → Set (FeedbackHistory r)
  | 0, i => Fin.elim0 i
  | r + 1, i => Fin.lastCases (Prod.fst ⁻¹' X.query r) (fun j => Prod.fst ⁻¹' X.hit r j) i

theorem measurable_hit (X : AuxiliaryExperiment) (r : ℕ) (i : Fin r) :
    MeasurableSet (X.hit r i) := by
  induction r with
  | zero => exact Fin.elim0 i
  | succ r ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hit, Fin.lastCases_last]
      exact measurable_fst (X.measurable_query r)
    · rw [hit, Fin.lastCases_castSucc]
      exact measurable_fst (ih j)

private theorem measure_of_preimage_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α β) [IsMarkovKernel κ]
    (s : Set α) (hs : MeasurableSet s) :
    (μ ⊗ₘ κ) (Prod.fst ⁻¹' s) = μ s := by
  rw [← Measure.map_apply measurable_fst hs, ← Measure.fst, Measure.fst_compProd]

theorem law_hit (X : AuxiliaryExperiment) (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (r : ℕ) (i : Fin r) :
    X.law Q r (X.hit r i) = X.law Q i (X.query i) := by
  induction r with
  | zero => exact Fin.elim0 i
  | succ r ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hit, Fin.lastCases_last, Fin.val_last]
      exact measure_of_preimage_fst (X.law Q r) (X.step Q r)
        (X.query r) (X.measurable_query r)
    · rw [hit, Fin.lastCases_castSucc, Fin.val_castSucc]
      exact (measure_of_preimage_fst (X.law Q r) (X.step Q r) (X.hit r j)
        (X.measurable_hit r j)).trans (ih j)

/-- The transcript divergence is the one-observation divergence times the
expected number of times the changed action is queried in the baseline world. -/
theorem klDiv_law (X : AuxiliaryExperiment) (Q Q' : Measure ℝ)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure Q'] (hac : Q ≪ Q') (r : ℕ) :
    klDiv (X.law Q r) (X.law Q' r) =
      klDiv Q Q' * ∑ i : Fin r, X.law Q r (X.hit r i) := by
  induction r with
  | zero =>
    rw [Fin.sum_univ_zero, mul_zero]
    exact klDiv_self (X.law Q 0)
  | succ r ih =>
    classical
    let _ : IsMarkovKernel (X.other r) := X.markov_other r
    have h := klDiv_compProd_changed_on (X.law Q r) (X.law Q' r)
      (X.measurable_query r) Q Q' hac (X.other r)
    calc
      _ = klDiv (X.law Q r) (X.law Q' r) + klDiv Q Q' * X.law Q r (X.query r) := h
      _ = _ := by
        rw [ih, ← mul_add]
        congr 1
        simp only [law_hit]
        rw [Fin.sum_univ_castSucc]
        simp

/-- Lemma 4.8's one-period comparison for a single auxiliary action. -/
theorem bonus_hit_bound (X : AuxiliaryExperiment) {η : ℝ} (hη : 0 ≤ η) (hη₁ : η < 1)
    (r : ℕ) :
    let Q : Measure ℝ := volume.restrict (Icc 0 1)
    let Q' := Q.map (bonusTransform η)
    let baseline := ∑ i : Fin r, (X.law Q r).real (X.hit r i)
    (∑ i : Fin r, (X.law Q' r).real (X.hit r i)) ≤
      baseline + η * r * Real.sqrt (baseline / 6) := by
  intro Q Q' baseline
  have _ : IsProbabilityMeasure Q := ⟨by simp [Q, Real.volume_Icc]⟩
  have hm : Measurable (bonusTransform η) := by unfold bonusTransform; fun_prop
  have _ : IsProbabilityMeasure Q' := Measure.isProbabilityMeasure_map hm.aemeasurable
  have hbonus : klDiv Q Q' ≤ ENNReal.ofReal (η ^ 2 / 3) := lemma_4_7 hη hη₁
  have hfin : klDiv Q Q' ≠ ⊤ := ne_of_lt (hbonus.trans_lt ENNReal.ofReal_lt_top)
  have hac := (klDiv_ne_top_iff.mp hfin).1
  apply expected_auxiliary_hits_le (X.law Q r) (X.law Q' r) (X.hit r) (X.measurable_hit r) hη
  rw [X.klDiv_law Q Q' hac, ENNReal.ofReal_mul (by positivity : 0 ≤ η ^ 2 / 3),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => measureReal_nonneg)]
  simp_rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  gcongr

/-- Two experiments with the same observation kernels have the same law. -/
theorem law_eq_of_step_eq (X Y : AuxiliaryExperiment) (Q : Measure ℝ)
    (h : ∀ t, X.step Q t = Y.step Q t) (r : ℕ) : X.law Q r = Y.law Q r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change X.law Q r ⊗ₘ X.step Q r = Y.law Q r ⊗ₘ Y.step Q r
    rw [ih, h]

end AuxiliaryExperiment

/-- A period with a fixed private seed. The learner's action is a
measurable function of the reward transcript in that period. -/
structure AuxiliaryPeriod (K M : ℕ) where
  pick : (t : ℕ) → FeedbackHistory t → Fin K
  measurable_pick : ∀ t, Measurable (pick t)
  aux : Fin M ↪ Fin K
  base : (t : ℕ) → Kernel (FeedbackHistory t) ℝ
  markov_base : ∀ t, IsMarkovKernel (base t)

namespace AuxiliaryPeriod

def experiment {K M : ℕ} (A : AuxiliaryPeriod K M) (j : Fin M) : AuxiliaryExperiment where
  query := fun t => A.pick t ⁻¹' {A.aux j}
  measurable_query := fun t => A.measurable_pick t (measurableSet_singleton _)
  other := A.base
  markov_other := A.markov_base

theorem step_base {K M : ℕ} (A : AuxiliaryPeriod K M) (Q : Measure ℝ)
    (hbase : ∀ t h j, A.pick t h = A.aux j → A.base t h = Q) (j : Fin M) (t : ℕ) :
    (A.experiment j).step Q t = A.base t := by
  classical
  ext h s hs
  rw [AuxiliaryExperiment.step, Kernel.piecewise_apply']
  by_cases he : A.pick t h = A.aux j
  · simp [experiment, he, hbase t h j he]
  · simp [experiment, he]

/-- If each auxiliary action gives a base-law observation in the baseline
world, a uniform choice of the bonus action yields the one-period bound
from Lemma 4.8. -/
theorem average_bonus_hits_le {K M : ℕ} (A : AuxiliaryPeriod K M) (hM : 0 < M)
    (r : ℕ) {η : ℝ} (hη : 0 ≤ η) (hη₁ : η < 1) :
    let Q : Measure ℝ := volume.restrict (Icc 0 1)
    let Q' := Q.map (bonusTransform η)
    (∀ t h j, A.pick t h = A.aux j → A.base t h = Q) →
    (∑ j : Fin M, ∑ i : Fin r, ((A.experiment j).law Q' r).real ((A.experiment j).hit r i)) / M
      ≤ (r : ℝ) / M + η * r * Real.sqrt ((r : ℝ) / (6 * M)) := by
  intro Q Q' hbase
  let j₀ : Fin M := ⟨0, hM⟩
  let baseline (j : Fin M) := ∑ i : Fin r, ((A.experiment j).law Q r).real ((A.experiment j).hit r i)
  let selected (j : Fin M) := ∑ i : Fin r, ((A.experiment j).law Q' r).real ((A.experiment j).hit r i)
  have _ : IsProbabilityMeasure Q := ⟨by simp [Q, Real.volume_Icc]⟩
  have hnonneg (j : Fin M) : 0 ≤ baseline j := Finset.sum_nonneg fun _ _ => measureReal_nonneg
  have hbaseline (j : Fin M) (t : ℕ) : (A.experiment j).law Q t = (A.experiment j₀).law Q t :=
    AuxiliaryExperiment.law_eq_of_step_eq _ _ Q
      (fun u => (A.step_base Q hbase j u).trans (A.step_base Q hbase j₀ u).symm) t
  have hmass (i : Fin r) :
      (∑ j : Fin M, ((A.experiment j₀).law Q i).real ((A.experiment j).query i)) ≤ 1 := by
    let μ := (A.experiment j₀).law Q i
    let s := fun j => (A.experiment j).query i
    have hd : Pairwise (Disjoint on s) := by
      intro j k hjk
      refine Set.disjoint_left.mpr fun h hj hk => hjk ?_
      apply A.aux.injective
      exact ((Set.mem_singleton_iff.mp hj).symm.trans (Set.mem_singleton_iff.mp hk))
    rw [← measureReal_iUnion_fintype (μ := μ) hd (fun j => (A.experiment j).measurable_query i)]
    exact (measureReal_mono (subset_univ _)).trans_eq probReal_univ
  have hcounts : (∑ j, baseline j) ≤ (r : ℝ) := by
    have he (j : Fin M) (i : Fin r) :
        ((A.experiment j).law Q r).real ((A.experiment j).hit r i) =
        ((A.experiment j₀).law Q i).real ((A.experiment j).query i) := by
      rw [measureReal_def, (A.experiment j).law_hit Q r i, hbaseline, measureReal_def]
    simp only [baseline, he]
    rw [Finset.sum_comm]
    simpa using Finset.sum_le_sum (s := (Finset.univ : Finset (Fin r))) (fun i _ => hmass i)
  exact auxiliary_average_le hM (Nat.cast_nonneg r) hη baseline selected hnonneg hcounts
    (fun j => (A.experiment j).bonus_hit_bound hη hη₁ r)

end AuxiliaryPeriod

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open Set MeasureTheory

theorem treeBonusProb_mem {h M U : ℕ} (leaf : Fin (2 ^ h))
    (coin : TreeNode h → Bool) (leafCoin : Bool) (selected : Fin M) (a : TreeAction h M U) :
    treeBonusProb leaf coin leafCoin selected a ∈ Icc (0 : ℝ) 1 := by
  have hz : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have h₁ : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  rcases a with ⟨v, side⟩ | (j | j)
  · have hdepth : (v.1 : ℕ) ≤ h := Nat.le_of_lt_succ v.1.isLt
    have hd : ((v.1 : ℕ) : ℝ) ≤ h := by exact_mod_cast hdepth
    have hh : 0 < treeHeight h := by unfold treeHeight; positivity
    have hfrac : (((v.1 : ℕ) + 1 : ℝ) / (2 * treeHeight h)) ∈ Icc 0 1 := by
      refine ⟨by positivity, (div_le_one (by positivity)).mpr ?_⟩
      unfold treeHeight
      linarith
    simp only [treeBonusProb]
    split_ifs <;> assumption
  · simp only [treeBonusProb]
    split <;> assumption
  · exact hz

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The normalized observation uses the bonus transform exactly when the
independent threshold draw falls below the current bonus probability. -/
noncomputable def observationLaw (η u : ℝ) : Measure ℝ :=
  let Q : Measure ℝ := volume.restrict (Icc 0 1)
  ENNReal.ofReal (1 - u) • Q + ENNReal.ofReal u • Q.map (bonusTransform η)

theorem observationLaw_probability (η : ℝ) {u : ℝ} (hu : u ∈ Icc 0 1) :
    IsProbabilityMeasure (observationLaw η u) := by
  let Q : Measure ℝ := volume.restrict (Icc 0 1)
  have _ : IsProbabilityMeasure Q := ⟨by simp [Q, Real.volume_Icc]⟩
  have hm : Measurable (bonusTransform η) := by unfold bonusTransform; fun_prop
  have _ : IsProbabilityMeasure (Q.map (bonusTransform η)) := Measure.isProbabilityMeasure_map hm.aemeasurable
  refine ⟨?_⟩
  change (ENNReal.ofReal (1 - u) • Q + ENNReal.ofReal u • Q.map (bonusTransform η)) univ = 1
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hu.2) hu.1]
  simp

theorem map_threshold_observation (η : ℝ) {u : ℝ} (hu : u ∈ Icc 0 1) :
    let Q : Measure ℝ := volume.restrict (Icc 0 1)
    let V : Measure ℝ := volume.restrict (Ico 0 1)
    (V.prod Q).map (fun p : ℝ × ℝ => if p.1 < u then bonusTransform η p.2 else p.2) =
      observationLaw η u := by
  intro Q V
  let f (p : ℝ × ℝ) := if p.1 < u then bonusTransform η p.2 else p.2
  have hb : Measurable (bonusTransform η) := by unfold bonusTransform; fun_prop
  have hm : Measurable f := Measurable.ite (measurableSet_lt measurable_fst measurable_const)
    (hb.comp measurable_snd) measurable_snd
  have _ : IsProbabilityMeasure Q := ⟨by simp [Q, Real.volume_Icc]⟩
  have hlow : V (Iio u) = ENNReal.ofReal u := by
    rw [show V = volume.restrict (Ico 0 1) from rfl, Measure.restrict_apply measurableSet_Iio]
    have he : Iio u ∩ Ico (0 : ℝ) 1 = Ico 0 u := by
      ext x
      simp only [mem_inter_iff, mem_Iio, mem_Ico]
      exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.trans_le hu.2⟩⟩
    rw [he, Real.volume_Ico, sub_zero]
  have hhigh : V (Ici u) = ENNReal.ofReal (1 - u) := by
    rw [show V = volume.restrict (Ico 0 1) from rfl, Measure.restrict_apply measurableSet_Ici]
    have he : Ici u ∩ Ico (0 : ℝ) 1 = Ico u 1 := by
      ext x
      simp only [mem_inter_iff, mem_Ici, mem_Ico]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hu.1.trans h.1, h.2⟩⟩
    rw [he, Real.volume_Ico]
  ext s hs
  change ((V.prod Q).map f) s = _
  rw [Measure.map_apply hm hs, Measure.prod_apply (hm hs)]
  let F := (Iio u).indicator (fun _ : ℝ => Q (bonusTransform η ⁻¹' s))
  let G := (Ici u).indicator (fun _ : ℝ => Q s)
  have he (w : ℝ) : Q (Prod.mk w ⁻¹' (f ⁻¹' s)) = F w + G w := by
    by_cases hw : w < u
    · have heq : Prod.mk w ⁻¹' (f ⁻¹' s) = bonusTransform η ⁻¹' s := by
        ext z
        simp [f, hw]
      simp [heq, F, G, hw, not_le_of_gt hw]
    · have heq : Prod.mk w ⁻¹' (f ⁻¹' s) = s := by
        ext z
        simp [f, hw]
      simp [heq, F, G, hw, le_of_not_gt hw]
  rw [lintegral_congr he, lintegral_add_left (measurable_const.indicator measurableSet_Iio)]
  change (∫⁻ w, F w ∂V) + (∫⁻ w, G w ∂V) = _
  rw [lintegral_indicator_const measurableSet_Iio, lintegral_indicator_const measurableSet_Ici,
    hlow, hhigh]
  simp only [observationLaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply hb hs]
  change _ = ENNReal.ofReal (1 - u) * Q s + ENNReal.ofReal u * Q (bonusTransform η ⁻¹' s)
  ac_rfl

/-- The baseline observation kernel with every auxiliary bonus turned off. -/
noncomputable def treeAuxiliaryPeriod {h M U N : ℕ}
    (e : Fin N ≃ TreeAction h M U) (η : ℝ) (leaf : Fin (2 ^ h))
    (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool) (dummy : Fin M)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N)
    (hm : ∀ t, Measurable (pick t)) : AuxiliaryPeriod N M := by
  let u (t : ℕ) (i : Fin N) : ℝ :=
    match e i with
    | .inr (.inl _) => 0
    | a => treeBonusProb leaf coin (leafCoin t) dummy a
  have hu (t : ℕ) (i : Fin N) : u t i ∈ Icc (0 : ℝ) 1 := by
    unfold u
    split
    · exact ⟨le_rfl, zero_le_one⟩
    · apply treeBonusProb_mem
  let kernel (t : ℕ) : Kernel (Fin N) ℝ :=
    Kernel.ofFunOfCountable (fun i => observationLaw η (u t i))
  have hk (t : ℕ) : IsMarkovKernel (kernel t) :=
    ⟨fun i => observationLaw_probability η (hu t i)⟩
  exact ⟨pick, hm, ⟨fun j => e.symm (.inr (.inl j)), by
      intro i j hij
      have he := e.symm.injective hij
      injection he with he
      injection he⟩,
    fun t => (kernel t).comap (pick t) (hm t),
    fun t => by
      let _ := hk t
      infer_instance⟩

/-- The selected-world kernel agrees with the actual tree reward law for
every action at every history. -/
theorem treeAuxiliaryPeriod_selected_step {h M U N : ℕ}
    (e : Fin N ≃ TreeAction h M U) (η : ℝ) (leaf : Fin (2 ^ h))
    (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool) (dummy j : Fin M)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N)
    (hm : ∀ t, Measurable (pick t)) (t : ℕ) (x : FeedbackHistory t) :
    let A := treeAuxiliaryPeriod e η leaf coin leafCoin dummy pick hm
    let Q := volume.restrict (Icc (0 : ℝ) 1)
    (A.experiment j).step (Q.map (bonusTransform η)) t x =
      observationLaw η (treeBonusProb leaf coin (leafCoin t) j (e (pick t x))) := by
  classical
  intro A Q
  rw [AuxiliaryExperiment.step, Kernel.piecewise_apply]
  have hr : x ∈ (A.experiment j).query t ↔ e (pick t x) = .inr (.inl j) := by
    change pick t x = e.symm (.inr (.inl j)) ↔ _
    rw [Equiv.eq_symm_apply]
  simp only [hr]
  cases he : e (pick t x) with
  | inl a =>
    simp [he, A, treeAuxiliaryPeriod, AuxiliaryPeriod.experiment, Kernel.comap_apply,
      Kernel.ofFunOfCountable, treeBonusProb]
  | inr b =>
    cases b with
    | inl k =>
      by_cases hk : k = j
      · subst k
        simp [treeBonusProb, observationLaw, Q, Kernel.const_apply]
      · simp [he, hk, A, treeAuxiliaryPeriod, AuxiliaryPeriod.experiment, Kernel.comap_apply,
          Kernel.ofFunOfCountable, treeBonusProb, observationLaw]
    | inr k =>
      simp [he, A, treeAuxiliaryPeriod, AuxiliaryPeriod.experiment, Kernel.comap_apply,
        Kernel.ofFunOfCountable, treeBonusProb, observationLaw]

/-- The bound on the expected number of hits within a period of the actual
tree construction, for any fixed values of the tree and leaf coins. -/
theorem tree_period_average_hits {h M U N : ℕ}
    (e : Fin N ≃ TreeAction h M U) (η : ℝ) (hη : 0 ≤ η) (hη₁ : η < 1)
    (leaf : Fin (2 ^ h)) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool) (dummy : Fin M)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t))
    (r : ℕ) :
    let A := treeAuxiliaryPeriod e η leaf coin leafCoin dummy pick hm
    let Q := volume.restrict (Icc (0 : ℝ) 1)
    let Q' := Q.map (bonusTransform η)
    (∑ j : Fin M, ∑ i : Fin r, ((A.experiment j).law Q' r).real ((A.experiment j).hit r i)) / M
      ≤ (r : ℝ) / M + η * r * Real.sqrt ((r : ℝ) / (6 * M)) := by
  intro A Q Q'
  refine A.average_bonus_hits_le (Nat.zero_lt_of_lt dummy.isLt) r hη hη₁ ?_
  intro t x j hx
  have hx' : pick t x = e.symm (.inr (.inl j)) := hx
  have he := congrArg e hx'
  simp only [Equiv.apply_symm_apply] at he
  change (Kernel.ofFunOfCountable (fun i =>
    observationLaw η (match e i with
      | .inr (.inl _) => 0
      | a => treeBonusProb leaf coin (leafCoin t) dummy a))) (pick t x) = Q
  simp [Kernel.ofFunOfCountable, he, observationLaw, Q]

/-- A round uses one common base draw and an independent threshold draw
for each action. This is the normalized reward for one action. -/
noncomputable def observedReward {N : ℕ} (η u : ℝ) (i : Fin N)
    (p : ℝ × (Fin N → ℝ)) : ℝ :=
  if p.2 i < u then bonusTransform η p.1 else p.1

theorem measurable_observedReward {N : ℕ} (η u : ℝ) (i : Fin N) :
    Measurable (observedReward η u i) := by
  have hm : Measurable (bonusTransform η) := by unfold bonusTransform; fun_prop
  exact Measurable.ite (measurableSet_lt ((measurable_pi_apply i).comp measurable_snd) measurable_const)
    (hm.comp measurable_fst) measurable_fst

theorem map_observedReward {N : ℕ} (η : ℝ) {u : ℝ} (hu : u ∈ Icc 0 1) (i : Fin N) :
    let Q : Measure ℝ := volume.restrict (Icc 0 1)
    let V : Measure ℝ := volume.restrict (Ico 0 1)
    let tape := Q.prod (Measure.pi fun _ : Fin N => V)
    tape.map (observedReward η u i) = observationLaw η u := by
  intro Q V tape
  have _ : IsProbabilityMeasure Q := ⟨by simp [Q, Real.volume_Icc]⟩
  have _ : IsProbabilityMeasure V := ⟨by simp [V, Real.volume_Ico]⟩
  let τ : Measure (Fin N → ℝ) := Measure.pi fun _ : Fin N => V
  let get (r : Fin N → ℝ) := r i
  have hg : Measurable get := measurable_pi_apply i
  have hmap : τ.map get = V := (measurePreserving_eval (fun _ : Fin N => V) i).map_eq
  have hp : (Q.prod τ).map (Prod.map id get) = Q.prod V := by
    rw [← Measure.map_prod_map _ _ measurable_id hg, Measure.map_id, hmap]
  let f (p : ℝ × ℝ) := if p.1 < u then bonusTransform η p.2 else p.2
  have hb : Measurable (bonusTransform η) := by unfold bonusTransform; fun_prop
  have hf : Measurable f := Measurable.ite (measurableSet_lt measurable_fst measurable_const)
    (hb.comp measurable_snd) measurable_snd
  change (Q.prod τ).map ((f ∘ Prod.swap) ∘ Prod.map id get) = _
  rw [← Measure.map_map (hf.comp measurable_swap) (measurable_id.prodMap hg), hp,
    ← Measure.map_map hf measurable_swap, Measure.prod_swap]
  exact map_threshold_observation η hu

/-- The next transcript is obtained by appending the observation from an
independent draw. This describes the same law as the observation kernel. -/
theorem map_product_append {A B H Y : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace H] [MeasurableSpace Y] (μ : Measure A) (ν : Measure B)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (past : A → H) (hp : Measurable past)
    (observe : H × B → Y) (ho : Measurable observe)
    (κ : Kernel H Y) [IsMarkovKernel κ]
    (hk : ∀ x, κ x = ν.map (fun b => observe (x, b))) :
    (μ.prod ν).map (fun x : A × B => (past x.1, observe (past x.1, x.2))) =
      μ.map past ⊗ₘ κ := by
  let f (x : A × B) := (past x.1, observe (past x.1, x.2))
  have hm : Measurable f :=
    (hp.comp measurable_fst).prodMk (ho.comp ((hp.comp measurable_fst).prodMk measurable_snd))
  ext s hs
  change ((μ.prod ν).map f) s = _
  rw [Measure.map_apply hm hs, Measure.prod_apply (hm hs), Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hp]
  apply lintegral_congr
  intro a
  rw [hk]
  have hx : Measurable (fun b => observe (past a, b)) := ho.comp measurable_prodMk_left
  rw [Measure.map_apply hx (measurable_prodMk_left hs)]
  rfl

noncomputable def observationOfHistory {N t : ℕ} (η : ℝ) (u : Fin N → ℝ)
    (pick : FeedbackHistory t → Fin N) (p : FeedbackHistory t × (ℝ × (Fin N → ℝ))) : ℝ :=
  observedReward η (u (pick p.1)) (pick p.1) p.2

theorem measurable_observationOfHistory {N t : ℕ} (η : ℝ) (u : Fin N → ℝ)
    (pick : FeedbackHistory t → Fin N) (hm : Measurable pick) :
    Measurable (observationOfHistory η u pick) :=
  measurable_select (hm.comp measurable_fst)
    fun i => (measurable_observedReward η (u i) i).comp measurable_snd

noncomputable def transcriptFromTape {N : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) :
    (t : ℕ) → RewardTape N t → FeedbackHistory t
  | 0, _ => ()
  | t + 1, p =>
    let past := transcriptFromTape η u pick t p.1
    (past, observationOfHistory η (u t) (pick t) (past, p.2))

theorem measurable_transcriptFromTape {N : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t))
    (r : ℕ) : Measurable (transcriptFromTape η u pick r) := by
  induction r with
  | zero => exact measurable_const
  | succ r ih =>
    change Measurable (fun p : RewardTape N r × (ℝ × (Fin N → ℝ)) =>
      (transcriptFromTape η u pick r p.1,
        observationOfHistory η (u r) (pick r) (transcriptFromTape η u pick r p.1, p.2)))
    have hp : Measurable (fun p : RewardTape N r × (ℝ × (Fin N → ℝ)) =>
        transcriptFromTape η u pick r p.1) := ih.comp measurable_fst
    exact hp.prodMk ((measurable_observationOfHistory η (u r) (pick r) (hm r)).comp
      (hp.prodMk measurable_snd))

set_option maxHeartbeats 850000 in
/-- The product law of the complete reward tape induces the observation
kernel law in each selected world of the lower bound. -/
theorem treeAuxiliaryPeriod_law_eq_map {h M U N : ℕ}
    (e : Fin N ≃ TreeAction h M U) (η : ℝ) (leaf : Fin (2 ^ h))
    (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool) (dummy j : Fin M)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N)
    (hm : ∀ t, Measurable (pick t)) (r : ℕ) :
    let A := treeAuxiliaryPeriod e η leaf coin leafCoin dummy pick hm
    let Q := volume.restrict (Icc (0 : ℝ) 1)
    let u (t : ℕ) (i : Fin N) := treeBonusProb leaf coin (leafCoin t) j (e i)
    (rewardTapeLaw N r).map (transcriptFromTape η u pick r) =
      (A.experiment j).law (Q.map (bonusTransform η)) r := by
  intro A Q u
  have _ : IsProbabilityMeasure Q := ⟨by simp [Q, Real.volume_Icc]⟩
  have hη : Measurable (bonusTransform η) := by unfold bonusTransform; fun_prop
  have _ : IsProbabilityMeasure (Q.map (bonusTransform η)) := Measure.isProbabilityMeasure_map hη.aemeasurable
  let X := A.experiment j
  induction r with
  | zero =>
    change (Measure.dirac ((): Unit)).map (fun _ : Unit => ()) = Measure.dirac ()
    exact Measure.map_dirac' (measurable_const : Measurable (fun _ : Unit => ())) ()
  | succ r ih =>
    let κ := X.step (Q.map (bonusTransform η)) r
    have hk (x : FeedbackHistory r) :
        κ x = (roundDrawLaw N).map (fun b => observationOfHistory η (u r) (pick r) (x, b)) := by
      have hu := treeBonusProb_mem (U := U) leaf coin (leafCoin r) j (e (pick r x))
      exact (treeAuxiliaryPeriod_selected_step e η leaf coin leafCoin dummy j pick hm r x).trans
        (map_observedReward η hu (pick r x)).symm
    have hnext := map_product_append (rewardTapeLaw N r) (roundDrawLaw N)
      (transcriptFromTape η u pick r) (measurable_transcriptFromTape η u pick hm r)
      (observationOfHistory η (u r) (pick r)) (measurable_observationOfHistory η (u r) (pick r) (hm r))
      κ hk
    rw [ih] at hnext
    exact hnext

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set

@[simp] theorem rewardTapePrefix_refl (N r : ℕ) :
    rewardTapePrefix N (le_refl r) = id := by simp [rewardTapePrefix]

@[simp] theorem rewardTapePrefix_succ (N : ℕ) {r t : ℕ} (h : r ≤ t) :
    rewardTapePrefix N (Nat.le_succ_of_le h) = rewardTapePrefix N h ∘ Prod.fst := by
  unfold rewardTapePrefix
  exact Nat.leRec_succ _ _ h

theorem measurable_rewardTapePrefix (N : ℕ) {r t : ℕ} (h : r ≤ t) :
    Measurable (rewardTapePrefix N h) := by
  induction h with
  | refl => rw [rewardTapePrefix_refl]; exact measurable_id
  | step h ih => rw [rewardTapePrefix_succ N h]; exact ih.comp measurable_fst

theorem rewardTapePrefix_map (N : ℕ) {r t : ℕ} (h : r ≤ t) :
    (rewardTapeLaw N t).map (rewardTapePrefix N h) = rewardTapeLaw N r := by
  induction h with
  | refl => rw [rewardTapePrefix_refl, Measure.map_id]
  | step h ih =>
    rw [rewardTapePrefix_succ N h]
    change ((rewardTapeLaw N _).prod (roundDrawLaw N)).map
      (rewardTapePrefix N h ∘ Prod.fst) = _
    rw [← Measure.map_map (measurable_rewardTapePrefix N h) measurable_fst, Measure.map_fst_prod,
      measure_univ, one_smul, ih]

open scoped ENNReal

theorem measurable_supportedBase : Measurable fun x => (supportedBase x : ℝ) := by
  have he : (fun x => (supportedBase x : ℝ)) = fun x => if x ∈ Icc (0 : ℝ) 1 then x else 0 := by
    funext x
    by_cases hx : x ∈ Icc (0 : ℝ) 1 <;> simp [supportedBase, hx]
  rw [he]
  exact Measurable.ite measurableSet_Icc measurable_id measurable_const

theorem measurable_supportedThreshold : Measurable fun x => (supportedThreshold x : ℝ) := by
  have he : (fun x => (supportedThreshold x : ℝ)) = fun x => if x ∈ Ico (0 : ℝ) 1 then x else 0 := by
    funext x
    by_cases hx : x ∈ Ico (0 : ℝ) 1 <;> simp [supportedThreshold, hx]
  rw [he]
  exact Measurable.ite measurableSet_Ico measurable_id measurable_const

theorem measurable_boundedRoundReward {N : ℕ} (η u : ℝ) (i : Fin N) :
    Measurable (boundedRoundReward η u i) := by
  let z (d : ℝ × (Fin N → ℝ)) : ℝ := supportedBase d.1
  have hz : Measurable z := measurable_supportedBase.comp measurable_fst
  have hth := measurable_supportedThreshold.comp ((measurable_pi_apply i).comp
    (measurable_snd : Measurable (Prod.snd : ℝ × (Fin N → ℝ) → (Fin N → ℝ))))
  unfold boundedRoundReward bonusReward
  simp only [decide_eq_true_eq]
  exact (measurable_const.add (hz.div_const _)).add
    (((hz.const_mul _).mul (measurable_const.sub hz)).mul
      (Measurable.ite (measurableSet_lt hth measurable_const) measurable_const measurable_const))

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set

theorem measurable_boundedObservation {N : ℕ} (η u : ℝ) (i : Fin N) :
    Measurable (boundedObservation η u i) :=
  ((measurable_boundedRoundReward η u i).const_mul _).sub measurable_const

theorem boundedObservation_ae {N : ℕ} (η u : ℝ) (i : Fin N) :
    boundedObservation η u i =ᵐ[roundDrawLaw N] observedReward η u i := by
  let Q : Measure ℝ := volume.restrict (Icc 0 1)
  let V : Measure ℝ := volume.restrict (Ico 0 1)
  have _ : IsProbabilityMeasure Q := ⟨by simp [Q, Real.volume_Icc]⟩
  have _ : IsProbabilityMeasure V := ⟨by simp [V, Real.volume_Ico]⟩
  let τ : Measure (Fin N → ℝ) := Measure.pi fun _ : Fin N => V
  have hbase : ∀ᵐ d ∂roundDrawLaw N, d.1 ∈ Icc (0 : ℝ) 1 := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    change ∀ᵐ d ∂(Q.prod τ).map Prod.fst, d ∈ Icc (0 : ℝ) 1
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact ae_restrict_mem measurableSet_Icc
  have hth : ∀ᵐ d ∂roundDrawLaw N, d.2 i ∈ Ico (0 : ℝ) 1 := by
    apply ae_of_ae_map ((measurable_pi_apply i).comp measurable_snd).aemeasurable
    change ∀ᵐ d ∂(Q.prod τ).map ((fun r => r i) ∘ Prod.snd), d ∈ Ico (0 : ℝ) 1
    rw [← Measure.map_map (measurable_pi_apply i) measurable_snd, Measure.map_snd_prod,
      measure_univ, one_smul, (measurePreserving_eval (fun _ : Fin N => V) i).map_eq]
    exact ae_restrict_mem measurableSet_Ico
  filter_upwards [hbase, hth] with d hz hd
  unfold boundedObservation boundedRoundReward bonusReward observedReward bonusTransform
  simp only [supportedBase, supportedThreshold, dif_pos hz, dif_pos hd, decide_eq_true_eq]
  split <;> ring

theorem measurable_boundedTapeTranscript {N : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t))
    (r : ℕ) : Measurable (boundedTapeTranscript η u pick r) := by
  induction r with
  | zero => exact measurable_const
  | succ r ih =>
    change Measurable (fun p : RewardTape N r × (ℝ × (Fin N → ℝ)) =>
      (boundedTapeTranscript η u pick r p.1,
        boundedObservation η (u r (pick r (boundedTapeTranscript η u pick r p.1)))
          (pick r (boundedTapeTranscript η u pick r p.1)) p.2))
    exact (ih.comp measurable_fst).prodMk
      (measurable_select ((hm r).comp (ih.comp measurable_fst)) fun i =>
        (measurable_boundedObservation η (u r i) i).comp measurable_snd)

theorem boundedTapeTranscript_ae {N : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (r : ℕ) :
    boundedTapeTranscript η u pick r =ᵐ[rewardTapeLaw N r] transcriptFromTape η u pick r := by
  induction r with
  | zero => exact Filter.EventuallyEq.rfl
  | succ r ih =>
    let μ := rewardTapeLaw N r
    let ν := roundDrawLaw N
    have hs : ∀ᵐ d ∂ν, ∀ i : Fin N,
        boundedObservation η (u r i) i d = observedReward η (u r i) i d :=
      ae_all_iff.mpr fun i => boundedObservation_ae η (u r i) i
    have hs' : ∀ᵐ p ∂μ.prod ν, ∀ i : Fin N,
        boundedObservation η (u r i) i p.2 = observedReward η (u r i) i p.2 :=
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hs
    have hf' : ∀ᵐ p ∂μ.prod ν,
        boundedTapeTranscript η u pick r p.1 = transcriptFromTape η u pick r p.1 :=
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae ih
    change ∀ᵐ p ∂μ.prod ν,
      boundedTapeTranscript η u pick (r + 1) p = transcriptFromTape η u pick (r + 1) p
    filter_upwards [hf', hs'] with p hf hs
    change boundedTapeTranscript η u pick r p.1 = transcriptFromTape η u pick r p.1 at hf
    change ∀ i : Fin N, boundedObservation η (u r i) i p.2 = observedReward η (u r i) i p.2 at hs
    simp only [boundedTapeTranscript, transcriptFromTape, observationOfHistory]
    rw [hf, hs]

private theorem measurable_playHit {A : Type*} [MeasurableSpace A] {N : ℕ} {a : A → Fin N}
    (ha : Measurable a) (j : Fin N) : Measurable fun x => if a x = j then (1 : ℝ) else 0 :=
  Measurable.ite (measurableSet_eq_fun ha measurable_const) measurable_const measurable_const

theorem integral_periodHits {h M U N : ℕ}
    (e : Fin N ≃ TreeAction h M U) (η : ℝ) (leaf : Fin (2 ^ h))
    (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool) (dummy j : Fin M)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t))
    (r : ℕ) :
    let u (t : ℕ) (i : Fin N) := treeBonusProb leaf coin (leafCoin t) j (e i)
    let A := treeAuxiliaryPeriod e η leaf coin leafCoin dummy pick hm
    let Q' := (volume.restrict (Icc (0 : ℝ) 1)).map (bonusTransform η)
    (∫ tape, periodHits η u pick (e.symm (.inr (.inl j))) r tape ∂rewardTapeLaw N r) =
      ∑ i : Fin r, ((A.experiment j).law Q' r).real ((A.experiment j).hit r i) := by
  classical
  intro u A Q'
  have hη : Measurable (bonusTransform η) := by unfold bonusTransform; fun_prop
  have _ : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp [Real.volume_Icc]⟩
  have _ : IsProbabilityMeasure Q' := Measure.isProbabilityMeasure_map hη.aemeasurable
  let X := A.experiment j
  let target := e.symm (.inr (.inl j))
  let f (i : Fin r) (x : FeedbackHistory i) : ℝ := if pick i x = target then 1 else 0
  have hf (i : Fin r) : Measurable (f i) := measurable_playHit (hm i) target
  let pre (i : Fin r) := rewardTapePrefix N i.isLt.le
  let tr (i : Fin r) := boundedTapeTranscript η u pick i
  have htr (i : Fin r) : Measurable (tr i) := measurable_boundedTapeTranscript η u pick hm i
  have hpre (i : Fin r) : Measurable (pre i) := measurable_rewardTapePrefix N i.isLt.le
  let g (i : Fin r) (tape : RewardTape N r) := f i (tr i (pre i tape))
  have hg (i : Fin r) : Integrable (g i) (rewardTapeLaw N r) := by
    apply Integrable.of_bound ((hf i).comp ((htr i).comp (hpre i))).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro x
    change ‖g i x‖ ≤ 1
    unfold g f
    split <;> simp
  change (∫ x, ∑ i, g i x ∂rewardTapeLaw N r) = ∑ i : Fin r, (X.law Q' r).real (X.hit r i)
  rw [integral_finsetSum _ (fun i _ => hg i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hmap :
      (rewardTapeLaw N i).map (tr i) = X.law Q' i :=
    (Measure.map_congr (boundedTapeTranscript_ae η u pick i)).trans
      (treeAuxiliaryPeriod_law_eq_map e η leaf coin leafCoin dummy j pick hm i)
  have htarget : f i = (X.query i).indicator (fun _ => (1 : ℝ)) := by
    funext x
    have he : x ∈ X.query i ↔ pick i x = target := Iff.rfl
    simp only [f, Set.indicator, he]
  calc
    _ = ∫ x, f i (tr i x) ∂rewardTapeLaw N i := by
      have he := integral_map (μ := rewardTapeLaw N r) (hpre i).aemeasurable ((hf i).comp (htr i)).aestronglyMeasurable
      rw [show (rewardTapeLaw N r).map (pre i) = rewardTapeLaw N i from rewardTapePrefix_map N i.isLt.le] at he
      exact he.symm
    _ = ∫ x, f i x ∂X.law Q' i := by
      have he := integral_map (μ := rewardTapeLaw N i) (htr i).aemeasurable (hf i).aestronglyMeasurable
      rw [hmap] at he
      exact he.symm
    _ = (X.law Q' i).real (X.query i) := by
      rw [htarget]
      exact integral_indicator_one (X.measurable_query i)
    _ = _ := congrArg ENNReal.toReal (X.law_hit Q' r i).symm

/-- The one-period bound in terms of the actual independent reward draws. -/
theorem integral_periodHits_average_le {h M U N : ℕ}
    (e : Fin N ≃ TreeAction h M U) (η : ℝ) (hη : 0 ≤ η) (hη₁ : η < 1)
    (leaf : Fin (2 ^ h)) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool) (dummy : Fin M)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t)) (r : ℕ) :
    let u (j : Fin M) (t : ℕ) (i : Fin N) := treeBonusProb leaf coin (leafCoin t) j (e i)
    (∑ j : Fin M, ∫ tape, periodHits η (u j) pick (e.symm (.inr (.inl j))) r tape ∂rewardTapeLaw N r) / M
      ≤ (r : ℝ) / M + η * r * Real.sqrt ((r : ℝ) / (6 * M)) := by
  intro u
  have he (j : Fin M) :
      (∫ tape, periodHits η (u j) pick (e.symm (.inr (.inl j))) r tape ∂rewardTapeLaw N r) =
        ∑ i : Fin r, ((treeAuxiliaryPeriod e η leaf coin leafCoin dummy pick hm).experiment j |> fun X => (X.law ((volume.restrict (Icc (0 : ℝ) 1)).map (bonusTransform η)) r).real
            (X.hit r i)) :=
    integral_periodHits e η leaf coin leafCoin dummy j pick hm r
  rw [Finset.sum_congr rfl (fun j _ => he j)]
  exact tree_period_average_hits e η hη hη₁ leaf coin leafCoin dummy pick hm r

end CalibeatBandit

end

theorem solution : type_of% @CalibeatBandit.integral_periodHits_average_le := @CalibeatBandit.integral_periodHits_average_le
