-- Prove2me | solution 1 for ComplementFreeCA.CFRounding.eventB_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:23:16.369755+00:00
-- url     : https://prove2.me/submissions/31303e03-f561-48c5-98ff-9e7dd9bb1281

import Definitions.Def_ComplementFreeCA_CFRounding_LP
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory
open ComplementFreeCA.CFRounding Finset
private noncomputable def finiteLaw {α : Type*} [Fintype α] (p : α → ℝ)
    (h0 : ∀ a, 0 ≤ p a) (h1 : ∑ a, p a = 1) : PMF α :=
  PMF.ofFintype (fun a => ENNReal.ofReal (p a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a ha => h0 a), h1]; simp)

private theorem finiteLaw_real {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : α → ℝ) (h0 : ∀ a, 0 ≤ p a) (h1 : ∑ a, p a = 1) (a : α) :
    (finiteLaw p h0 h1).toMeasure.real {a} = p a := by
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
  exact ENNReal.toReal_ofReal (h0 a)

private theorem finiteLaw_integral {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : α → ℝ) (h0 : ∀ a, 0 ≤ p a) (h1 : ∑ a, p a = 1) (f : α → ℝ) :
    (∫ a, f a ∂(finiteLaw p h0 h1).toMeasure) = ∑ a, p a * f a := by
  rw [integral_fintype .of_finite]
  simp [finiteLaw_real]

private theorem law_nonneg {n m : ℕ} (x : Fin n → Finset (Fin m) → ℝ) (hx : IsLPFeasible x) :
    ∀ i S, 0 ≤ roundLaw x i S := by
  intro i S
  unfold roundLaw
  split_ifs <;> linarith [hx.2.2 i S, hx.2.1 i]

private theorem law_sum {n m : ℕ} (x : Fin n → Finset (Fin m) → ℝ) :
    ∀ i, ∑ S, roundLaw x i S = 1 := by
  classical
  intro i
  simp [roundLaw, sum_add_distrib]

private theorem pi_real {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : ι → α → ℝ) (h0 : ∀ i a, 0 ≤ p i a) (h1 : ∀ i, ∑ a, p i a = 1) (σ : ι → α) :
    (Measure.pi (fun i => (finiteLaw (p i) (h0 i) (h1 i)).toMeasure)).real {σ} = ∏ i, p i (σ i) := by
  rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  apply prod_congr rfl
  intro i hi
  exact finiteLaw_real _ _ _ _

open Classical in
private theorem pi_prob {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : ι → α → ℝ) (h0 : ∀ i a, 0 ≤ p i a) (h1 : ∀ i, ∑ a, p i a = 1) (E : (ι → α) → Prop) :
    (Measure.pi (fun i => (finiteLaw (p i) (h0 i) (h1 i)).toMeasure)).real {σ | E σ} =
      ∑ σ, if E σ then ∏ i, p i (σ i) else 0 := by
  classical
  let μ := Measure.pi (fun i => (finiteLaw (p i) (h0 i) (h1 i)).toMeasure)
  have he : μ.real {σ | E σ} = ∫ σ, Set.indicator {σ | E σ} (fun _ => (1:ℝ)) σ ∂μ := by
    rw [integral_indicator_const (1:ℝ) (Set.toFinite _).measurableSet]
    simp
  rw [he, integral_fintype .of_finite]
  apply sum_congr rfl
  intro σ hσ
  change μ.real {σ} * _ = _
  rw [show μ.real {σ} = ∏ i, p i (σ i) from pi_real p h0 h1 σ]
  by_cases h : E σ <;> simp [Set.indicator,h]

private theorem pi_integral_coord {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : ι → α → ℝ) (h0 : ∀ i a, 0 ≤ p i a) (h1 : ∀ i, ∑ a, p i a = 1) (i : ι) (f : α → ℝ) :
    (∫ σ, f (σ i) ∂(Measure.pi (fun i => (finiteLaw (p i) (h0 i) (h1 i)).toMeasure))) =
      ∑ a, p i a * f a := by
  rw [← integral_map (measurable_pi_apply i).aemeasurable (by fun_prop),
    (measurePreserving_eval (fun i => (finiteLaw (p i) (h0 i) (h1 i)).toMeasure) i).map_eq]
  exact finiteLaw_integral _ _ _ _

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hmono : ∀ i, IsMonotone (v i))
    (x : Fin n → Finset (Fin m) → ℝ) (hx : IsLPFeasible x)
    (hlarge : ∀ i, 3 * v i Finset.univ < lpValue v x) :
    roundProb x (fun σ => welfare v σ < lpValue v x / 3) < 3 / 4 := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [roundProb,welfare,lpValue]
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  obtain ⟨i₀, hi₀, hmax⟩ := exists_max_image univ (fun i : Fin n => v i univ) univ_nonempty
  let B := v i₀ univ
  have hv0 : ∀ i S, 0 ≤ v i S := by
    intro i S
    have h := hmono i ∅ S (empty_subset S)
    simpa [show v i ∅ = 0 from hnorm i] using h
  have hvB : ∀ i S, v i S ≤ B := by
    intro i S
    exact (hmono i S univ (subset_univ S)).trans (hmax i (mem_univ _))
  have hB0 : 0 ≤ B := hv0 i₀ _
  have hL0 : 0 < lpValue v x := by linarith [hlarge i₀]
  letI : MeasurableSpace (Finset (Fin m)) := ⊤
  let p := roundLaw x
  have hp0 := law_nonneg x hx
  have hp1 := law_sum x
  let μ := Measure.pi (fun i => (finiteLaw (p i) (hp0 i) (hp1 i)).toMeasure)
  let X := fun (i : Fin n) (σ : Fin n → Finset (Fin m)) => v i (σ i)
  have hLp : ∀ i, MemLp (X i) 2 μ := fun i => memLp_of_bounded
    (Filter.Eventually.of_forall (fun σ => show X i σ ∈ Set.Icc 0 B from ⟨hv0 i _,hvB i _⟩))
    (by fun_prop) 2
  have hInt : ∀ i, Integrable (X i) μ := fun i => (hLp i).integrable (by norm_num)
  have hind : iIndepFun X μ := iIndepFun_pi
    (μ := fun i => (finiteLaw (p i) (hp0 i) (hp1 i)).toMeasure)
    (X := v) (fun i => by fun_prop)
  have hE : (∫ σ, welfare v σ ∂μ) = lpValue v x := by
    unfold welfare lpValue
    rw [integral_finsetSum univ (fun i hi => hInt i)]
    apply sum_congr rfl
    intro i hi
    rw [pi_integral_coord p hp0 hp1 i]
    apply sum_congr rfl
    intro S hS
    by_cases hS0 : S = ∅
    · subst S
      simp [show v i ∅ = 0 from hnorm i]
    · simp [p,roundLaw,hS0]
  have hsLp : MemLp (welfare v) 2 μ := memLp_finsetSum univ (fun i hi => hLp i)
  have hvar : variance (welfare v) μ ≤ B * lpValue v x := by
    have he : variance (welfare v) μ = ∑ i, variance (X i) μ := by
      have hf : welfare v = ∑ i, X i := by funext σ; simp [welfare,X]
      rw [hf]
      exact IndepFun.variance_sum (s := univ) (fun i hi => hLp i)
        (fun i hi j hj hne => hind.indepFun hne)
    have hei : (∑ i, ∫ σ, X i σ ∂μ) = lpValue v x := by
      rw [← integral_finsetSum univ (fun i hi => hInt i)]
      exact hE
    rw [he, ← hei, mul_sum]
    apply sum_le_sum
    intro i hi
    rw [variance_eq_sub (hLp i)]
    have hsq : (∫ σ, (X i σ)^2 ∂μ) ≤ B * ∫ σ, X i σ ∂μ := by
      rw [← integral_const_mul]
      apply integral_mono (hLp i).integrable_sq ((hInt i).const_mul _)
      intro σ
      have h0 := hv0 i (σ i)
      have h1 := hvB i (σ i)
      change v i (σ i)^2 ≤ B * v i (σ i)
      nlinarith
    change (∫ σ, (X i σ)^2 ∂μ) - (∫ σ, X i σ ∂μ)^2 ≤ B * ∫ σ, X i σ ∂μ
    nlinarith [sq_nonneg (∫ σ, X i σ ∂μ)]
  have hα : 0 < 2 * lpValue v x / 3 := by positivity
  have hc := meas_ge_le_variance_div_sq hsLp hα
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ μ) (sq_nonneg _)),hE] at hr
  have hsub : μ.real {σ | welfare v σ < lpValue v x / 3} ≤
      μ.real {σ | 2*lpValue v x/3 ≤ |welfare v σ-lpValue v x|} := by
    refine measureReal_mono ?_
    intro σ hσ
    change welfare v σ < lpValue v x/3 at hσ
    change 2*lpValue v x/3 ≤ |welfare v σ-lpValue v x|
    rw [abs_of_neg (by linarith)]
    linarith
  have hprob : μ.real {σ | welfare v σ < lpValue v x / 3} =
      roundProb x (fun σ => welfare v σ < lpValue v x / 3) := pi_prob p hp0 hp1 _
  rw [← hprob]
  apply lt_of_le_of_lt (hsub.trans (hr.trans (div_le_div_of_nonneg_right hvar (sq_nonneg _))))
  apply (div_lt_iff₀ (sq_pos_of_pos hα)).mpr
  have hstrict := mul_lt_mul_of_pos_right (hlarge i₀) hL0
  change 3*B*lpValue v x < lpValue v x*lpValue v x at hstrict
  nlinarith
