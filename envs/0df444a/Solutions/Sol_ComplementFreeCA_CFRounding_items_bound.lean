-- Prove2me | solution 1 for ComplementFreeCA.CFRounding.items_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:26:26.256984+00:00
-- url     : https://prove2.me/submissions/23239659-5ccf-413d-bfdb-ad51d6757ca6

import Definitions.Def_ComplementFreeCA_CFRounding_LP
import Definitions.Def_ComplementFreeCA_CFRounding_Algorithm
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory
universe u

private theorem bernoulli_tail :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ (N : ℕ) (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : Fin N → Ω → ℝ),
        (∀ i, Measurable (X i)) → iIndepFun X μ →
        (∀ i ω, X i ω = 0 ∨ X i ω = 1) →
        ∑ i, μ.real {ω | X i ω = 1} ≤ 1 →
        μ.real {ω | 3 * Real.log m / Real.log (Real.log m) < ∑ i, X i ω} ≤ 1 / (m : ℝ) ^ 2 := by
  classical
  obtain ⟨m₀,hm₀⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨m₀, ?_⟩
  intro m hm N Ω _ μ _ X hmeas hind hrange hsum
  have hmexp : Real.exp 1 < (m:ℝ) := hm₀.trans_le (by exact_mod_cast hm)
  have hmpos : (0:ℝ) < m := (Real.exp_pos 1).trans hmexp
  have hlog : 1 < Real.log m := (Real.lt_log_iff_exp_lt hmpos).mpr hmexp
  have hlogpos : 0 < Real.log m := by linarith
  let t := Real.log (Real.log m)
  have ht : 0 < t := Real.log_pos hlog
  let ε := 3 * Real.log m / t
  let S := fun ω => ∑ i, X i ω
  let p := fun i => μ.real {ω | X i ω = 1}
  have hX0 : ∀ i ω, 0 ≤ X i ω := by intro i ω; rcases hrange i ω with h | h <;> simp [h]
  have hX1 : ∀ i ω, X i ω ≤ 1 := by intro i ω; rcases hrange i ω with h | h <;> simp [h]
  have hInt : ∀ i, Integrable (X i) μ := by
    intro i
    apply Integrable.of_bound (hmeas i).aestronglyMeasurable 1
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hX0 i ω)]
    exact hX1 i ω
  have hEX : ∀ i, (∫ ω, X i ω ∂μ) = p i := by
    intro i
    have he : X i = Set.indicator {ω | X i ω = 1} (fun _ => (1:ℝ)) := by
      funext ω
      rcases hrange i ω with h | h <;> simp [Set.indicator,h]
    rw [he, integral_indicator_const (1:ℝ) (measurableSet_eq_fun (hmeas i) measurable_const)]
    simp [p]
  have hp0 : ∀ i, 0 ≤ p i := by intro i; dsimp [p]; positivity
  have hcoef : 0 ≤ Real.exp t - 1 := sub_nonneg.mpr (Real.one_le_exp ht.le)
  have hmgf : ∀ i, mgf (X i) μ t = 1 + p i * (Real.exp t - 1) := by
    intro i
    have he : (fun ω => Real.exp (t*X i ω)) = (fun ω => 1+(Real.exp t-1)*X i ω) := by
      funext ω
      rcases hrange i ω with h | h <;> simp [h] <;> ring
    unfold mgf
    rw [he, integral_add (integrable_const 1) ((hInt i).const_mul _), integral_const_mul, hEX i]
    simp
    ring
  have hmgfle : ∀ i, mgf (X i) μ t ≤ Real.exp (p i*(Real.exp t-1)) := by
    intro i
    rw [hmgf]
    simpa [add_comm] using Real.add_one_le_exp (p i*(Real.exp t-1))
  have hprod : (∏ i, mgf (X i) μ t) ≤ Real.exp (Real.exp t-1) := by
    calc
      _ ≤ ∏ i, Real.exp (p i*(Real.exp t-1)) := Finset.prod_le_prod
        (fun i hi => by rw [hmgf]; positivity) (fun i hi => hmgfle i)
      _ = Real.exp ((∑ i, p i)*(Real.exp t-1)) := by rw [← Real.exp_sum, Finset.sum_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hSmeas : Measurable S := by dsimp [S]; fun_prop
  have hSle : ∀ ω, S ω ≤ (N:ℝ) := by
    intro ω
    calc
      _ ≤ ∑ i : Fin N, (1:ℝ) := Finset.sum_le_sum (fun i hi => hX1 i ω)
      _ = _ := by simp
  have hExpInt : Integrable (fun ω => Real.exp (t*S ω)) μ := by
    apply Integrable.of_bound ((hSmeas.const_mul t).exp.aestronglyMeasurable) (Real.exp (t*N))
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hSle ω) ht.le)
  have hSfun : S = ∑ i, X i := by funext ω; simp [S]
  have hmgfS : mgf S μ t = ∏ i, mgf (X i) μ t := by
    rw [hSfun]
    exact hind.mgf_sum hmeas Finset.univ
  have htail := measure_ge_le_exp_mul_mgf ε ht.le hExpInt
  rw [hmgfS] at htail
  have hbound : Real.exp (-t*ε) * Real.exp (Real.exp t-1) ≤ 1/(m:ℝ)^2 := by
    calc
      _ ≤ Real.exp (-t*ε) * Real.exp (Real.exp t) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
      _ = Real.exp (-(2*Real.log m)) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [t,ε]
        rw [Real.exp_log hlogpos]
        have ht0 : Real.log (Real.log (m:ℝ)) ≠ 0 := ne_of_gt ht
        field_simp [ht0]
        <;> ring
      _ = _ := by
        rw [Real.exp_neg]
        have he : Real.exp (2*Real.log m) = (m:ℝ)^2 := by
          rw [show 2*Real.log m = Real.log m+Real.log m by ring, Real.exp_add, Real.exp_log hmpos]
          ring
        rw [he, one_div]
  have hsub : μ.real {ω | ε < S ω} ≤ μ.real {ω | ε ≤ S ω} := measureReal_mono (by intro ω h; change ε ≤ S ω; change ε < S ω at h; exact h.le)
  exact hsub.trans (htail.trans ((mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le).trans hbound))

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

theorem solution :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (n : ℕ) (x : Fin n → Finset (Fin m) → ℝ), IsLPFeasible x →
      (∀ j : Fin m, roundProb x
          (fun σ => 3 * Real.log m / Real.log (Real.log m) < (count σ j : ℝ)) ≤ 1 / (m : ℝ) ^ 2) ∧
      roundProb x
          (fun σ => ∃ j : Fin m, 3 * Real.log m / Real.log (Real.log m) < (count σ j : ℝ))
        ≤ 1 / (m : ℝ) := by
  classical
  obtain ⟨m₀,hm₀⟩ := bernoulli_tail.{0}
  refine ⟨max m₀ 1, ?_⟩
  intro m hm n x hx
  letI : MeasurableSpace (Finset (Fin m)) := ⊤
  let p := roundLaw x
  have hp0 := law_nonneg x hx
  have hp1 := law_sum x
  let μ := Measure.pi (fun i => (finiteLaw (p i) (hp0 i) (hp1 i)).toMeasure)
  let ε := 3 * Real.log m / Real.log (Real.log m)
  have hprob (E : (Fin n → Finset (Fin m)) → Prop) : μ.real {σ | E σ} = roundProb x E :=
    pi_prob p hp0 hp1 E
  have hjbound : ∀ j : Fin m, μ.real {σ | ε < (count σ j : ℝ)} ≤ 1/(m:ℝ)^2 := by
    intro j
    let X := fun (i : Fin n) (σ : Fin n → Finset (Fin m)) => if j ∈ σ i then (1:ℝ) else 0
    have hind : iIndepFun X μ := iIndepFun_pi
      (μ := fun i => (finiteLaw (p i) (hp0 i) (hp1 i)).toMeasure)
      (X := fun (_ : Fin n) (S : Finset (Fin m)) => if j ∈ S then (1:ℝ) else 0) (fun i => by fun_prop)
    have hexpect (i : Fin n) : μ.real {σ | X i σ = 1} =
        ∑ S ∈ univ.filter (fun S : Finset (Fin m) => j ∈ S), x i S := by
      have he : {σ | X i σ = 1} = {σ | j ∈ σ i} := by ext σ; simp [X]
      have heint : μ.real {σ | j ∈ σ i} = ∫ σ, Set.indicator {σ | j ∈ σ i} (fun _ => (1:ℝ)) σ ∂μ := by
        rw [integral_indicator_const (1:ℝ) (Set.toFinite _).measurableSet]
        simp
      rw [he,heint]
      have hindicator : Set.indicator {σ : Fin n → Finset (Fin m) | j ∈ σ i} (fun _ => (1:ℝ)) =
          fun σ => if j ∈ σ i then (1:ℝ) else 0 := by funext σ; simp [Set.indicator]
      rw [hindicator, pi_integral_coord p hp0 hp1 i (fun S => if j ∈ S then (1:ℝ) else 0)]
      simp only [sum_filter]
      apply sum_congr rfl
      intro S hS
      by_cases hj : j ∈ S
      · have hS0 : S ≠ ∅ := by intro he; simpa [he] using hj
        simp [p,roundLaw,hj,hS0]
      · simp [hj]
    have hcount (σ : Fin n → Finset (Fin m)) : (count σ j : ℝ) = ∑ i, X i σ := by
      simp only [count, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, X]
    simp_rw [hcount]
    exact hm₀ m ((le_max_left _ _).trans hm) n _ μ X (by intro i; fun_prop) hind
      (by intro i σ; by_cases h : j ∈ σ i <;> simp [X,h]) (by simp_rw [hexpect]; exact hx.1 j)
  refine ⟨?_, ?_⟩
  · intro j
    rw [← hprob]
    exact hjbound j
  · rw [← hprob]
    have hset : {σ : Fin n → Finset (Fin m) | ∃ j : Fin m, ε < (count σ j : ℝ)} = ⋃ j : Fin m, {σ | ε < (count σ j : ℝ)} := by
      ext σ; simp
    rw [hset]
    calc
      _ ≤ ∑ j : Fin m, μ.real {σ | ε < (count σ j : ℝ)} := measureReal_iUnion_fintype_le _
      _ ≤ ∑ j : Fin m, 1/(m:ℝ)^2 := sum_le_sum (fun j hj => hjbound j)
      _ = 1/(m:ℝ) := by
        have hmpos : (0:ℝ) < m := by exact_mod_cast ((le_max_right m₀ 1).trans hm)
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
