-- Prove2me | solution 1 for ComplementFreeCA.CFRounding.cf_rounding_approximation
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:27:12.984263+00:00
-- url     : https://prove2.me/submissions/9be56baf-d80e-499f-8852-ced6cc12652f

import Definitions.Def_ComplementFreeCA_CFRounding_LP
import Definitions.Def_ComplementFreeCA_CFRounding_Algorithm
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.Variance
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

private theorem items_bound :
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

private theorem eventB_bound {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
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

private theorem rank_strict {n m : ℕ} (σ : Fin n → Finset (Fin m)) (j : Fin m)
    {i i' : Fin n} (hi : j ∈ σ i) (hii' : i < i') :
    (univ.filter fun l => l < i ∧ j ∈ σ l).card < (univ.filter fun l => l < i' ∧ j ∈ σ l).card := by
  apply card_lt_card
  apply ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro l hl
    simp only [mem_filter, mem_univ, true_and] at hl ⊢
    exact ⟨hl.1.trans hii', hl.2⟩
  · intro he
    have hmem : i ∈ univ.filter fun l => l < i' ∧ j ∈ σ l := by simp [hii', hi]
    rw [← he] at hmem
    simpa using hmem

private theorem rank_bound {n m : ℕ} (σ : Fin n → Finset (Fin m)) (j : Fin m)
    (i : Fin n) (hi : j ∈ σ i) :
    (univ.filter fun l => l < i ∧ j ∈ σ l).card < count σ j := by
  apply card_lt_card
  apply ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro l hl
    simp only [mem_filter, mem_univ, true_and] at hl ⊢
    exact hl.2
  · intro he
    have hmem : i ∈ univ.filter fun l => j ∈ σ l := by simp [hi]
    rw [← he] at hmem
    simpa using hmem

private theorem layers_partition {n m : ℕ} (σ : Fin n → Finset (Fin m)) (k : ℕ)
    (hcount : ∀ j, count σ j ≤ k) :
    (∀ r : ℕ, 1 ≤ r → r ≤ k → IsAllocation (fun i => layer σ i r)) ∧
    (∀ i : Fin n, σ i = (Finset.Icc 1 k).biUnion (fun r => layer σ i r)) ∧
    (∀ (i : Fin n) (r r' : ℕ), 1 ≤ r → 1 ≤ r' → r ≠ r' →
      Disjoint (layer σ i r) (layer σ i r')) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr hrk i i' hne
    apply disjoint_left.mpr
    intro j hj hj'
    simp only [layer, mem_filter] at hj hj'
    rcases lt_or_gt_of_ne hne with h | h
    · have := rank_strict σ j hj.1 h
      omega
    · have := rank_strict σ j hj'.1 h
      omega
  · intro i
    ext j
    simp only [mem_biUnion, mem_Icc]
    constructor
    · intro hj
      let q := (univ.filter fun l => l < i ∧ j ∈ σ l).card
      refine ⟨q+1, ⟨by omega, ?_⟩, ?_⟩
      · have h := rank_bound σ j i hj
        have hc := hcount j
        omega
      · simp [layer, hj, q]
    · rintro ⟨r, hr, hj⟩
      exact (mem_filter.mp hj).1
  · intro i r r' hr hr' hne
    apply disjoint_left.mpr
    intro j hj hj'
    simp only [layer, mem_filter] at hj hj'
    omega

private theorem sum_layers {n m : ℕ} (v : Finset (Fin m) → ℝ) (hnorm : IsNormalized v)
    (hsub : IsSubadditive v) (σ : Fin n → Finset (Fin m)) (k : ℕ)
    (hcount : ∀ j, count σ j ≤ k) (i : Fin n) :
    v (σ i) ≤ ∑ r ∈ Finset.Icc 1 k, v (layer σ i r) := by
  have hgen : ∀ s : Finset ℕ, v (s.biUnion (layer σ i)) ≤ ∑ r ∈ s, v (layer σ i r) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa only [biUnion_empty, sum_empty] using le_of_eq hnorm
    | @insert r s hr ih =>
      rw [biUnion_insert, sum_insert hr]
      exact (hsub _ _).trans (add_le_add le_rfl ih)
  rw [(layers_partition σ k hcount).2.1 i]
  exact hgen _

private theorem best_layer_bound {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hsub : ∀ i, IsSubadditive (v i))
    (x : Fin n → Finset (Fin m) → ℝ) (σ : Fin n → Finset (Fin m)) (k : ℕ) (hk : 1 ≤ k)
    (hcount : ∀ j, count σ j ≤ k) (hval : lpValue v x / 3 ≤ welfare v σ)
    (r : ℕ) (hr : IsBestLayer v σ k r) :
    lpValue v x / (3 * k) ≤ welfare v (fun i => layer σ i r) := by
  have htotal : welfare v σ ≤ ∑ q ∈ Finset.Icc 1 k, welfare v (fun i => layer σ i q) := by
    unfold welfare
    rw [sum_comm]
    exact sum_le_sum (fun i hi => sum_layers _ (hnorm i) (hsub i) σ k hcount i)
  have hmax : (∑ q ∈ Finset.Icc 1 k, welfare v (fun i => layer σ i q)) ≤
      (k:ℝ) * welfare v (fun i => layer σ i r) := by
    calc
      _ ≤ ∑ q ∈ Finset.Icc 1 k, welfare v (fun i => layer σ i r) :=
        sum_le_sum (fun q hq => hr.2.2 q (mem_Icc.mp hq).1 (mem_Icc.mp hq).2)
      _ = _ := by simp
  have hkR : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 3*k)).mpr
  nlinarith

private theorem opt_le_lp {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (x : Fin n → Finset (Fin m) → ℝ) (hx : IsOptimalLP v x)
    (O : Fin n → Finset (Fin m)) (hO : IsAllocation O) :
    welfare v O ≤ lpValue v x := by
  classical
  let y : Fin n → Finset (Fin m) → ℝ := fun i S => if S = O i then 1 else 0
  have hy : IsLPFeasible y := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      simp only [y, sum_ite_eq', mem_filter, mem_univ, true_and]
      by_cases he : ∃ i, j ∈ O i
      · obtain ⟨i, hi⟩ := he
        have hother : ∀ i' ≠ i, j ∉ O i' := by
          intro i' hne hj
          exact disjoint_left.mp (hO i' i hne) hj hi
        rw [sum_eq_single i]
        · simp [hi]
        · intro i' hi' hne
          simp [hother i' hne]
        · simp
      · simp only [not_exists] at he
        simp [he]
    · intro i
      simp [y]
    · intro i S
      simp only [y]
      split_ifs <;> norm_num
  have heq : lpValue v y = welfare v O := by
    simp [lpValue, welfare, y, ite_mul]
  rw [← heq]
  exact hx.2 y hy

private theorem all_to_one_alloc {n m : ℕ} (i₀ : Fin n) :
    IsAllocation (fun i : Fin n => if i = i₀ then (univ : Finset (Fin m)) else ∅) := by
  classical
  intro i j hij
  by_cases hi : i = i₀ <;> by_cases hj : j = i₀ <;> simp_all

private theorem all_to_one_welfare {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (i₀ : Fin n) :
    welfare v (fun i : Fin n => if i = i₀ then univ else ∅) = v i₀ univ := by
  classical
  unfold welfare
  rw [sum_eq_single i₀]
  · simp
  · intro i hi hne
    simp [hne,show v i ∅ = 0 from hnorm i]
  · simp

theorem solution :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (n : ℕ) (v : Fin n → Finset (Fin m) → ℝ),
      (∀ i, IsNormalized (v i)) → (∀ i, IsMonotone (v i)) → (∀ i, IsSubadditive (v i)) →
      ∀ x : Fin n → Finset (Fin m) → ℝ, IsOptimalLP v x →
        -- (a) step (i) succeeds with probability greater than 1/6
        ((∀ i, 3 * v i Finset.univ < lpValue v x) →
          1 / 6 < roundProb x
            (fun σ => (∀ j, count σ j ≤ kOf m) ∧ lpValue v x / 3 ≤ welfare v σ)) ∧
        -- (b) from any such preallocation, every admissible run of steps (ii)–(iv) outputs
        --     an allocation whose welfare is at least OPT / (3k)
        (∀ σ : Fin n → Finset (Fin m), (∀ j, count σ j ≤ kOf m) →
          lpValue v x / 3 ≤ welfare v σ →
          ∀ r : ℕ, IsBestLayer v σ (kOf m) r →
          ∀ i₀ : Fin n, IsStepFourChoice v (fun i => layer σ i r) i₀ →
            IsAllocation (algOutput v σ r i₀) ∧
            ∀ O : Fin n → Finset (Fin m), IsAllocation O →
              welfare v O / (3 * kOf m) ≤ welfare v (algOutput v σ r i₀)) ∧
        -- (c) the small case: giving all items to a bidder maximizing vᵢ(M) is a
        --     3-approximation
        (∀ i₀ : Fin n, (∀ i, v i Finset.univ ≤ v i₀ Finset.univ) →
          lpValue v x ≤ 3 * v i₀ Finset.univ →
          ∀ O : Fin n → Finset (Fin m), IsAllocation O → welfare v O / 3 ≤ v i₀ Finset.univ) := by
  classical
  obtain ⟨m₀, hm₀⟩ := items_bound
  obtain ⟨m₁, hm₁⟩ := exists_nat_gt (max (Real.exp 1) (12:ℝ))
  refine ⟨max m₀ m₁, ?_⟩
  intro m hm n v hnorm hmono hsub x hx
  have hm₁m : (m₁:ℝ) ≤ m := by exact_mod_cast (le_max_right m₀ m₁).trans hm
  have hmexp : Real.exp 1 < (m:ℝ) := (le_max_left _ _).trans_lt (hm₁.trans_le hm₁m)
  have hm12 : (12:ℝ) < m := (le_max_right _ _).trans_lt (hm₁.trans_le hm₁m)
  have hmpos : (0:ℝ) < m := by linarith
  have hlog : 1 < Real.log m := (Real.lt_log_iff_exp_lt hmpos).mpr hmexp
  have hloglog : 0 < Real.log (Real.log m) := Real.log_pos hlog
  let ε := 3 * Real.log m / Real.log (Real.log m)
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  refine ⟨?_, ?_, ?_⟩
  · intro hlarge
    letI : MeasurableSpace (Finset (Fin m)) := ⊤
    let p := roundLaw x
    have hp0 := law_nonneg x hx.1
    have hp1 := law_sum x
    let μ := Measure.pi (fun i => (finiteLaw (p i) (hp0 i) (hp1 i)).toMeasure)
    have hprob (E : (Fin n → Finset (Fin m)) → Prop) : μ.real {σ | E σ} = roundProb x E :=
      pi_prob p hp0 hp1 E
    let A : Set (Fin n → Finset (Fin m)) := {σ | ∃ j, ε < (count σ j : ℝ)}
    let B : Set (Fin n → Finset (Fin m)) := {σ | welfare v σ < lpValue v x/3}
    have hA : μ.real A ≤ 1/(m:ℝ) := by
      rw [hprob]
      exact (hm₀ m ((le_max_left _ _).trans hm) n x hx.1).2
    have hB : μ.real B < 3/4 := by
      rw [hprob]
      exact eventB_bound v hnorm hmono x hx.1 hlarge
    have hgood : {σ | (∀ j, count σ j ≤ kOf m) ∧ lpValue v x/3 ≤ welfare v σ} = (A ∪ B)ᶜ := by
      ext σ
      change ((∀ j, count σ j ≤ ⌊ε⌋₊) ∧ lpValue v x/3 ≤ welfare v σ) ↔
        ¬ ((∃ j, ε < (count σ j : ℝ)) ∨ welfare v σ < lpValue v x/3)
      simp only [not_or,not_exists,not_lt,Nat.le_floor_iff hε]
    rw [← hprob, hgood, measureReal_compl (Set.toFinite _).measurableSet]
    have hunion : μ.real (A∪B) ≤ μ.real A+μ.real B := measureReal_union_le _ _
    have hrecip : 1/(m:ℝ) < 1/12 := by exact one_div_lt_one_div_of_lt (by norm_num) hm12
    have huniv : μ.real Set.univ = 1 := probReal_univ
    rw [huniv]
    linarith
  · intro σ hcount hval r hr i₀ hi₀
    have hk : 1 ≤ kOf m := hr.1.trans hr.2.1
    have hbest := best_layer_bound v hnorm hsub x σ (kOf m) hk hcount hval r hr
    have hlayer := (layers_partition σ (kOf m) hcount).1 r hr.1 hr.2.1
    have hout : welfare v (fun i => layer σ i r) ≤ welfare v (algOutput v σ r i₀) := by
      unfold algOutput
      split_ifs with h
      · rw [all_to_one_welfare v hnorm i₀]
        exact h
      · exact le_rfl
    refine ⟨?_, ?_⟩
    · unfold algOutput
      split_ifs
      · exact all_to_one_alloc i₀
      · exact hlayer
    · intro O hO
      have hk0 : (0:ℝ) < kOf m := by exact_mod_cast (show 0 < kOf m by omega)
      exact (div_le_div_of_nonneg_right (opt_le_lp v x hx O hO) (by positivity)).trans
        (hbest.trans hout)
  · intro i₀ hmax hsmall O hO
    have hopt := opt_le_lp v x hx O hO
    linarith
