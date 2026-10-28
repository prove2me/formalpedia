-- Prove2me | solution 1 for ClosestString.PTAS.lemma_6_rounding
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T12:57:20.708731+00:00
-- url     : https://prove2.me/submissions/b273dcc6-a082-44cb-87b9-09f1a9620dce

import Mathlib

namespace ClosestString.PTAS.A3L6

open MeasureTheory ProbabilityTheory

/-- Hoeffding for `[0,1]`-valued independent variables, both tails. -/
theorem hoeff {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ) (hm : ∀ i, Measurable (X i))
    (hind : iIndepFun X Pr) (hb : ∀ i, ∀ᵐ ω ∂Pr, X i ω ∈ Set.Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 ≤ t) :
    Pr.real {ω | (∫ ω', ∑ i, X i ω' ∂Pr) + t ≤ ∑ i, X i ω} ≤
        Real.exp (-t ^ 2 / (2 * ∑ _i : ι, (((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : NNReal) : ℝ))) ∧
      Pr.real {ω | ∑ i, X i ω ≤ (∫ ω', ∑ i, X i ω' ∂Pr) - t} ≤
        Real.exp (-t ^ 2 / (2 * ∑ _i : ι, (((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : NNReal) : ℝ))) := by
  have hint : ∀ i, Integrable (X i) Pr := fun i =>
    Integrable.of_mem_Icc 0 1 (hm i).aemeasurable (hb i)
  have hsum : (∫ ω', ∑ i, X i ω' ∂Pr) = ∑ i, ∫ ω', X i ω' ∂Pr :=
    integral_finset_sum _ fun i _ => hint i
  set Y : ι → Ω → ℝ := fun i ω => X i ω - ∫ ω', X i ω' ∂Pr with hYdef
  have hYind : iIndepFun Y Pr :=
    hind.comp (fun i x => x - ∫ ω', X i ω' ∂Pr) fun i => measurable_id.sub_const _
  have hYsub : ∀ i, HasSubgaussianMGF (Y i) ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) Pr := fun i =>
    hasSubgaussianMGF_of_mem_Icc (hm i).aemeasurable (hb i)
  have hYsum : ∀ ω, ∑ i ∈ Finset.univ, Y i ω = ∑ i, X i ω - ∫ ω', ∑ i, X i ω' ∂Pr := by
    intro ω; rw [hsum]; simp [hYdef, Finset.sum_sub_distrib]
  have h1 := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hYind (s := Finset.univ)
    (fun i _ => hYsub i) ht
  have hnind : iIndepFun (fun i ω => -Y i ω) Pr :=
    hYind.comp (fun _ x => -x) fun _ => measurable_neg
  have h2 := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hnind (s := Finset.univ)
    (fun i _ => (hYsub i).neg) ht
  push_cast at h1 h2 ⊢
  constructor
  · refine le_trans (le_of_eq ?_) h1
    congr 1; ext ω; simp only [Set.mem_setOf_eq, hYsum]; constructor <;> intro h <;> linarith
  · refine le_trans (le_of_eq ?_) h2
    congr 1; ext ω
    simp only [Set.mem_setOf_eq, Finset.sum_neg_distrib, hYsum]
    constructor <;> intro h <;> linarith

theorem main {A : Type*} [Fintype A] [DecidableEq A] [MeasurableSpace A]
    [DiscreteMeasurableSpace A] {ι : Type*} [Fintype ι] {n : ℕ} (a : Fin n → ι → A)
    (b : Fin n → ℝ) (xbar : ι → A → ℝ) (hx0 : ∀ j c, 0 ≤ xbar j c) (hx1 : ∀ j, ∑ c, xbar j c = 1)
    (D : ℝ) (hLP : ∀ i, ∑ j, ∑ c, (if a i j = c then (0 : ℝ) else 1) * xbar j c ≤ D - b i)
    (ε' : ℝ) (hε' : 0 < ε') :
    Measure.pi (fun j : ι => ∑ c : A, ENNReal.ofReal (xbar j c) • Measure.dirac c)
        {x | ∃ i, D + ε' * Fintype.card ι - b i ≤ (hammingDist (a i) x : ℝ)}
        ≤ ENNReal.ofReal (n * Real.exp (-(1 / 3) * ε' ^ 2 * Fintype.card ι)) ∧
      (4 * Real.log n / ε' ^ 2 ≤ Fintype.card ι →
        (n : ℝ) * Real.exp (-(1 / 3) * ε' ^ 2 * Fintype.card ι) ≤ (n : ℝ) ^ (-(1 / 3 : ℝ))) := by
  set μ : ι → Measure A := fun j => ∑ c : A, ENNReal.ofReal (xbar j c) • Measure.dirac c with hμ
  haveI hprob : ∀ j, IsProbabilityMeasure (μ j) := fun j => by
    constructor
    simp only [hμ, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ => hx0 j c), hx1 j, ENNReal.ofReal_one]
  have hint : ∀ j (f : A → ℝ), ∫ c, f c ∂μ j = ∑ c, xbar j c * f c := by
    intro j f
    simp only [hμ]
    rw [integral_finset_sum_measure (fun c _ => Integrable.of_finite.smul_measure ENNReal.ofReal_ne_top)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hx0 j c), smul_eq_mul]
  set K : ℝ := ((Fintype.card ι : ℕ) : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  have hone : ∀ i : Fin n, Measure.pi μ {x | D + ε' * K - b i ≤ (hammingDist (a i) x : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-(1 / 3) * ε' ^ 2 * K)) := by
    intro i
    set X' : ι → A → ℝ := fun j c => if a i j = c then 0 else 1 with hX'
    set X : ι → (ι → A) → ℝ := fun j x => X' j (x j) with hX
    have hm : ∀ j, Measurable (X j) := fun j =>
      (Measurable.of_discrete (f := X' j)).comp (measurable_pi_apply j)
    have hind : iIndepFun X (Measure.pi μ) :=
      iIndepFun_pi (X := X') fun j => (Measurable.of_discrete (f := X' j)).aemeasurable
    have hb : ∀ j, ∀ᵐ x ∂(Measure.pi μ), X j x ∈ Set.Icc (0 : ℝ) 1 := fun j =>
      ae_of_all _ fun x => by simp only [hX, hX']; split_ifs <;> norm_num
    obtain ⟨h1, -⟩ := hoeff (Measure.pi μ) X hm hind hb (t := ε' * K) (by positivity)
    have hmean : (∫ x, ∑ j, X j x ∂(Measure.pi μ)) ≤ D - b i := by
      rw [integral_finset_sum _ fun j _ =>
        Integrable.of_mem_Icc 0 1 (hm j).aemeasurable (hb j)]
      refine le_trans (le_of_eq ?_) (hLP i)
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show (fun x : ι → A => X j x) = fun x => X' j (x j) from rfl,
        integral_comp_eval (Measurable.of_discrete (f := X' j)).aestronglyMeasurable, hint]
      exact Finset.sum_congr rfl fun c _ => mul_comm _ _
    have hham : ∀ x, (hammingDist (a i) x : ℝ) = ∑ j, X j x := by
      intro x
      simp only [hammingDist, hX, hX']
      rw [Finset.card_filter]; push_cast
      exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp_all
    have hsub : {x | D + ε' * K - b i ≤ (hammingDist (a i) x : ℝ)} ⊆
        {x | (∫ x, ∑ j, X j x ∂(Measure.pi μ)) + ε' * K ≤ ∑ j, X j x} := by
      intro x hx
      simp only [Set.mem_setOf_eq, hham] at hx ⊢
      linarith
    have hc : ∑ _j : ι, (((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : NNReal) : ℝ) = K / 4 := by
      simp [hK]; norm_num; ring
    rw [hc] at h1
    have hexp : Real.exp (-(ε' * K) ^ 2 / (2 * (K / 4))) ≤ Real.exp (-(1 / 3) * ε' ^ 2 * K) := by
      rw [Real.exp_le_exp]
      rcases hK0.lt_or_eq with hKp | hKz
      · rw [show -(ε' * K) ^ 2 / (2 * (K / 4)) = -2 * ε' ^ 2 * K by field_simp; ring]
        nlinarith [sq_nonneg ε']
      · rw [← hKz]; simp
    calc Measure.pi μ {x | D + ε' * K - b i ≤ (hammingDist (a i) x : ℝ)}
        ≤ Measure.pi μ {x | (∫ x, ∑ j, X j x ∂(Measure.pi μ)) + ε' * K ≤ ∑ j, X j x} :=
          measure_mono hsub
      _ = ENNReal.ofReal ((Measure.pi μ).real
            {x | (∫ x, ∑ j, X j x ∂(Measure.pi μ)) + ε' * K ≤ ∑ j, X j x}) :=
          (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (h1.trans hexp)
  constructor
  · have hU : {x : ι → A | ∃ i, D + ε' * K - b i ≤ (hammingDist (a i) x : ℝ)} =
        ⋃ i, {x | D + ε' * K - b i ≤ (hammingDist (a i) x : ℝ)} := by
      ext x; simp
    rw [hU]
    refine (measure_iUnion_fintype_le _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hone i).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  · intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog : 4 * Real.log n ≤ ε' ^ 2 * K := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < ε' ^ 2)).mp h
      linarith
    rw [Real.rpow_def_of_pos hnr]
    calc (n : ℝ) * Real.exp (-(1 / 3) * ε' ^ 2 * K)
        ≤ Real.exp (Real.log n) * Real.exp (Real.log n * (-(4 / 3))) := by
          rw [Real.exp_log hnr]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hnr.le
      _ = Real.exp (Real.log n * (-(1 / 3))) := by
          rw [← Real.exp_add]; ring_nf

end ClosestString.PTAS.A3L6

open MeasureTheory in
theorem solution {A : Type*} [Fintype A] [DecidableEq A] [MeasurableSpace A]
    [DiscreteMeasurableSpace A] {ι : Type*} [Fintype ι] {n : ℕ} (a : Fin n → ι → A)
    (b : Fin n → ℝ) (xbar : ι → A → ℝ) (hx0 : ∀ j c, 0 ≤ xbar j c) (hx1 : ∀ j, ∑ c, xbar j c = 1)
    (D : ℝ) (hLP : ∀ i, ∑ j, ∑ c, (if a i j = c then (0 : ℝ) else 1) * xbar j c ≤ D - b i)
    (ε' : ℝ) (hε' : 0 < ε') :
    Measure.pi (fun j : ι => ∑ c : A, ENNReal.ofReal (xbar j c) • Measure.dirac c)
        {x | ∃ i, D + ε' * Fintype.card ι - b i ≤ (hammingDist (a i) x : ℝ)}
        ≤ ENNReal.ofReal (n * Real.exp (-(1 / 3) * ε' ^ 2 * Fintype.card ι)) ∧
      (4 * Real.log n / ε' ^ 2 ≤ Fintype.card ι →
        (n : ℝ) * Real.exp (-(1 / 3) * ε' ^ 2 * Fintype.card ι) ≤ (n : ℝ) ^ (-(1 / 3 : ℝ))) :=
  ClosestString.PTAS.A3L6.main a b xbar hx0 hx1 D hLP ε' hε'

#print axioms solution
