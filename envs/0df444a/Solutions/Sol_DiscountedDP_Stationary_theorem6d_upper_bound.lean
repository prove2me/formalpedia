-- Prove2me | solution 1 for DiscountedDP.Stationary.theorem6d_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T21:05:24.771149+00:00
-- url     : https://prove2.me/submissions/11764d76-b68a-415f-8e81-1fe52b74a761

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Operators



namespace DiscountedDP.Stationary

open MeasureTheory ProbabilityTheory

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

lemma d6_hsnd (n : ℕ) : Measurable (fun h : Hist S A n => h.2) := measurable_snd

lemma d6_prob (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) :
    ∀ n, IsProbabilityMeasure (historyLaw P π s n) := by
  intro n
  induction n with
  | zero => simp only [historyLaw]; exact Measure.dirac.isProbabilityMeasure
  | succ n ih =>
    haveI := π.κ_markov n
    haveI := P.q_markov
    haveI : IsMarkovKernel (nextKernel P n) := by unfold nextKernel; infer_instance
    simp only [historyLaw]
    exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma d6_stage_prob (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) (n : ℕ) :
    IsProbabilityMeasure (stageLaw P π s n) := by
  haveI := π.κ_markov n
  haveI := P.q_markov
  haveI := d6_prob P π s n
  haveI : IsMarkovKernel (nextKernel P n) := by unfold nextKernel; infer_instance
  simp only [stageLaw]
  infer_instance

lemma d6_hist_succ (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) (n : ℕ)
    (g : S → ℝ) (hg : Measurable g) :
    ∫ h, g h.2 ∂historyLaw P π s (n+1) = ∫ x, g x.2 ∂stageLaw P π s n := by
  haveI := π.κ_markov n
  haveI := P.q_markov
  haveI : IsMarkovKernel (nextKernel P n) := by unfold nextKernel; infer_instance
  simp only [historyLaw, stageLaw]
  have hφ : Measurable (fun x : (Hist S A n × A) × S =>
          (((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => S × A)
            (Fin.last n)).symm ((x.1.1.2, x.1.2), x.1.1.1), x.2) : Hist S A (n+1))) := by fun_prop
  exact integral_map hφ.aemeasurable (f := fun h : Hist S A (n+1) => g h.2)
    ((hg.comp (d6_hsnd (n+1))).aestronglyMeasurable)

lemma d6_bdd_int {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (g : X → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ x, |g x| ≤ C) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable C (Filter.Eventually.of_forall (fun x => by simpa using hC x))

lemma d6_step (P : Problem S A) (u : S → ℝ) (hu : IsBM u)
    (hupper : ∀ a s, Ta P a u s ≤ u s)
    (π : Plan (S := S) (A := A)) (s : S) (n : ℕ) :
    stageReward P π s n + P.β * ∫ h, u h.2 ∂historyLaw P π s (n+1) ≤
      ∫ h, u h.2 ∂historyLaw P π s n := by
  haveI := π.κ_markov n
  haveI := P.q_markov
  haveI := d6_prob P π s n
  haveI := d6_stage_prob P π s n
  haveI : IsMarkovKernel (nextKernel P n) := by unfold nextKernel; infer_instance
  obtain ⟨Cr, hr⟩ := P.r_bounded
  obtain ⟨Cu, hCu⟩ := hu.2
  have hβ := P.β_nonneg
  rw [d6_hist_succ P π s n u hu.1]
  have hrm : Measurable (fun x : (Hist S A n × A) × S => P.r (x.1.1.2, x.1.2, x.2)) :=
    P.r_measurable.comp (by fun_prop)
  have hum : Measurable (fun x : (Hist S A n × A) × S => u x.2) := hu.1.comp measurable_snd
  have i1 : Integrable (fun x : (Hist S A n × A) × S => P.r (x.1.1.2, x.1.2, x.2)) (stageLaw P π s n) :=
    d6_bdd_int _ _ hrm Cr (fun x => hr _)
  have i2 : Integrable (fun x : (Hist S A n × A) × S => u x.2) (stageLaw P π s n) :=
    d6_bdd_int _ _ hum Cu (fun x => hCu _)
  have e1 : stageReward P π s n + P.β * ∫ x, u x.2 ∂stageLaw P π s n =
      ∫ x, (P.r (x.1.1.2, x.1.2, x.2) + P.β * u x.2) ∂stageLaw P π s n := by
    rw [integral_add i1 (i2.const_mul _), integral_const_mul]; rfl
  rw [e1]
  set μ := historyLaw P π s n with hμ
  set κ := π.κ n
  have hGm : Measurable (fun x : (Hist S A n × A) × S => P.r (x.1.1.2, x.1.2, x.2) + P.β * u x.2) :=
    hrm.add (hum.const_mul _)
  have iG : Integrable (fun x : (Hist S A n × A) × S => P.r (x.1.1.2, x.1.2, x.2) + P.β * u x.2)
      (stageLaw P π s n) := i1.add (i2.const_mul _)
  have e2 : ∫ x, (P.r (x.1.1.2, x.1.2, x.2) + P.β * u x.2) ∂stageLaw P π s n =
      ∫ p, (∫ s', (P.r (p.1.2, p.2, s') + P.β * u s') ∂nextKernel P n p) ∂(μ.compProd κ) := by
    have : stageLaw P π s n = (μ.compProd κ).compProd (nextKernel P n) := rfl
    rw [this] at iG ⊢
    rw [Measure.integral_compProd iG]
  rw [e2]
  have hnext : ∀ p : Hist S A n × A, nextKernel P n p = P.q (p.1.2, p.2) := by
    intro p
    simp only [nextKernel]
    rw [Kernel.comp_deterministic_eq_comap, Kernel.comap_apply]
  have e3 : ∀ p : Hist S A n × A, ∫ s', (P.r (p.1.2, p.2, s') + P.β * u s') ∂nextKernel P n p =
      Ta P p.2 u p.1.2 := by
    intro p; rw [hnext]; rfl
  simp_rw [e3]
  -- integrability
  have hTam : Measurable (fun p : Hist S A n × A => Ta P p.2 u p.1.2) := by
    have h : StronglyMeasurable (fun p : Hist S A n × A =>
        ∫ s', (P.r (p.1.2, p.2, s') + P.β * u s') ∂nextKernel P n p) := by
      apply StronglyMeasurable.integral_kernel_prod_right (κ := nextKernel P n)
        (f := fun (p : Hist S A n × A) (s' : S) => P.r (p.1.2, p.2, s') + P.β * u s')
      apply Measurable.stronglyMeasurable
      exact (P.r_measurable.comp (by fun_prop)).add ((hu.1.comp measurable_snd).const_mul _)
    simp_rw [e3] at h
    exact h.measurable
  have hTab : ∀ p : Hist S A n × A, |Ta P p.2 u p.1.2| ≤ Cr + P.β * Cu := by
    intro p
    have := norm_integral_le_of_norm_le_const (μ := P.q (p.1.2, p.2))
      (f := fun s' => P.r (p.1.2, p.2, s') + P.β * u s') (C := Cr + P.β * Cu)
      (Filter.Eventually.of_forall (fun s' => by
        simp only [Real.norm_eq_abs]
        calc |P.r (p.1.2, p.2, s') + P.β * u s'| ≤ |P.r (p.1.2, p.2, s')| + |P.β * u s'| := abs_add_le _ _
          _ ≤ Cr + P.β * Cu := by
            rw [abs_mul, abs_of_nonneg hβ]
            exact add_le_add (hr _) (mul_le_mul_of_nonneg_left (hCu s') hβ)))
    simpa [Ta] using this
  have iT : Integrable (fun p : Hist S A n × A => Ta P p.2 u p.1.2) (μ.compProd κ) :=
    d6_bdd_int _ _ hTam _ hTab
  have iU : Integrable (fun p : Hist S A n × A => u p.1.2) (μ.compProd κ) :=
    d6_bdd_int _ _ (hu.1.comp (measurable_snd.comp measurable_fst)) Cu (fun p => hCu _)
  calc ∫ p, Ta P p.2 u p.1.2 ∂(μ.compProd κ) ≤ ∫ p, u p.1.2 ∂(μ.compProd κ) :=
        integral_mono iT iU (fun p => hupper _ _)
    _ = ∫ h, u h.2 ∂μ := by
        rw [Measure.integral_compProd iU]
        congr 1; funext h
        simp

theorem theorem6d_core
    (P : Problem S A) (u : S → ℝ) (hu : IsBM u)
    (hupper : ∀ a s, Ta P a u s ≤ u s) :
    ∀ π : Plan (S := S) (A := A), ∀ s, I P π s ≤ u s := by
  intro π s
  obtain ⟨Cr, hr⟩ := P.r_bounded
  obtain ⟨Cu, hCu⟩ := hu.2
  have hβ0 := P.β_nonneg
  have hβ1 := P.β_lt_one
  set W : ℕ → ℝ := fun n => ∫ h, u h.2 ∂historyLaw P π s n with hW
  set R : ℕ → ℝ := fun n => stageReward P π s n with hR
  have hstep : ∀ n, R n + P.β * W (n+1) ≤ W n := fun n => d6_step P u hu hupper π s n
  have hW0 : W 0 = u s := by
    simp only [hW, historyLaw]
    exact integral_dirac' _ _ ((hu.1.comp measurable_snd).stronglyMeasurable)
  have hWb : ∀ n, |W n| ≤ Cu := by
    intro n
    haveI := d6_prob P π s n
    have := norm_integral_le_of_norm_le_const (μ := historyLaw P π s n) (f := fun h => u h.2) (C := Cu)
      (Filter.Eventually.of_forall (fun h => by simpa using hCu h.2))
    simpa using this
  have hRb : ∀ n, |R n| ≤ Cr := by
    intro n
    haveI := d6_stage_prob P π s n
    have := norm_integral_le_of_norm_le_const (μ := stageLaw P π s n)
      (f := fun x : (Hist S A n × A) × S => P.r (x.1.1.2, x.1.2, x.2)) (C := Cr)
      (Filter.Eventually.of_forall (fun h => by simpa using hr _))
    simpa [hR, stageReward] using this
  have hsum : Summable (fun n => P.β ^ n * R n) := by
    refine Summable.of_norm_bounded (g := fun n => Cr * P.β ^ n)
      ((summable_geometric_of_lt_one hβ0 hβ1).mul_left Cr) ?_
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 n), mul_comm]
    exact mul_le_mul_of_nonneg_right (hRb n) (pow_nonneg hβ0 n)
  have hpartial : ∀ N, ∑ k ∈ Finset.range N, P.β ^ k * R k ≤ W 0 - P.β ^ N * W N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have := hstep N
      have hp : 0 ≤ P.β ^ N := pow_nonneg hβ0 N
      have : P.β ^ N * R N ≤ P.β ^ N * W N - P.β ^ (N+1) * W (N+1) := by
        rw [pow_succ]; nlinarith
      linarith
  have hbound : ∀ N, ∑ k ∈ Finset.range N, P.β ^ k * R k ≤ u s + P.β ^ N * Cu := by
    intro N
    have h1 := hpartial N
    have h2 : -(P.β ^ N * W N) ≤ P.β ^ N * Cu := by
      have := (abs_le.mp (hWb N)).1
      have hp : 0 ≤ P.β ^ N := pow_nonneg hβ0 N
      nlinarith
    linarith
  have ht : Filter.Tendsto (fun N => ∑ k ∈ Finset.range N, P.β ^ k * R k) Filter.atTop
      (nhds (I P π s)) := hsum.hasSum.tendsto_sum_nat
  have ht2 : Filter.Tendsto (fun N : ℕ => u s + P.β ^ N * Cu) Filter.atTop (nhds (u s + 0 * Cu)) :=
    tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const Cu)
  have := le_of_tendsto_of_tendsto' ht ht2 hbound
  simpa using this

end DiscountedDP.Stationary

open DiscountedDP.Stationary


theorem solution
    {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : Problem S A) (u : S → ℝ) (hu : IsBM u)
    (hupper : ∀ a s, Ta P a u s ≤ u s) :
    ∀ π : Plan (S := S) (A := A), ∀ s, I P π s ≤ u s := by
  exact theorem6d_core P u hu hupper
