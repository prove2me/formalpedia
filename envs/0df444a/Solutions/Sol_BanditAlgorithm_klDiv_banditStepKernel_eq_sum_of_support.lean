-- Prove2me | solution 1 for BanditAlgorithm.klDiv_banditStepKernel_eq_sum_of_support
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T17:07:03.626864+00:00
-- url     : https://prove2.me/submissions/3bd5e5d9-7d01-4286-926e-407c31ef11f6

import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.CompProdEqIff
import Definitions.Def_BanditPolicy

/-!
# The one-round divergence of the canonical bandit model

`klDiv (banditStepKernel ν π n h) (banditStepKernel ν' π n h)
  = ∑ i, (π.select n h) {i} * klDiv (ν.P i) (ν'.P i)`.

This is the conditional computation inside L&S Lemma 15.1 / Eq. (15.2) (printed pp. 198-199):
after conditioning on the arm actually selected, the policy factors cancel from the likelihood
ratio and only the reward divergences survive, weighted by the policy's selection probabilities.

It is stated here as a standalone reusable lemma: it is the per-round content of every divergence
decomposition in the canonical model, and is needed pointwise on an event whenever the
decomposition is localised (as in stopping-time arguments).
-/

open MeasureTheory ProbabilityTheory InformationTheory

namespace BanditAlgorithm

/-- For a measure on a finite type, almost every point has positive mass. -/
private lemma ae_singleton_ne_zero {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (μ : Measure ι) : ∀ᵐ i ∂μ, μ {i} ≠ 0 := by
  classical
  rw [ae_iff]
  simp only [ne_eq, not_not]
  have hset : {i : ι | μ {i} = 0} = ⋃ i ∈ {i : ι | μ {i} = 0}, ({i} : Set ι) := by
    ext i; simp
  rw [hset, measure_biUnion_null_iff (Set.to_countable _)]
  exact fun i hi ↦ hi

private theorem arm_ac {k : ℕ} (nu nu' : StochasticBandit k)
    (hKL : ∀ i, klDiv (nu.P i) (nu'.P i) ≠ ⊤) (i : Fin k) :
    nu.P i ≪ nu'.P i :=
  (klDiv_ne_top_iff.mp (hKL i)).1

private theorem measurable_arm_rnDeriv {k : ℕ} (nu nu' : StochasticBandit k) :
    Measurable (fun z : Fin k × ℝ ↦ (nu.P z.1).rnDeriv (nu'.P z.1) z.2) := by
  classical
  let f : Fin k × ℝ → ENNReal := fun z ↦
    ∑ i, Set.indicator {z : Fin k × ℝ | z.1 = i}
      (fun z ↦ (nu.P i).rnDeriv (nu'.P i) z.2) z
  have hf : Measurable f := by
    dsimp [f]
    apply Finset.measurable_sum
    intro i _
    exact ((Measure.measurable_rnDeriv (nu.P i) (nu'.P i)).comp measurable_snd).indicator
      ((measurableSet_singleton i).preimage measurable_fst)
  have h_eq : f = fun z : Fin k × ℝ ↦
      (nu.P z.1).rnDeriv (nu'.P z.1) z.2 := by
    funext z
    simp only [f, Set.indicator_apply, Set.mem_setOf_eq]
    rw [Finset.sum_ite_eq]
    simp
  rwa [← h_eq]

private theorem step_ac {k n : ℕ} (nu nu' : StochasticBandit k)
    (pi : BanditPolicy k) (h : BanditHistory k n)
    (hKL : ∀ i, (pi.select n h) {i} ≠ 0 → klDiv (nu.P i) (nu'.P i) ≠ ⊤) :
    banditStepKernel nu pi n h ≪ banditStepKernel nu' pi n h := by
  rw [banditStepKernel, banditStepKernel]
  rw [Kernel.compProd_apply_eq_compProd_sectR,
    Kernel.compProd_apply_eq_compProd_sectR]
  refine Measure.AbsolutelyContinuous.compProd_right ?_
  filter_upwards [ae_singleton_ne_zero (pi.select n h)] with i hi
  show nu.P i ≪ nu'.P i
  exact (klDiv_ne_top_iff.mp (hKL i hi)).1

private theorem step_withDensity {k n : ℕ} (nu nu' : StochasticBandit k)
    (pi : BanditPolicy k) (h : BanditHistory k n)
    (hKL : ∀ i, (pi.select n h) {i} ≠ 0 → klDiv (nu.P i) (nu'.P i) ≠ ⊤) :
    (banditStepKernel nu' pi n h).withDensity
        (fun z : Fin k × ℝ ↦ (nu.P z.1).rnDeriv (nu'.P z.1) z.2) =
      banditStepKernel nu pi n h := by
  rw [banditStepKernel, banditStepKernel]
  rw [Kernel.compProd_apply_eq_compProd_sectR,
    Kernel.compProd_apply_eq_compProd_sectR]
  ext s hs
  rw [withDensity_apply _ hs]
  rw [Measure.compProd_apply hs]
  rw [← lintegral_indicator hs]
  rw [Measure.lintegral_compProd
    ((measurable_arm_rnDeriv nu nu').indicator hs)]
  apply lintegral_congr_ae
  filter_upwards [ae_singleton_ne_zero (pi.select n h)] with i hi
  rw [Kernel.sectR_apply, Kernel.sectR_apply]
  simp only [Kernel.comap_apply, banditRewardKernel]
  change (∫⁻ x, s.indicator
      (fun z : Fin k × ℝ ↦ (nu.P z.1).rnDeriv (nu'.P z.1) z.2) (i, x)
      ∂nu'.P i) = nu.P i (Prod.mk i ⁻¹' s)
  calc
    _ = ∫⁻ x in Prod.mk i ⁻¹' s,
        (nu.P i).rnDeriv (nu'.P i) x ∂nu'.P i := by
      rw [← lintegral_indicator (measurable_prodMk_left hs)]
      apply lintegral_congr
      intro x
      rfl
    _ = nu.P i (Prod.mk i ⁻¹' s) :=
      Measure.setLIntegral_rnDeriv (klDiv_ne_top_iff.mp (hKL i hi)).1 _

private theorem rnDeriv_step {k n : ℕ} (nu nu' : StochasticBandit k)
    (pi : BanditPolicy k) (h : BanditHistory k n)
    (hKL : ∀ i, (pi.select n h) {i} ≠ 0 → klDiv (nu.P i) (nu'.P i) ≠ ⊤) :
    (banditStepKernel nu pi n h).rnDeriv (banditStepKernel nu' pi n h) =ᵐ[
      banditStepKernel nu' pi n h]
        fun z : Fin k × ℝ ↦ (nu.P z.1).rnDeriv (nu'.P z.1) z.2 := by
  rw [← step_withDensity nu nu' pi h hKL]
  exact Measure.rnDeriv_withDensity _ (measurable_arm_rnDeriv nu nu')

private theorem klDiv_banditStepKernel_eq_sum {k n : ℕ}
    (nu nu' : StochasticBandit k)
    (pi : BanditPolicy k) (h : BanditHistory k n)
    (hKL : ∀ i, (pi.select n h) {i} ≠ 0 → klDiv (nu.P i) (nu'.P i) ≠ ⊤) :
    klDiv (banditStepKernel nu pi n h) (banditStepKernel nu' pi n h) =
      ∑ i, ENNReal.ofReal ((pi.select n h).real {i}) *
        klDiv (nu.P i) (nu'.P i) := by
  rw [klDiv_eq_lintegral_klFun_of_ac (step_ac nu nu' pi h hKL)]
  calc
    (∫⁻ z, ENNReal.ofReal
        (klFun (((banditStepKernel nu pi n h).rnDeriv
          (banditStepKernel nu' pi n h)) z).toReal)
        ∂banditStepKernel nu' pi n h) =
        ∫⁻ z, ENNReal.ofReal
          (klFun (((nu.P z.1).rnDeriv (nu'.P z.1) z.2).toReal))
          ∂banditStepKernel nu' pi n h := by
      apply lintegral_congr_ae
      filter_upwards [rnDeriv_step nu nu' pi h hKL] with z hz
      rw [hz]
    _ = ∫⁻ i, klDiv (nu.P i) (nu'.P i) ∂pi.select n h := by
      rw [banditStepKernel]
      rw [Kernel.compProd_apply_eq_compProd_sectR]
      have hmeas : Measurable (fun z : Fin k × ℝ ↦ ENNReal.ofReal
          (klFun (((nu.P z.1).rnDeriv (nu'.P z.1) z.2).toReal))) :=
        ENNReal.measurable_ofReal.comp
          (measurable_klFun.comp
            (ENNReal.measurable_toReal.comp (measurable_arm_rnDeriv nu nu')))
      rw [Measure.lintegral_compProd hmeas]
      apply lintegral_congr_ae
      filter_upwards [ae_singleton_ne_zero (pi.select n h)] with i hi
      rw [Kernel.sectR_apply]
      simp only [Kernel.comap_apply, banditRewardKernel]
      change (∫⁻ x, ENNReal.ofReal
          (klFun (((nu.P i).rnDeriv (nu'.P i) x).toReal)) ∂nu'.P i) = _
      rw [klDiv_eq_lintegral_klFun_of_ac (klDiv_ne_top_iff.mp (hKL i hi)).1]
    _ = ∑ i, klDiv (nu.P i) (nu'.P i) * (pi.select n h) {i} := by
      exact lintegral_fintype _
    _ = ∑ i, ENNReal.ofReal ((pi.select n h).real {i}) *
        klDiv (nu.P i) (nu'.P i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [ofReal_measureReal, mul_comm]


theorem _root_.solution {k n : ℕ} (nu nu' : StochasticBandit k)
    (pi : BanditPolicy k) (h : BanditHistory k n)
    (hKL : ∀ i, (pi.select n h) {i} ≠ 0 → klDiv (nu.P i) (nu'.P i) ≠ ⊤) :
    klDiv (banditStepKernel nu pi n h) (banditStepKernel nu' pi n h) =
      ∑ i, ENNReal.ofReal ((pi.select n h).real {i}) *
        klDiv (nu.P i) (nu'.P i) :=
  klDiv_banditStepKernel_eq_sum nu nu' pi h hKL

end BanditAlgorithm
