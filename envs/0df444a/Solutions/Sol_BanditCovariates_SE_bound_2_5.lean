-- Prove2me | solution 1 for BanditCovariates.SE.bound_2_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:25:29.425151+00:00
-- url     : https://prove2.me/submissions/8b1e1ac0-d02a-4763-aaea-a6c62c14fe15

import Mathlib
import Definitions.Def_BanditCovariates_SE_Setting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory BanditCovariates.SE

theorem solution {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (K : ℕ) (hK : 1 ≤ K)
    (Y : Fin (K + 1) → ℕ → Ω → ℝ) (f : Fin (K + 1) → ℝ)
    (hmodel : RegretBandits.Stochastic.IsStochasticBandit P Y f)
    (hbounded : ∀ i k, ∀ᵐ ω ∂P, Y i k ω ∈ Set.Icc (0 : ℝ) 1)
    (hordered : Monotone f)
    (hbest : ∀ i, i ≠ Fin.last K → f i < f (Fin.last K))
    (i : Fin (K + 1)) (hi : i ≠ Fin.last K)
    (T τ : ℕ) (hT : 1 ≤ T) (hτ : 1 ≤ τ) (γ : ℝ) (hγ : 1 ≤ γ)
    (hthreshold : γ * U τ T ≤ gap f i) :
    P.real {ω | estimatedGap Y i τ ω < γ * U τ T} ≤
      Real.exp (-(τ : ℝ) * (gap f i - γ * U τ T) ^ 2 / 2) := by
  classical
  set L : Fin (K + 1) := Fin.last K with hL
  have hmean : ∀ a k, ∫ ω, Y a k ω ∂P = f a := fun a k =>
    (hmodel.identDistrib a k).integral_eq.trans (hmodel.mean a)
  have hsub : ∀ a k, HasSubgaussianMGF (fun ω => Y a k ω - f a) ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) P := by
    intro a k
    have := hasSubgaussianMGF_of_mem_Icc (μ := P) (X := Y a k) (hmodel.measurable a k).aemeasurable
      (hbounded a k)
    simpa [hmean a k] using this
  let V : Fin (K + 1) × ℕ → Ω → ℝ := fun p ω => (if p.1 = L then -1 else 1) * (Y p.1 p.2 ω - f p.1)
  have hV_indep : iIndepFun V P := by
    have := hmodel.indep.comp (fun (p : Fin (K + 1) × ℕ) (x : ℝ) => (if p.1 = L then (-1 : ℝ) else 1) * (x - f p.1))
      (fun p => by fun_prop)
    exact this
  have hVsub : ∀ p : Fin (K + 1) × ℕ, HasSubgaussianMGF (V p) ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) P := by
    intro p
    by_cases hp : p.1 = L
    · have h := (hsub p.1 p.2).neg
      have : V p = -(fun ω => Y p.1 p.2 ω - f p.1) := by
        funext ω; simp [V, hp]
      rw [this]; exact h
    · have : V p = (fun ω => Y p.1 p.2 ω - f p.1) := by
        funext ω; simp [V, hp]
      rw [this]; exact hsub p.1 p.2
  set t : ℝ := gap f i - γ * U τ T with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have hτpos : (0 : ℝ) < τ := by exact_mod_cast hτ
  set s : Finset (Fin (K + 1) × ℕ) := ({L, i} : Finset (Fin (K + 1))) ×ˢ Finset.range τ with hs
  have hiL : i ≠ L := hi
  have hH := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hV_indep
    (c := fun _ => (‖(1 : ℝ) - 0‖₊ / 2) ^ 2) (s := s) (fun p _ => hVsub p)
    (ε := τ * t) (mul_nonneg hτpos.le ht0)
  have hcardR : (((∑ p ∈ s, (‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : NNReal)) : ℝ) = (τ : ℝ) / 2 := by
    rw [Finset.sum_const, hs, Finset.card_product, Finset.card_pair hiL.symm, Finset.card_range]
    push_cast
    simp only [nsmul_eq_mul]
    push_cast
    simp
    ring
  have hsubset : {ω | estimatedGap Y i τ ω < γ * U τ T} ⊆ {ω | (τ : ℝ) * t ≤ ∑ p ∈ s, V p ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hsum : ∑ p ∈ s, V p ω = (τ : ℝ) * (f L - f i) -
        (∑ k ∈ Finset.range τ, Y L k ω - ∑ k ∈ Finset.range τ, Y i k ω) := by
      rw [hs, Finset.sum_product, Finset.sum_pair hiL.symm]
      simp only [V, if_pos rfl, if_neg hiL, if_true]
      simp only [neg_mul, one_mul, mul_sub, Finset.sum_neg_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    rw [hsum]
    unfold estimatedGap RegretBandits.Stochastic.sampleMean at hω
    rw [← sub_div, div_lt_iff₀ hτpos] at hω
    have hgap : gap f i = f L - f i := rfl
    rw [ht, hgap]
    nlinarith
  have hmono := measureReal_mono (μ := P) hsubset (measure_ne_top P _)
  refine hmono.trans (hH.trans ?_)
  rw [hcardR]
  apply Real.exp_le_exp.2
  have : -((τ : ℝ) * t) ^ 2 / (2 * ((τ : ℝ) / 2)) = -(τ : ℝ) * t ^ 2 := by
    field_simp
  rw [this]
  have : 0 ≤ (τ : ℝ) * t ^ 2 := by positivity
  linarith
