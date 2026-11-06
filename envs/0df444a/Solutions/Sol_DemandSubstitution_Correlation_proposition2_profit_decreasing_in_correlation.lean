-- Prove2me | solution 1 for DemandSubstitution.Correlation.proposition2_profit_decreasing_in_correlation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T22:16:11.406843+00:00
-- url     : https://prove2.me/submissions/6de30c72-e59c-4d40-9807-e0bb20e19fa3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DemandSubstitution_Correlation_Setting
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_StochasticOrders_PositiveDependence_Orders
import Theorems.Thm_DemandSubstitution_Correlation_muller_scarsini_normal_sm
import Theorems.Thm_DemandSubstitution_Correlation_profit_realization_submodular

open MeasureTheory ProbabilityTheory DemandSubstitution.Correlation
open Supermodularity.Monotonicity StochasticOrders.PositiveDependence

private lemma normalLaw_isProb {n : ℕ} (m : Fin n → ℝ) (S : Matrix (Fin n) (Fin n) ℝ) :
    IsProbabilityMeasure (normalLaw m S) := by
  unfold normalLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

private lemma integrable_coord {n : ℕ} (m : Fin n → ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) : Integrable (fun x : Fin n → ℝ => x i) (normalLaw m S) := by
  unfold normalLaw
  refine (integrable_map_measure (g := fun x : Fin n → ℝ => x i)
    (Continuous.aestronglyMeasurable (by fun_prop)) (by fun_prop)).2 ?_
  have := IsGaussian.integrable_dual (multivariateGaussian (WithLp.toLp 2 m) S)
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
  exact this

private lemma integrable_profitAt {n : ℕ} (M : Model n) (m : Fin n → ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (Q : Fin n → ℝ) :
    Integrable (fun x => profitAt M Q x) (normalLaw m S) := by
  have := normalLaw_isProb m S
  have hc := integrable_coord m S
  have hDs : ∀ k, Integrable (fun x => Ds M Q x k) (normalLaw m S) := by
    intro k
    unfold Ds
    refine (hc k).add (integrable_finsetSum _ fun j _ => ?_)
    exact ((((hc j).sub (integrable_const _)).sup (integrable_const _))).const_mul _
  unfold profitAt
  refine integrable_finsetSum _ fun k _ => ?_
  unfold firmProfitAt
  refine (((hDs k).const_mul _).sub ?_).sub ?_
  · exact (((hDs k).sub (integrable_const _)).sup (integrable_const _)).const_mul _
  · exact (((integrable_const _).sub (hDs k)).sup (integrable_const _)).const_mul _

theorem solution {n : ℕ} (M : Model n) (m : Fin n → ℝ)
    (S₁ S₂ : Matrix (Fin n) (Fin n) ℝ) (hS₁ : S₁.PosSemidef) (hS₂ : S₂.PosSemidef)
    (i j : Fin n) (hraise : RaisesCovariance S₁ S₂ i j) :
    (∀ Q : Fin n → ℝ, (∀ k, 0 ≤ Q k) → centralProfit M m S₂ Q ≤ centralProfit M m S₁ Q) ∧
      ∀ Q₁ Q₂ : Fin n → ℝ, IsCentralOptimal M m S₁ Q₁ → IsCentralOptimal M m S₂ Q₂ →
        centralProfit M m S₂ Q₂ ≤ centralProfit M m S₁ Q₁ := by
  obtain ⟨hij, hle_ij, hS₂sym, hS₁sym, hrest⟩ := hraise
  have hdiag : ∀ k, S₁ k k = S₂ k k := by
    intro k
    apply hrest
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hij (h1.symm.trans h2)
    · exact hij (h2.symm.trans h1)
  have hle : ∀ k l, S₁ k l ≤ S₂ k l := by
    intro k l
    by_cases h : (k = i ∧ l = j) ∨ (k = j ∧ l = i)
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hle_ij
      · rw [hS₁sym, hS₂sym]; exact hle_ij
    · exact le_of_eq (hrest k l h)
  have hord := muller_scarsini_normal_sm m S₁ S₂ hS₁ hS₂ hdiag hle
  have part1 : ∀ Q : Fin n → ℝ, (∀ k, 0 ≤ Q k) →
      centralProfit M m S₂ Q ≤ centralProfit M m S₁ Q := by
    intro Q hQ
    obtain ⟨-, hsm, -⟩ := profit_realization_submodular M Q hQ
    have h := hord _ hsm (integrable_profitAt M m S₁ Q).neg (integrable_profitAt M m S₂ Q).neg
    rw [integral_neg, integral_neg] at h
    unfold centralProfit
    linarith
  refine ⟨part1, ?_⟩
  intro Q₁ Q₂ h1 h2
  exact (part1 Q₂ h2.1).trans (h1.2 Q₂ h2.1)
