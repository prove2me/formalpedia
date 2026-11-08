-- Prove2me | solution 1 for BidPriceControl.Asymptotic.lemma1_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T10:05:31.802901+00:00
-- url     : https://prove2.me/submissions/15d4a160-0d2f-47c7-8a0d-727839140bb1

import Mathlib
import Definitions.Def_BidPriceControl_Asymptotic_Model

open MeasureTheory ProbabilityTheory

namespace Aux_BPC_l1
open BidPriceControl.Asymptotic

lemma optValue_nonneg {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ)) :
    ∀ t (y : Fin m → ℕ), 0 ≤ optValue A F t y := by
  intro t
  induction t with
  | zero => intro y; simp [optValue]
  | succ t ih =>
    intro y
    simp only [optValue]
    apply integral_nonneg
    intro r
    exact le_trans (ih y) ((Finset.le_fold_max _).mpr (Or.inl le_rfl))

/-- The partial relaxed sum `∑_{s=1}^t ∑_j E(R_s^j − μA^j)^+`. -/
noncomputable def S {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ))
    (μ : Fin m → ℝ) (t : ℕ) : ℝ :=
  ∑ s ∈ Finset.Icc 1 t, ∑ j, ∫ r, max (r j - bidSum A μ j) 0 ∂(F s)

lemma S_nonneg {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ))
    (μ : Fin m → ℝ) (t : ℕ) : 0 ≤ S A F μ t :=
  Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun j _ =>
    integral_nonneg fun r => le_max_right _ _

lemma main {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ))
    (k : ℕ) (hF : ∀ t ∈ Finset.Icc 1 k, IsRequestLaw (F t))
    (μ : Fin m → ℝ) (hμ : 0 ≤ μ) :
    ∀ t, t ≤ k → ∀ y : Fin m → ℕ, optValue A F t y ≤ S A F μ t + ∑ i, μ i * (y i : ℝ) := by
  intro t
  induction t with
  | zero =>
    intro _ y
    simp only [optValue, S, Finset.Icc_self, zero_add]
    have : Finset.Icc 1 0 = ∅ := by decide
    rw [this, Finset.sum_empty, zero_add]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hμ i) (Nat.cast_nonneg _)
  | succ t ih =>
    intro htk y
    have hRL := hF (t + 1) (Finset.mem_Icc.mpr ⟨by omega, htk⟩)
    haveI := hRL.isProbabilityMeasure
    have ih' := ih (by omega)
    set c : ℝ := S A F μ t + ∑ i, μ i * (y i : ℝ) with hc
    have hint : ∀ j, Integrable (fun r : Fin n → ℝ => max (r j - bidSum A μ j) 0) (F (t + 1)) :=
      fun j => ((hRL.integrable_coord j).sub (integrable_const _)).pos_part
    let g : (Fin n → ℝ) → ℝ := fun r => c + ∑ j, max (r j - bidSum A μ j) 0
    have hg : Integrable g (F (t + 1)) :=
      (integrable_const c).add (integrable_finset_sum _ fun j _ => hint j)
    have hle : ∀ r : Fin n → ℝ,
        (Finset.univ.filter (fun j => Fits A y j)).fold max (optValue A F t y)
          (fun j => r j + optValue A F t (y - column A j)) ≤ g r := by
      intro r
      have hsum0 : 0 ≤ ∑ j, max (r j - bidSum A μ j) 0 :=
        Finset.sum_nonneg fun j _ => le_max_right _ _
      rw [Finset.fold_max_le]
      refine ⟨by simp only [g]; linarith [ih' y], ?_⟩
      intro j hj
      rw [Finset.mem_filter] at hj
      have hfit := hj.2
      have h1 := ih' (y - column A j)
      have hcol : ∑ i, μ i * (((y - column A j) i : ℕ) : ℝ)
          = ∑ i, μ i * (y i : ℝ) - bidSum A μ j := by
        unfold bidSum
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Pi.sub_apply, column]
        rw [Nat.cast_sub (hfit i)]
        ring
      rw [hcol] at h1
      have h2 : r j - bidSum A μ j ≤ ∑ j', max (r j' - bidSum A μ j') 0 :=
        le_trans (le_max_left _ _)
          (Finset.single_le_sum (f := fun j' => max (r j' - bidSum A μ j') 0)
            (fun j' _ => le_max_right _ _) (Finset.mem_univ j))
      simp only [g]
      linarith
    have step : optValue A F (t + 1) y ≤ ∫ r, g r ∂(F (t + 1)) := by
      simp only [optValue]
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun r =>
          le_trans (optValue_nonneg A F t y) ((Finset.le_fold_max _).mpr (Or.inl le_rfl))
      · exact hg
      · exact Filter.Eventually.of_forall hle
    have hgi : ∫ r, g r ∂(F (t + 1)) = c + ∑ j, ∫ r, max (r j - bidSum A μ j) 0 ∂(F (t + 1)) := by
      simp only [g]
      rw [integral_add (integrable_const c) (integrable_finset_sum _ fun j _ => hint j),
        integral_finset_sum _ fun j _ => hint j]
      simp
    have hS : S A F μ (t + 1) = S A F μ t + ∑ j, ∫ r, max (r j - bidSum A μ j) 0 ∂(F (t + 1)) := by
      unfold S
      rw [Finset.sum_Icc_succ_top (by omega)]
    rw [hS]
    linarith

end Aux_BPC_l1

open BidPriceControl.Asymptotic in
theorem solution {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ))
    (k : ℕ) (x : Fin m → ℕ) (hF : ∀ t ∈ Finset.Icc 1 k, IsRequestLaw (F t))
    (μ : Fin m → ℝ) (hμ : 0 ≤ μ) :
    optValue A F k x ≤ relaxedValue A F k x μ :=
  Aux_BPC_l1.main A F k hF μ hμ k le_rfl x
