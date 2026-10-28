-- Prove2me | solution 1 for ForecastComp.IELF.belief_indep_factorization
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:14:01.957169+00:00
-- url     : https://prove2.me/submissions/cb9bffd0-60fc-49da-a153-e989f664cf68

import Mathlib
import Definitions.Def_ForecastComp_IELF_Model

open MeasureTheory

namespace Aux_IELF_bif
open ForecastComp.IELF

lemma meas_bool {β : Type*} [MeasurableSpace β] (g : β → Bool → ℝ)
    (hg : ∀ x, Measurable (fun b => g b x)) :
    Measurable (fun b : Bool × β => g b.2 b.1) := by
  have h : (fun b : Bool × β => g b.2 b.1) =
      fun b => if b.1 = true then g b.2 true else g b.2 false := by
    funext b; cases b.1 <;> simp
  rw [h]
  refine Measurable.ite ?_ ((hg true).comp measurable_snd) ((hg false).comp measurable_snd)
  exact measurable_fst (measurableSet_singleton true)

lemma int_elf {n : ℕ} (R : ℝ → Bool → ℝ) (hbdd : IsUnitBounded R)
    (hmeas : ∀ x, Measurable (fun y => R y x))
    (ν : Measure (Bool × (Fin n → ℝ))) [IsProbabilityMeasure ν]
    (hrep : ∀ᵐ b ∂ν, ∀ j, b.2 j ∈ Set.Icc (0:ℝ) 1) (i : Fin n) (z : ℝ)
    (hz : z ∈ Set.Icc (0:ℝ) 1) (l : Fin n) :
    Integrable (fun b : Bool × (Fin n → ℝ) => elfProb R (Function.update b.2 i z) b.1 l) ν := by
  have hk : ∀ k,
      Integrable (fun b : Bool × (Fin n → ℝ) => R (Function.update b.2 i z k) b.1) ν := by
    intro k
    have hm : Measurable (fun b : Bool × (Fin n → ℝ) => R (Function.update b.2 i z k) b.1) := by
      apply meas_bool (fun (w : Fin n → ℝ) (x : Bool) => R (Function.update w i z k) x)
      intro x
      by_cases hki : k = i
      · subst hki
        simp only [Function.update_self]
        exact measurable_const
      · simp only [Function.update_of_ne hki]
        exact (hmeas x).comp (measurable_pi_apply k)
    refine Integrable.of_bound hm.aestronglyMeasurable 1 ?_
    filter_upwards [hrep] with b hb
    have hmem : Function.update b.2 i z k ∈ Set.Icc (0:ℝ) 1 := by
      by_cases hki : k = i
      · subst hki; rw [Function.update_self]; exact hz
      · rw [Function.update_of_ne hki]; exact hb k
    have := hbdd _ hmem b.1
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [this.1, this.2]
  unfold elfProb
  exact (integrable_const _).add (((hk l).sub
    ((integrable_finset_sum _ (fun k _ => hk k)).const_mul _)).const_mul _)

end Aux_IELF_bif

open ForecastComp.IELF in
theorem solution {m n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ)
    (hbdd : IsUnitBounded R) (hmeas : ∀ x, Measurable (fun y => R y x))
    (ν : Fin m → Measure (Bool × (Fin n → ℝ))) [∀ k, IsProbabilityMeasure (ν k)]
    (hrep : ∀ k, ∀ᵐ b ∂(ν k), ∀ j, b.2 j ∈ Set.Icc (0:ℝ) 1)
    (i : Fin n) (yi : Fin m → ℝ) (hyi : ∀ k, yi k ∈ Set.Icc (0:ℝ) 1) :
    ∫ ω, ielfSelProb R (Function.update (reportsOf ω) i yi) (outcomeOf ω) i ∂(Measure.pi ν) =
      winProbOf (fun k l => ∫ b, elfProb R (Function.update b.2 i (yi k)) b.1 l ∂(ν k)) i := by
  have hfun : ∀ (ω : Fin m → Bool × (Fin n → ℝ)) k,
      (fun j => Function.update (reportsOf ω) i yi j k) = Function.update (ω k).2 i (yi k) := by
    intro ω k
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj, reportsOf]
  have hrw : (fun ω : Fin m → Bool × (Fin n → ℝ) =>
      ielfSelProb R (Function.update (reportsOf ω) i yi) (outcomeOf ω) i) =
      fun ω => ∑ w : Fin m → Fin n, (∏ k, (fun b : Bool × (Fin n → ℝ) =>
        elfProb R (Function.update b.2 i (yi k)) b.1 (w k)) (ω k)) * tieShare w i := by
    funext ω
    unfold ielfSelProb winProbOf
    refine Finset.sum_congr rfl (fun w _ => ?_)
    congr 1
    refine Finset.prod_congr rfl (fun k _ => ?_)
    simp only [hfun ω k, outcomeOf]
  rw [hrw, integral_finset_sum]
  · unfold winProbOf
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [integral_mul_const]
    congr 1
    exact integral_fintype_prod_eq_prod (𝕜 := ℝ) (E := fun _ => Bool × (Fin n → ℝ))
      (fun k (b : Bool × (Fin n → ℝ)) => elfProb R (Function.update b.2 i (yi k)) b.1 (w k))
  · intro w _
    apply Integrable.mul_const
    exact Integrable.fintype_prod (fun k =>
      Aux_IELF_bif.int_elf R hbdd hmeas (ν k) (hrep k) i (yi k) (hyi k) (w k))
