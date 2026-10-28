-- Prove2me | solution 1 for ForecastComp.IELF.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:08:44.964446+00:00
-- url     : https://prove2.me/submissions/9842d3bd-d0ba-45f7-8b86-36223327ff03

import Mathlib
import Definitions.Def_ForecastComp_IELF_Model

open MeasureTheory

namespace Aux_IELF2
open ForecastComp.IELF

lemma bool_eq (f : Bool → ℝ) (x : Bool) :
    f x = f false + (f true - f false) * (if x then 1 else 0) := by
  cases x <;> simp

lemma meas_bool {β : Type*} [MeasurableSpace β] (g : β → Bool → ℝ)
    (hg : ∀ x, Measurable (fun b => g b x)) :
    Measurable (fun b : Bool × β => g b.2 b.1) := by
  have h : (fun b : Bool × β => g b.2 b.1) =
      fun b => if b.1 = true then g b.2 true else g b.2 false := by
    funext b; cases b.1 <;> simp
  rw [h]
  refine Measurable.ite ?_ ((hg true).comp measurable_snd) ((hg false).comp measurable_snd)
  exact measurable_fst (measurableSet_singleton true)

end Aux_IELF2

open ForecastComp.IELF in
theorem solution {n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ)
    (hprop : IsStrictlyProper R) (hbdd : IsUnitBounded R)
    (hmeas : ∀ x, Measurable (fun y => R y x))
    (i : Fin n) (p : ℝ) (ν : Measure (Bool × (Fin n → ℝ))) [IsProbabilityMeasure ν]
    (hmean : ∫ b, (if b.1 then (1:ℝ) else 0) ∂ν = p)
    (hrep : ∀ᵐ b ∂ν, ∀ j, b.2 j ∈ Set.Icc (0:ℝ) 1)
    (y' : ℝ) (hy' : y' ∈ Set.Icc (0:ℝ) 1) (hne : y' ≠ p) :
    ∫ b, elfProb R (Function.update b.2 i y') b.1 i ∂ν <
      ∫ b, elfProb R (Function.update b.2 i p) b.1 i ∂ν := by
  -- indicator facts
  have hind_meas : Measurable (fun b : Bool × (Fin n → ℝ) => if b.1 then (1:ℝ) else 0) := by
    have := Aux_IELF2.meas_bool (fun (_ : Fin n → ℝ) (x : Bool) => if x then (1:ℝ) else 0)
      (fun x => measurable_const)
    exact this
  have hind_int : Integrable (fun b : Bool × (Fin n → ℝ) => if b.1 then (1:ℝ) else 0) ν := by
    refine Integrable.of_bound hind_meas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun b => ?_))
    cases b.1 <;> simp
  have hp : p ∈ Set.Icc (0:ℝ) 1 := by
    rw [← hmean]
    constructor
    · exact integral_nonneg (fun b => by cases b.1 <;> simp)
    · calc ∫ b, (if b.1 then (1:ℝ) else 0) ∂ν ≤ ∫ _b, (1:ℝ) ∂ν :=
            integral_mono hind_int (integrable_const _) (fun b => by cases b.1 <;> simp)
        _ = 1 := by simp
  -- integrals of R y b.1
  have hRint : ∀ y, Integrable (fun b : Bool × (Fin n → ℝ) => R y b.1) ν := by
    intro y
    have hm := Aux_IELF2.meas_bool (fun (_ : Fin n → ℝ) (x : Bool) => R y x)
      (fun x => measurable_const)
    refine Integrable.of_bound hm.aestronglyMeasurable (|R y true| + |R y false|)
      (Filter.Eventually.of_forall (fun b => ?_))
    rw [Real.norm_eq_abs]
    cases b.1 <;> linarith [abs_nonneg (R y true), abs_nonneg (R y false)]
  have hRval : ∀ y, ∫ b, R y b.1 ∂ν = expScore R y p := by
    intro y
    have h1 : (fun b : Bool × (Fin n → ℝ) => R y b.1) = fun b =>
        R y false + (R y true - R y false) * (if b.1 then (1:ℝ) else 0) := by
      funext b; exact Aux_IELF2.bool_eq (R y) b.1
    rw [h1, integral_add (integrable_const _) (hind_int.const_mul _), integral_const,
      probReal_univ, one_smul, integral_const_mul, hmean]
    unfold expScore; ring
  -- the other forecasters' term
  set D : Bool × (Fin n → ℝ) → ℝ := fun b =>
    1 / ((n:ℝ) - 1) * ∑ j ∈ Finset.univ.erase i, R (b.2 j) b.1 with hD
  have hDint : Integrable D ν := by
    apply Integrable.const_mul
    apply integrable_finset_sum
    intro j _
    have hm := Aux_IELF2.meas_bool (fun (v : Fin n → ℝ) (x : Bool) => R (v j) x)
      (fun x => (hmeas x).comp (measurable_pi_apply j))
    refine Integrable.of_bound hm.aestronglyMeasurable 1 ?_
    filter_upwards [hrep] with b hb
    rw [Real.norm_eq_abs, abs_le]
    have := hbdd (b.2 j) (hb j) b.1
    constructor <;> linarith [this.1, this.2]
  have hF : ∀ y, (fun b : Bool × (Fin n → ℝ) => elfProb R (Function.update b.2 i y) b.1 i) =
      fun b => 1 / (n:ℝ) + 1 / (n:ℝ) * (R y b.1 - D b) := by
    intro y
    funext b
    unfold elfProb
    simp only [Function.update_self, hD]
    rw [Finset.sum_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])]
  have hFint : ∀ y, ∫ b, elfProb R (Function.update b.2 i y) b.1 i ∂ν =
      1 / (n:ℝ) + 1 / (n:ℝ) * (expScore R y p - ∫ b, D b ∂ν) := by
    intro y
    have hI : Integrable (fun b => 1 / (n:ℝ) * (R y b.1 - D b)) ν :=
      ((hRint y).sub hDint).const_mul _
    rw [hF y, integral_add (integrable_const _) hI,
      integral_const, probReal_univ, one_smul, integral_const_mul, integral_sub (hRint y) hDint,
      hRval]
  rw [hFint, hFint]
  have hlt := hprop p hp y' hy' hne
  have hnpos : (0:ℝ) < 1 / (n:ℝ) := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    positivity
  nlinarith
