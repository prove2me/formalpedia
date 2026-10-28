-- Prove2me | solution 1 for ForecastComp.IELF.elf_uniform_transfer
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:11:07.111574+00:00
-- url     : https://prove2.me/submissions/96bb5964-60ae-4d0c-93d8-2231ec175ead

import Mathlib
import Definitions.Def_ForecastComp_IELF_Model

open MeasureTheory

namespace Aux_IELF_ut
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

lemma sum_one {n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ) (ys : Fin n → ℝ) (x : Bool) :
    ∑ l, elfProb R ys x l = 1 := by
  unfold elfProb
  simp_rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  have hn1 : (n:ℝ) - 1 ≠ 0 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hn0 : (n:ℝ) ≠ 0 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
  field_simp
  ring

lemma diff_i {n : ℕ} (R : ℝ → Bool → ℝ) (v : Fin n → ℝ) (i : Fin n) (y y' : ℝ) (x : Bool) :
    elfProb R (Function.update v i y') x i - elfProb R (Function.update v i y) x i =
      1 / (n:ℝ) * (R y' x - R y x) := by
  unfold elfProb
  simp only [Function.update_self]
  have : ∀ z, ∑ j ∈ Finset.univ.erase i, R (Function.update v i z j) x =
      ∑ j ∈ Finset.univ.erase i, R (v j) x := fun z =>
    Finset.sum_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
  rw [this y, this y']
  ring

lemma diff_j {n : ℕ} (R : ℝ → Bool → ℝ) (v : Fin n → ℝ) (i j : Fin n) (hji : j ≠ i)
    (y y' : ℝ) (x : Bool) :
    elfProb R (Function.update v i y') x j - elfProb R (Function.update v i y) x j =
      -(1 / (n:ℝ) * (R y' x - R y x)) / ((n:ℝ) - 1) := by
  unfold elfProb
  simp only [Function.update_of_ne hji]
  have hmem : i ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨Ne.symm hji, Finset.mem_univ i⟩
  have : ∀ z, ∑ k ∈ Finset.univ.erase j, R (Function.update v i z k) x =
      R z x + ∑ k ∈ (Finset.univ.erase j).erase i, R (v k) x := by
    intro z
    rw [← Finset.add_sum_erase _ _ hmem, Function.update_self]
    congr 1
    exact Finset.sum_congr rfl (fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)])
  rw [this y, this y']
  ring

end Aux_IELF_ut

open ForecastComp.IELF in
theorem solution {n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ)
    (hbdd : IsUnitBounded R) (hmeas : ∀ x, Measurable (fun y => R y x))
    (ν : Measure (Bool × (Fin n → ℝ))) [IsProbabilityMeasure ν]
    (hrep : ∀ᵐ b ∂ν, ∀ j, b.2 j ∈ Set.Icc (0:ℝ) 1) (i : Fin n)
    (y y' : ℝ) (hy : y ∈ Set.Icc (0:ℝ) 1) (hy' : y' ∈ Set.Icc (0:ℝ) 1) :
    (∑ l, ∫ b, elfProb R (Function.update b.2 i y) b.1 l ∂ν) = 1 ∧
    ∀ j, j ≠ i →
      (∫ b, elfProb R (Function.update b.2 i y') b.1 j ∂ν) -
          ∫ b, elfProb R (Function.update b.2 i y) b.1 j ∂ν =
        -((∫ b, elfProb R (Function.update b.2 i y') b.1 i ∂ν) -
            ∫ b, elfProb R (Function.update b.2 i y) b.1 i ∂ν) / ((n:ℝ) - 1) := by
  -- integrability of each score term
  have hk : ∀ z, z ∈ Set.Icc (0:ℝ) 1 → ∀ k,
      Integrable (fun b : Bool × (Fin n → ℝ) => R (Function.update b.2 i z k) b.1) ν := by
    intro z hz k
    have hm : Measurable (fun b : Bool × (Fin n → ℝ) => R (Function.update b.2 i z k) b.1) := by
      apply Aux_IELF_ut.meas_bool (fun (w : Fin n → ℝ) (x : Bool) => R (Function.update w i z k) x)
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
  have hint : ∀ z, z ∈ Set.Icc (0:ℝ) 1 → ∀ l,
      Integrable (fun b : Bool × (Fin n → ℝ) => elfProb R (Function.update b.2 i z) b.1 l) ν := by
    intro z hz l
    unfold elfProb
    exact (integrable_const _).add (((hk z hz l).sub
      ((integrable_finset_sum _ (fun k _ => hk z hz k)).const_mul _)).const_mul _)
  refine ⟨?_, fun j hji => ?_⟩
  · rw [← integral_finset_sum _ (fun l _ => hint y hy l)]
    simp_rw [Aux_IELF_ut.sum_one hn]
    simp
  · rw [← integral_sub (hint y' hy' j) (hint y hy j), ← integral_sub (hint y' hy' i) (hint y hy i)]
    simp_rw [Aux_IELF_ut.diff_j R _ i j hji y y', Aux_IELF_ut.diff_i R _ i y y']
    rw [integral_div, integral_neg]
