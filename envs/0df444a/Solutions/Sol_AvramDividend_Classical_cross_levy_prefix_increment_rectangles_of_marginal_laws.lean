-- Prove2me | solution 1 for AvramDividend.Classical.cross_levy_prefix_increment_rectangles_of_marginal_laws
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:52:24.0668+00:00
-- url     : https://prove2.me/submissions/64a04806-cabc-4448-82ba-70b897e2b2c7

import Mathlib.Probability.IdentDistrib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_levy_finitePrefix_increment_rectangle_product

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hMarginal : ∀ u : ℝ≥0, Measure.map (X.X u) P₁ = Measure.map (Y.X u) P₂)
    (t : ℕ → ℝ≥0) (ht : Monotone t)
    (n : ℕ) (B : Fin n → Set ℝ) (hB : ∀ i, MeasurableSet (B i)) :
    P₁ {ω | (fun i : Fin n =>
      X.X (t (i.val + 1)) ω - X.X (t i.val) ω) ∈
        Set.pi Set.univ B} =
    P₂ {ω | (fun i : Fin n =>
      Y.X (t (i.val + 1)) ω - Y.X (t i.val) ω) ∈
        Set.pi Set.univ B} := by
  have hcomp (i : Fin n) :
      P₁ {ω | X.X (t (i.val + 1)) ω - X.X (t i.val) ω ∈ B i} =
      P₂ {ω | Y.X (t (i.val + 1)) ω - Y.X (t i.val) ω ∈ B i} := by
    have hle : t i.val ≤ t (i.val + 1) := ht (Nat.le_succ _)
    let u : ℝ≥0 := t (i.val + 1) - t i.val
    have hX := X.stationaryIncrements (t i.val) (t (i.val + 1)) hle
    have hY := Y.stationaryIncrements (t i.val) (t (i.val + 1)) hle
    have hLaw : Measure.map
        (fun ω : Ω₁ => X.X (t (i.val + 1)) ω - X.X (t i.val) ω) P₁ =
      Measure.map
        (fun ω : Ω₂ => Y.X (t (i.val + 1)) ω - Y.X (t i.val) ω) P₂ :=
      hX.map_eq.trans ((hMarginal u).trans hY.map_eq.symm)
    have hIdent : IdentDistrib
        (fun ω : Ω₁ => X.X (t (i.val + 1)) ω - X.X (t i.val) ω)
        (fun ω : Ω₂ => Y.X (t (i.val + 1)) ω - Y.X (t i.val) ω)
        P₁ P₂ :=
      ⟨hX.aemeasurable_fst, hY.aemeasurable_fst, hLaw⟩
    exact hIdent.measure_mem_eq (hB i)
  have hprod : (∏ k ∈ Finset.range n,
       P₁ {ω | X.X (t (k + 1)) ω - X.X (t k) ω ∈
         (if hk : k < n then B ⟨k, hk⟩ else univ)}) =
      (∏ k ∈ Finset.range n,
       P₂ {ω | Y.X (t (k + 1)) ω - Y.X (t k) ω ∈
         (if hk : k < n then B ⟨k, hk⟩ else univ)}) := by
    apply Finset.prod_congr rfl
    intro k hk
    have hklt : k < n := Finset.mem_range.mp hk
    simp only [dif_pos hklt]
    exact hcomp ⟨k, hklt⟩
  have hzero : (0 : ℝ≥0) ≤ t 0 := zero_le
  rw [levy_finitePrefix_increment_rectangle_product X 0 t ht hzero n B hB,
      levy_finitePrefix_increment_rectangle_product Y 0 t ht hzero n B hB]
  exact hprod
