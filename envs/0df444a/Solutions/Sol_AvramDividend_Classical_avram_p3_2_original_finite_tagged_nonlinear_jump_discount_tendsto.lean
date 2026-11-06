-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_finite_tagged_nonlinear_jump_discount_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T08:43:57.723041+00:00
-- url     : https://prove2.me/submissions/023fcd7d-6acf-446b-bda1-8f3aad468f74

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped BigOperators Topology
noncomputable section

/-- At finitely many genuine tagged jumps, physical-grid nonlinear jump
discounts converge to actual jump-time discounts under original prestates. -/
theorem solution
    (w : ℝ → ℝ) (n : ℕ)
    (z j e d : ℕ → Fin n → ℝ)
    (p a r : Fin n → ℝ)
    (hz : ∀ i, Tendsto (fun k => z k i) atTop (𝓝 (p i)))
    (hj : ∀ i, Tendsto (fun k => j k i) atTop (𝓝 (a i)))
    (he : ∀ i, Tendsto (fun k => e k i) atTop (𝓝 (r i)))
    (hd : ∀ i, Tendsto (fun k => d k i) atTop (𝓝 (r i)))
    (hwp : ∀ i, ContinuousAt w (p i))
    (hwpa : ∀ i, ContinuousAt w (p i - a i)) :
    Tendsto (fun k =>
      (∑ i : Fin n, e k i *
        (w (z k i - j k i) - w (z k i))) -
      (∑ i : Fin n, d k i *
        (w (p i - a i) - w (p i)))) atTop (𝓝 0) := by
  classical
  let G : ℕ → Fin n → ℝ := fun k i =>
    e k i * (w (z k i - j k i) - w (z k i))
  let H : ℕ → Fin n → ℝ := fun k i =>
    d k i * (w (p i - a i) - w (p i))
  have hGrid (i : Fin n) :
      Tendsto (fun k => G k i) atTop
        (𝓝 (r i * (w (p i - a i) - w (p i)))) := by
    dsimp [G]
    exact (he i).mul
      (((hwpa i).tendsto.comp ((hz i).sub (hj i))).sub
        ((hwp i).tendsto.comp (hz i)))
  have hTag (i : Fin n) :
      Tendsto (fun k => H k i) atTop
        (𝓝 (r i * (w (p i - a i) - w (p i)))) := by
    dsimp [H]
    exact (hd i).mul tendsto_const_nhds
  have hCell (i : Fin n) :
      Tendsto (fun k => G k i - H k i) atTop (𝓝 0) := by
    simpa only [sub_self] using (hGrid i).sub (hTag i)
  have hAll (s : Finset (Fin n)) :
      Tendsto (fun k => ∑ i ∈ s, (G k i - H k i))
        atTop (𝓝 0) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      simpa only [zero_add] using (hCell i).add ih
  have h := hAll Finset.univ
  simpa only [G, H, Finset.sum_sub_distrib] using h
