-- Prove2me | solution 1 for AvramDividend.Classical.cross_sample_finite_coord_law_of_grid_vector_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T14:53:09.809981+00:00
-- url     : https://prove2.me/submissions/14109694-d846-4623-aeac-01cd1f2ff5c3

import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal NNReal

theorem solution
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) (P₂ : Measure Ω₂)
    (Y : Ω₁ → (ℝ≥0 → ℝ)) (Z : Ω₂ → (ℝ≥0 → ℝ))
    (hY : ∀ u : ℝ≥0, Measurable (fun ω => Y ω u))
    (hZ : ∀ u : ℝ≥0, Measurable (fun ω => Z ω u))
    (J : Finset ℝ≥0) (t : ℕ → ℝ≥0) (n : ℕ)
    (henum : ∀ j : J, ∃ i : Fin n, t (i.val + 1) = j.1)
    (hGrid :
      Measure.map (fun ω : Ω₁ => fun i : Fin n => Y ω (t (i.val + 1))) P₁ =
      Measure.map (fun ω : Ω₂ => fun i : Fin n => Z ω (t (i.val + 1))) P₂) :
    Measure.map (fun ω : Ω₁ => fun j : J => Y ω j.1) P₁ =
    Measure.map (fun ω : Ω₂ => fun j : J => Z ω j.1) P₂ := by
  let idx : J → Fin n := fun j => Classical.choose (henum j)
  have hidx : ∀ j : J, t ((idx j).val + 1) = j.1 :=
    fun j => Classical.choose_spec (henum j)
  let g : (Fin n → ℝ) → (J → ℝ) := fun v j => v (idx j)
  have hg : Measurable g := measurable_pi_iff.mpr (fun j => measurable_pi_apply _)
  have keyY : (fun ω : Ω₁ => fun j : J => Y ω j.1) =
      g ∘ (fun ω : Ω₁ => fun i : Fin n => Y ω (t (i.val + 1))) := by
    funext ω j
    change Y ω j.1 = Y ω (t ((idx j).val + 1))
    rw [hidx j]
  have keyZ : (fun ω : Ω₂ => fun j : J => Z ω j.1) =
      g ∘ (fun ω : Ω₂ => fun i : Fin n => Z ω (t (i.val + 1))) := by
    funext ω j
    change Z ω j.1 = Z ω (t ((idx j).val + 1))
    rw [hidx j]
  have hmY : Measurable (fun ω : Ω₁ => fun i : Fin n =>
      Y ω (t (i.val + 1))) :=
    measurable_pi_iff.mpr (fun i => hY _)
  have hmZ : Measurable (fun ω : Ω₂ => fun i : Fin n =>
      Z ω (t (i.val + 1))) :=
    measurable_pi_iff.mpr (fun i => hZ _)
  rw [keyY, keyZ, ← Measure.map_map hg hmY, ← Measure.map_map hg hmZ]
  exact congrArg (Measure.map g) hGrid
