-- Prove2me | solution 1 for AvramDividend.Classical.levy_gridPosition_law_implies_finiteIndex_law
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:21:50.541383+00:00
-- url     : https://prove2.me/submissions/bd3ff915-8797-45ac-a9bd-5b3bd6cf0020

import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Constructions.Pi
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (t : ℕ → ℝ≥0) (n : ℕ) (J : Finset ℝ≥0)
    (e : J → Fin n)
    (he : ∀ j : J, t ((e j).val + 1) = (j : ℝ≥0))
    (hGrid :
      Measure.map (fun ω : Ω => fun i : Fin n =>
        X.X (s + t (i.val + 1)) ω - X.X s ω) P =
      Measure.map (fun ω : Ω => fun i : Fin n =>
        X.X (t (i.val + 1)) ω) P) :
    Measure.map (fun ω : Ω => fun j : J =>
      X.X (s + (j : ℝ≥0)) ω - X.X s ω) P =
    Measure.map (fun ω : Ω => fun j : J =>
      X.X (j : ℝ≥0) ω) P := by
  have hm : ∀ r, Measurable (X.X r) := fun r =>
    (X.adapted r).mono (𝓕.le r) le_rfl
  let g : (Fin n → ℝ) → (J → ℝ) := fun f j => f (e j)
  have hg : Measurable g := measurable_pi_lambda _ fun j => measurable_pi_apply _
  have h1 := congrArg (Measure.map g) hGrid
  rw [Measure.map_map hg (measurable_pi_lambda (fun ω (i : Fin n) => X.X (s + t (i.val + 1)) ω - X.X s ω)
      fun i => (hm _).sub (hm _)),
    Measure.map_map hg (measurable_pi_lambda (fun ω (i : Fin n) => X.X (t (i.val + 1)) ω)
      fun i => hm _)] at h1
  convert h1 using 2 <;> funext ω j <;> simp [g, he]
