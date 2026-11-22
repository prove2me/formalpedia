-- Prove2me | solution 1 for AvramDividend.Classical.avram_a77_nonpositive_negative_Borel_simpleFunc_approx
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:47:48.759252+00:00
-- url     : https://prove2.me/submissions/be676d36-e5bc-4633-bbbf-2c532b517eba

/- Concrete original negative-mark finite Borel simple quantisation.
   Pinned Mathlib StronglyMeasurable.approx supplies finite-range
   values, and a continuous nonpositive clamp preserves convergence. -/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    (θ : ℝ) (hθ : 0 ≤ θ) :
    ∃ q : ℕ → SimpleFunc ℝ ℝ,
      (∀ n y, q n y ≤ 0) ∧
      (∀ y, y < 0 →
        Tendsto (fun n => q n y) atTop (𝓝 (θ * y))) := by
  classical
  let g : ℝ → ℝ := fun y => min (θ * y) 0
  have hg : StronglyMeasurable g := by
    fun_prop
  let q : ℕ → SimpleFunc ℝ ℝ :=
    fun n => (hg.approx n).map (fun z : ℝ => min z 0)
  refine ⟨q, ?_, ?_⟩
  · intro n y
    change min ((hg.approx n) y) 0 ≤ 0
    exact min_le_right _ _
  · intro y hy
    have hgy : g y = θ * y := by
      dsimp [g]
      exact min_eq_left (mul_nonpos_of_nonneg_of_nonpos hθ (le_of_lt hy))
    have hApprox : Tendsto (fun n => (hg.approx n) y)
        atTop (𝓝 (g y)) := hg.tendsto_approx y
    have hCont : Continuous (fun z : ℝ => min z 0) :=
      continuous_id.min continuous_const
    have hClamp := (hCont.tendsto (g y)).comp hApprox
    change Tendsto (fun n => min ((hg.approx n) y) 0)
      atTop (𝓝 (min (g y) 0)) at hClamp
    simpa only [q, SimpleFunc.coe_map, Function.comp_apply, hgy,
      min_eq_left (mul_nonpos_of_nonneg_of_nonpos hθ (le_of_lt hy))]
      using hClamp

