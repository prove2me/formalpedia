-- Prove2me | solution 1 for ErschlerZheng.isProbabilityMeasure_pathMeasure
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T11:44:25.686768+00:00
-- url     : https://prove2.me/submissions/a48ba3aa-5866-4368-8552-77533294bddd

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Definitions.Def_ErschlerZheng_Construction

section
/-!
# Basic facts about sections, `a`, and the generators `b_ω, c_ω, d_ω`

Development helpers for the Grigorchuk part of the Erschler–Zheng mission (not published).
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace GrigBasic

/-! ### Sections -/

/-! ### The root swap -/

/-! ### `a` and the generators -/

/-! ### Words -/

end GrigBasic

end ErschlerZheng
end

section
/-!
# Walks: facts backing sentences of the notes (not results of the paper)

1. For a non-degenerate `μ`, `HasNontrivialPoissonBoundary μ` is the literal p. 2 criterion
   (moved from `checks/lean/WalksGuards.lean`).
2. The point mass `δ_1` on a non-trivial group: a probability of finite entropy with `h = 0`,
   every function is `δ_1`-harmonic (so the literal criterion holds), and
   `¬ HasNontrivialPoissonBoundary δ_1` (moved from `WalksGuards.lean`, §Degenerate).
3. `μ_β` is non-degenerate (moved from `Dev/P3Goal.lean`).
4. `pathMeasure μ x` is a probability measure when points are measurable: the path map is
   a.e. equal to a map that factors through the countable set `insert 1 (support μ)`.
5. `HasVolumeExponent` along `ℕ` is the same as the limit along real `r`, since
   `log ⌊r⌋ / log r → 1`.
-/

open MeasureTheory Filter Topology

set_option linter.style.haveILetI false

namespace ErschlerZheng

namespace NewWalksDev

/-! ### Item 1: non-degenerate `μ` -/

section Nondegenerate

variable {G : Type*} [Group G]

end Nondegenerate

/-! ### Item 2: the point mass at the identity -/

section Degenerate

variable {G : Type*} [Group G]

end Degenerate

/-! ### Item 3: `μ_β` is non-degenerate -/

section MuBeta

open Garrido

end MuBeta

/-! ### Item 4: `pathMeasure μ x` is a probability measure -/

section PathMeasure

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableSingletonClass G]

omit [Group G] [MeasurableSingletonClass G] in
theorem stepMeasure_apply (μ : G → ℝ) {s : Set G} (hs : MeasurableSet s) :
    stepMeasure μ s = ∑' g, ENNReal.ofReal (μ g) * s.indicator 1 g := by
  unfold stepMeasure
  rw [Measure.sum_apply _ hs]
  congr 1; funext g
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]

omit [Group G] [MeasurableSingletonClass G] in
theorem isProbabilityMeasure_stepMeasure {μ : G → ℝ} (hμ : IsProbability μ) :
    IsProbabilityMeasure (stepMeasure μ) := by
  constructor
  rw [stepMeasure_apply μ MeasurableSet.univ]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg hμ.1 hμ.2.summable, hμ.2.tsum_eq, ENNReal.ofReal_one]

omit [Group G] [MeasurableSingletonClass G] in
/-- The step distribution gives no mass off the support of `μ`. -/
theorem stepMeasure_compl_support (μ : G → ℝ)
    (hS : MeasurableSet (Function.support μ)) : stepMeasure μ (Function.support μ)ᶜ = 0 := by
  rw [stepMeasure_apply μ hS.compl]
  refine ENNReal.tsum_eq_zero.mpr fun g => ?_
  by_cases hg : g ∈ Function.support μ
  · simp [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hg)]
  · rw [Function.notMem_support.mp hg]; simp

/-- The path map is a.e. equal to a measurable map: almost every increment lies in the countable
support `S` of `μ`, and on `S^ℕ` the path map factors through `ξ ↦ (ξ_0, …, ξ_{n-1}) ∈ T^n` with
`T = insert 1 S` countable. -/
theorem aemeasurable_pathMap {μ : G → ℝ} (hμ : IsProbability μ) (x : G) :
    AEMeasurable (fun ξ : ℕ → G => fun n => x * (List.ofFn fun i : Fin n => ξ i).prod)
      (Measure.infinitePi fun _ : ℕ => stepMeasure μ) := by
  classical
  haveI := isProbabilityMeasure_stepMeasure hμ
  set S := Function.support μ with hSdef
  have hSc : S.Countable := hμ.2.summable.countable_support
  have hS : MeasurableSet S := hSc.measurableSet
  set T : Set G := insert 1 S with hTdef
  haveI : Countable T := (hSc.insert 1).to_subtype
  let q : G → G := fun g => if g ∈ S then g else 1
  have hqT : ∀ g, q g ∈ T := fun g => by
    by_cases hg : g ∈ S
    · simp only [q, if_pos hg]; exact Set.mem_insert_of_mem _ hg
    · simp only [q, if_neg hg]; exact Set.mem_insert _ _
  let p : G → T := fun g => ⟨q g, hqT g⟩
  have hq : Measurable q := Measurable.ite hS measurable_id measurable_const
  have hp : Measurable p := hq.subtype_mk
  let F : (ℕ → G) → ℕ → G := fun ξ n => x * (List.ofFn fun i : Fin n => (p (ξ i) : G)).prod
  have hF : Measurable F := by
    apply measurable_pi_lambda
    intro n
    have h1 : Measurable fun ξ : ℕ → G => fun i : Fin n => p (ξ i) :=
      measurable_pi_lambda _ fun i => hp.comp (measurable_pi_apply _)
    exact (measurable_of_countable
      (fun u : Fin n → T => x * (List.ofFn fun i : Fin n => (u i : G)).prod)).comp h1
  have hae : ∀ᵐ ξ ∂(Measure.infinitePi fun _ : ℕ => stepMeasure μ), ∀ i, ξ i ∈ S := by
    rw [ae_all_iff]
    intro i
    have hstep : ∀ᵐ g ∂(stepMeasure μ), g ∈ S := by
      rw [ae_iff]
      exact stepMeasure_compl_support μ hS
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => stepMeasure μ) i).quasiMeasurePreserving.ae
      hstep
  refine ⟨F, hF, ?_⟩
  filter_upwards [hae] with ξ hξ
  funext n
  have : (fun i : Fin n => (p (ξ i) : G)) = fun i : Fin n => ξ i := by
    funext i; simp only [p, q, if_pos (hξ i)]
  simp only [F, this]

theorem isProbabilityMeasure_pathMeasure' {μ : G → ℝ} (hμ : IsProbability μ) (x : G) :
    IsProbabilityMeasure (pathMeasure μ x) := by
  haveI := isProbabilityMeasure_stepMeasure hμ
  exact Measure.isProbabilityMeasure_map (aemeasurable_pathMap hμ x)

end PathMeasure

/-! ### Item 5: the volume exponent along `ℕ` and along `ℝ` -/

end NewWalksDev

end ErschlerZheng

end

section
open MeasureTheory Filter Topology
set_option linter.style.haveILetI false
open ErschlerZheng
theorem solution {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableSingletonClass G] (μ : G → ℝ) (hμ : IsProbability μ) (x : G) :
    MeasureTheory.IsProbabilityMeasure (pathMeasure μ x) :=
  NewWalksDev.isProbabilityMeasure_pathMeasure' hμ x
end
