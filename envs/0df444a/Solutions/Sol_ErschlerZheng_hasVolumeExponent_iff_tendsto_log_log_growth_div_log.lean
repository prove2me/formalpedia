-- Prove2me | solution 1 for ErschlerZheng.hasVolumeExponent_iff_tendsto_log_log_growth_div_log
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T12:44:16.808394+00:00
-- url     : https://prove2.me/submissions/8d940d28-42e8-4863-b995-241d8c3d1bb8

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Definitions.Def_ErschlerZheng_Construction
import Definitions.Def_ErschlerZheng_Walks

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

end PathMeasure

/-! ### Item 5: the volume exponent along `ℕ` and along `ℝ` -/

/-- `log ⌊r⌋ / log r → 1`: for `r ⩾ 1`, `0 ⩽ log r - log ⌊r⌋ ⩽ log 2` since `r ⩽ 2⌊r⌋`. -/
theorem tendsto_log_floor_div_log :
    Tendsto (fun r : ℝ => Real.log ⌊r⌋₊ / Real.log r) atTop (𝓝 1) := by
  have h1 : Tendsto (fun r : ℝ => Real.log 2 / Real.log r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hfl : ∀ r : ℝ, 1 ≤ r → 0 < (⌊r⌋₊ : ℝ) ∧ (⌊r⌋₊ : ℝ) ≤ r ∧ r ≤ 2 * ⌊r⌋₊ := by
    intro r hr
    have h0 : 1 ≤ ⌊r⌋₊ := Nat.le_floor (by simpa using hr)
    have h0' : (1 : ℝ) ≤ ⌊r⌋₊ := by exact_mod_cast h0
    refine ⟨by linarith, Nat.floor_le (by linarith), ?_⟩
    have := Nat.lt_floor_add_one r
    linarith
  have h2 : Tendsto (fun r : ℝ => (Real.log r - Real.log ⌊r⌋₊) / Real.log r) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ h1
    · filter_upwards [eventually_ge_atTop 1] with r hr
      obtain ⟨hpos, hle, -⟩ := hfl r hr
      apply div_nonneg _ (Real.log_nonneg hr)
      linarith [Real.log_le_log hpos hle]
    · filter_upwards [eventually_gt_atTop 1] with r hr
      obtain ⟨hpos, -, h2le⟩ := hfl r hr.le
      apply div_le_div_of_nonneg_right _ (Real.log_pos hr).le
      rw [sub_le_iff_le_add, ← Real.log_mul (by norm_num) hpos.ne']
      exact Real.log_le_log (by linarith) h2le
  have h3 := (tendsto_const_nhds (x := (1 : ℝ))).sub h2
  rw [sub_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with r hr
  have := (Real.log_pos hr).ne'
  field_simp
  ring

theorem hasVolumeExponent_iff_tendsto {G : Type*} [Group G] (S : Set G) (α : ℝ) :
    HasVolumeExponent S α ↔
      Tendsto (fun r : ℝ => Real.log (Real.log (growth S r)) / Real.log r) atTop (𝓝 α) := by
  constructor
  · intro h
    set a : ℕ → ℝ := fun n => Real.log (Real.log (growth S n))
    have hg : ∀ r : ℝ, growth S r = growth S (⌊r⌋₊ : ℝ) := by
      intro r; simp only [growth, Nat.floor_natCast]
    have h1 : Tendsto (fun r : ℝ => a ⌊r⌋₊ / Real.log ⌊r⌋₊) atTop (𝓝 α) :=
      h.comp tendsto_nat_floor_atTop
    have h2 := h1.mul tendsto_log_floor_div_log
    rw [mul_one] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with r hr
    have hfl : (2 : ℝ) ≤ ⌊r⌋₊ := by exact_mod_cast Nat.le_floor (by simpa using hr)
    have hne : Real.log ⌊r⌋₊ ≠ 0 := (Real.log_pos (by linarith)).ne'
    simp only [a, hg r]
    field_simp
  · intro h
    exact h.comp tendsto_natCast_atTop_atTop

end NewWalksDev

end ErschlerZheng

end

section
open MeasureTheory Filter Topology
set_option linter.style.haveILetI false
open ErschlerZheng
theorem solution {G : Type*} [Group G]
    (S : Set G) (α : ℝ) :
    HasVolumeExponent S α ↔
      Filter.Tendsto (fun r : ℝ => Real.log (Real.log (growth S r)) / Real.log r) Filter.atTop
        (nhds α) :=
  NewWalksDev.hasVolumeExponent_iff_tendsto S α
end
