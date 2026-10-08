-- Prove2me | solution 1 for ErschlerZheng.isProbability_and_hasFiniteEntropy_and_asymptoticEntropy_eq_zero_and_forall_isHarmonic_and_exists_bounded_isHarmonic_ne_and_not_hasNontrivialPoissonBoundary_indicator_singleton_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T11:44:25.379+00:00
-- url     : https://prove2.me/submissions/d017a095-3d4c-4db8-ab5b-77f7ddad94b6

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

open scoped Classical in
/-- The point mass at `a`. -/
noncomputable def delta (a : G) : G → ℝ := fun g => if g = a then 1 else 0

theorem indicator_singleton_one_eq_delta : (Set.indicator {1} 1 : G → ℝ) = delta 1 := by
  funext g
  by_cases h : g = 1 <;> simp [delta, h]

open scoped Classical in
/-- Convolution of point masses: `δ_a ⋆ δ_b = δ_{ab}`. -/
theorem conv_delta (a b : G) : conv (delta a) (delta b) = delta (a * b) := by
  funext g
  simp only [conv, delta]
  rw [tsum_eq_single a]
  · by_cases h : g = a * b
    · subst h; simp
    · have : a⁻¹ * g ≠ b := by
        intro h'; apply h; rw [← h']; group
      simp [h, this]
  · intro c hc; simp [hc]

open scoped Classical in
/-- `μ^{(0)}` is the point mass at the identity. -/
theorem convPow_zero (μ : G → ℝ) : convPow μ 0 = delta (1 : G) := by
  funext g; simp [convPow, delta]

/-- Powers of a point mass: `δ_1^{(n)} = δ_1`. -/
theorem convPow_delta_one (n : ℕ) : convPow (delta (1 : G)) n = delta (1 : G) := by
  induction n with
  | zero => exact convPow_zero _
  | succ n ih => rw [convPow, ih, conv_delta, one_mul]

omit [Group G] in
theorem entropy_delta (a : G) : entropy (delta a) = 0 := by
  classical
  have : (fun g => Real.negMulLog (delta a g)) = fun _ => 0 := by
    funext g; by_cases h : g = a <;> simp [delta, h]
  simp [entropy, this]

omit [Group G] in
theorem isProbability_delta (a : G) : IsProbability (delta a) := by
  classical
  refine ⟨fun g => by by_cases h : g = a <;> simp [delta, h], ?_⟩
  convert hasSum_ite_eq a (1 : ℝ) using 1
  funext g
  by_cases hg : g = a <;> simp [delta, hg]

omit [Group G] in
theorem hasFiniteEntropy_delta (a : G) : HasFiniteEntropy (delta a) := by
  classical
  have : (fun g => Real.negMulLog (delta a g)) = fun _ => 0 := by
    funext g; by_cases h : g = a <;> simp [delta, h]
  rw [HasFiniteEntropy, this]
  exact summable_zero

/-- Every function is `δ_1`-harmonic. -/
theorem isHarmonic_delta_one (f : G → ℝ) : IsHarmonic (delta (1 : G)) f := by
  classical
  intro x
  rw [tsum_eq_single 1]
  · simp [delta]
  · intro y hy; simp [delta, hy]

/-- On a non-trivial group, `δ_1` itself is a bounded, `δ_1`-harmonic, non-constant function. -/
theorem exists_bounded_isHarmonic_ne_delta_one [Nontrivial G] :
    ∃ f : G → ℝ, (∃ C, ∀ x, |f x| ≤ C) ∧ IsHarmonic (delta (1 : G)) f ∧ ∃ x y, f x ≠ f y := by
  classical
  obtain ⟨a, ha⟩ := exists_ne (1 : G)
  refine ⟨delta 1, ⟨1, fun x => ?_⟩, isHarmonic_delta_one _, 1, a, ?_⟩
  · by_cases h : x = 1 <;> simp [delta, h]
  · simp [delta, ha]

theorem asymptoticEntropy_delta_one : asymptoticEntropy (delta (1 : G)) = 0 := by
  have : (fun n : ℕ => entropy (convPow (delta (1 : G)) n) / n) = fun _ => 0 := by
    funext n; rw [convPow_delta_one, entropy_delta, zero_div]
  rw [asymptoticEntropy, this]
  exact tendsto_const_nhds.limUnder_eq

/-- `δ_1` has trivial Poisson boundary: the submonoid generated by its support is `{1}`. -/
theorem not_hasNontrivialPoissonBoundary_delta_one :
    ¬ HasNontrivialPoissonBoundary (delta (1 : G)) := by
  classical
  rintro ⟨f, -, -, x, hx, y, hy, hxy⟩
  have hsupp : Function.support (delta (1 : G)) = {1} := by
    ext g; by_cases hg : g = 1 <;> simp [delta, hg]
  rw [hsupp, Submonoid.closure_singleton_one, Submonoid.mem_bot] at hx hy
  exact hxy (by rw [hx, hy])

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

end NewWalksDev

end ErschlerZheng

end

section
open MeasureTheory Filter Topology
set_option linter.style.haveILetI false
open ErschlerZheng
theorem solution
    {G : Type*} [Group G] [Nontrivial G] :
    IsProbability (Set.indicator {1} 1 : G → ℝ) ∧ HasFiniteEntropy (Set.indicator {1} 1 : G → ℝ) ∧
      asymptoticEntropy (Set.indicator {1} 1 : G → ℝ) = 0 ∧
      (∀ f : G → ℝ, IsHarmonic (Set.indicator {1} 1) f) ∧
      (∃ f : G → ℝ, (∃ C, ∀ x, |f x| ≤ C) ∧ IsHarmonic (Set.indicator {1} 1) f ∧
        ∃ x y, f x ≠ f y) ∧
      ¬ HasNontrivialPoissonBoundary (Set.indicator {1} 1 : G → ℝ) := by
  rw [NewWalksDev.indicator_singleton_one_eq_delta]
  exact ⟨NewWalksDev.isProbability_delta 1, NewWalksDev.hasFiniteEntropy_delta 1,
    NewWalksDev.asymptoticEntropy_delta_one, NewWalksDev.isHarmonic_delta_one,
    NewWalksDev.exists_bounded_isHarmonic_ne_delta_one,
    NewWalksDev.not_hasNontrivialPoissonBoundary_delta_one⟩
end
