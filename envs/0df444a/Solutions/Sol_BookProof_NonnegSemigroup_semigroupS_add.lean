-- Prove2me | solution 1 for BookProof.NonnegSemigroup.semigroupS_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-25T15:08:32.521368+00:00
-- url     : https://prove2.me/submissions/f2209ddb-730f-4b1a-a62f-3e6290b56081

-- Generated from ChapterNonnegSemigroup.lean — solution of BookProof.NonnegSemigroup.semigroupS_add
import Mathlib
import Definitions.Def_ChapterNonnegSemigroup
import Theorems.Thm_BookProof_NonnegSemigroup_approxS_add
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterPositiveSquareRootUnique
import Definitions.Def_ChapterNonnegResolvent
import Definitions.Def_ChapterNonnegUnitaryGroup
open BookProof.NonnegSemigroup




open BookProof.ClosureUniqueness BookProof.PositiveSquareRoot BookProof.NonnegResolvent
open BookProof.NonnegUnitaryGroup
open Filter Topology NormedSpace
open scoped InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {T : Submodule ℂ (F × F)}

set_option maxHeartbeats 1000000 in
theorem solution (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    semigroupS hT hsv (add_nonneg hs ht) = semigroupS hT hsv hs * semigroupS hT hsv ht := by

  ext x
  refine tendsto_nhds_unique (tendsto_semigroupS hT hsv (add_nonneg hs ht) x) ?_
  have h : (fun n : ℕ => approxS hT n (s + t) x)
      = fun n : ℕ => approxS hT n s (approxS hT n t x) := by
    funext n
    rw [approxS_add]
    rfl
  rw [h, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₁, hN₁⟩ :=
    Metric.tendsto_atTop.mp (tendsto_semigroupS hT hsv ht x) (ε / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ :=
    Metric.tendsto_atTop.mp (tendsto_semigroupS hT hsv hs (semigroupS hT hsv ht x)) (ε / 2)
      (by linarith)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have h1 : dist (approxS hT n s (approxS hT n t x)) (approxS hT n s (semigroupS hT hsv ht x))
      < ε / 2 := by
    rw [dist_eq_norm, ← map_sub]
    have hb := norm_approxS_apply_le hT n hs (approxS hT n t x - semigroupS hT hsv ht x)
    have := hN₁ n hn1
    rw [dist_eq_norm] at this
    exact lt_of_le_of_lt hb this
  have h2 : dist (approxS hT n s (semigroupS hT hsv ht x))
      (semigroupS hT hsv hs (semigroupS hT hsv ht x)) < ε / 2 := hN₂ n hn2
  calc dist (approxS hT n s (approxS hT n t x))
        (semigroupS hT hsv hs (semigroupS hT hsv ht x))
      ≤ dist (approxS hT n s (approxS hT n t x)) (approxS hT n s (semigroupS hT hsv ht x))
        + dist (approxS hT n s (semigroupS hT hsv ht x))
            (semigroupS hT hsv hs (semigroupS hT hsv ht x)) := dist_triangle _ _ _
    _ < ε := by linarith
