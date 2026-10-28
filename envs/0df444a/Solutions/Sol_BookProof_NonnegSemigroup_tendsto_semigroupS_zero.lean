-- Prove2me | solution 1 for BookProof.NonnegSemigroup.tendsto_semigroupS_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-25T15:08:35.924752+00:00
-- url     : https://prove2.me/submissions/15fd604a-b453-4631-b9a9-b19ec3a3832b

-- Generated from ChapterNonnegSemigroup.lean — solution of BookProof.NonnegSemigroup.tendsto_semigroupS_zero
import Mathlib
import Definitions.Def_ChapterNonnegSemigroup
import Theorems.Thm_BookProof_NonnegSemigroup_norm_semigroupS_apply_le
import Theorems.Thm_BookProof_NonnegSemigroup_norm_semigroupS_sub_self_le_of_mem
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
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) (x : F) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (t : ℝ) (ht : 0 ≤ t), t < δ → ‖semigroupS hT hsv ht x - x‖ < ε := by

  obtain ⟨z, hz, hxz⟩ := (dense_domain hT hsv).exists_dist_lt x (ε := ε / 4) (by linarith)
  obtain ⟨p, hp, hp1⟩ := Submodule.mem_map.1 hz
  have hpy : (z, p.2) ∈ T := by
    have hpe : p = (z, p.2) := by rw [← hp1]; simp
    rwa [← hpe]
  refine ⟨ε / (4 * (‖p.2‖ + 1)), by positivity, fun t ht htδ => ?_⟩
  have hzx : ‖x - z‖ < ε / 4 := by rwa [← dist_eq_norm]
  have h1 : ‖semigroupS hT hsv ht x - semigroupS hT hsv ht z‖ ≤ ‖x - z‖ := by
    rw [← map_sub]
    exact norm_semigroupS_apply_le hT hsv ht _
  have h2 : ‖semigroupS hT hsv ht z - z‖ ≤ t * ‖p.2‖ :=
    norm_semigroupS_sub_self_le_of_mem hT hsv hpy ht
  have h3 : t * ‖p.2‖ < ε / 4 := by
    have hb : t * ‖p.2‖ ≤ t * (‖p.2‖ + 1) := by nlinarith [norm_nonneg p.2]
    have : t * (‖p.2‖ + 1) < ε / 4 := by
      have hlt : t < ε / (4 * (‖p.2‖ + 1)) := htδ
      have hpos : (0 : ℝ) < ‖p.2‖ + 1 := by positivity
      rw [lt_div_iff₀ (by positivity)] at hlt
      nlinarith
    linarith
  have h4 : ‖z - x‖ < ε / 4 := by rw [norm_sub_rev]; exact hzx
  calc ‖semigroupS hT hsv ht x - x‖
      ≤ ‖semigroupS hT hsv ht x - semigroupS hT hsv ht z‖
        + ‖semigroupS hT hsv ht z - z‖ + ‖z - x‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub (semigroupS hT hsv ht x)
          (semigroupS hT hsv ht z) z
        have h5 := norm_sub_le_norm_sub_add_norm_sub (semigroupS hT hsv ht x) z x
        linarith
    _ < ε := by linarith
