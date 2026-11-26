-- Prove2me | solution 1 for CSeparatedNPComplete.majorized.sum_convex_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:52:03.024134+00:00
-- url     : https://prove2.me/submissions/945ae015-e9b8-47d6-bacd-dfc30acc98e9

module
public import Definitions.Def_CSeparatedNPComplete_ConvexPredicate
public import Definitions.Def_CSeparatedNPComplete_ConvexSlopes
public import Definitions.Def_CSeparatedNPComplete_WeightedSum
public import Definitions.Def_CSeparatedNPComplete_Karamata
public import Theorems.Thm_CSeparatedNPComplete_exists_antitone_secant_coefficients
public import Theorems.Thm_CSeparatedNPComplete_sum_mul_nonneg_of_antitone_of_prefix_nonneg


set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
namespace majorized
theorem _root_.solution {n : Nat} {u v : Vec n}
    (hmajorized : majorized u v) {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ConvexOn ℝ s f) (hu_mem : ∀ i, u i ∈ s) (hv_mem : ∀ i, v i ∈ s) :
    vecSum (fun i => f (v i)) ≤ vecSum (fun i => f (u i)) := by
  rcases hmajorized with ⟨hu, hv, hprefix, htotal⟩
  obtain ⟨c, hc, hfactor⟩ := exists_antitone_secant_coefficients hf u v
    (fun _ _ hij => hu _ _ hij) (fun _ _ hij => hv _ _ hij) hu_mem hv_mem
  have hsum := sum_mul_nonneg_of_antitone_of_prefix_nonneg
    (fun i => u i - v i) c hc
    (fun k => by
      rw [Finset.sum_sub_distrib]
      exact sub_nonneg.mpr (hprefix k))
    (by
      rw [Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr htotal)
  simp_rw [← hfactor, Finset.sum_sub_distrib] at hsum
  exact sub_nonneg.mp hsum
end majorized
end CSeparatedNPComplete
