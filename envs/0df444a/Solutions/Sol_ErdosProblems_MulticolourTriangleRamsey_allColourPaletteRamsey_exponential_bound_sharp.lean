-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.allColourPaletteRamsey_exponential_bound_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/4530b7e9-fa0a-41c8-8f43-bbc3eae464ec

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_triangleRamseyNumber_mono
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_recursivePaletteRamsey_exponential_bound
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_paletteLogWidth_two_le
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_log_le_paletteLogWidth
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_paletteColourCount_mono
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_exists_paletteStage_bracket
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_paletteColourCount_adjacent_scaled_sharp
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_palette_exponential_adjacent_transfer_sharp

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (k : ℕ)
    (hk : paletteColourCount 3 ≤ k) :
    ∃ H : ℕ,
      3 ≤ H ∧
      paletteColourCount H ≤ k ∧
      k < paletteColourCount (H + 1) ∧
      ((H : ℝ) / Real.exp 38) ^ k ≤
        (triangleRamseyNumber k : ℝ) := by
  have htwo : paletteColourCount 2 ≤ paletteColourCount 3 :=
    paletteColourCount_mono (by omega) (by omega)
  obtain ⟨H, hH, hlower, hupper⟩ :=
    exists_paletteStage_bracket k (htwo.trans hk)
  have hthree : 3 ≤ H := by
    by_contra hnot
    have htwoeq : H = 2 := by omega
    subst H
    exact (Nat.not_lt_of_ge hk) (by simpa using hupper)
  have hratio :
      paletteLogWidth H * k ≤
        (paletteLogWidth H + 34) * paletteColourCount H := by
    exact (Nat.mul_le_mul_left (paletteLogWidth H)
      (Nat.le_of_lt hupper)).trans
        (paletteColourCount_adjacent_scaled_sharp H hthree)
  refine ⟨H, hthree, hlower, hupper, ?_⟩
  calc
    ((H : ℝ) / Real.exp 38) ^ k ≤
        ((H : ℝ) / Real.exp 4) ^ paletteColourCount H :=
      palette_exponential_adjacent_transfer_sharp H (paletteLogWidth H)
        (paletteColourCount H) k hthree
        (log_le_paletteLogWidth H) hlower hratio
    _ ≤ (triangleRamseyNumber (paletteColourCount H) : ℝ) :=
      by
        simpa [paletteColourCount] using
          recursivePaletteRamsey_exponential_bound H (paletteLogWidth H)
            (by omega) (paletteLogWidth_two_le H) (log_le_paletteLogWidth H)
    _ ≤ (triangleRamseyNumber k : ℝ) := by
      exact_mod_cast triangleRamseyNumber_mono hlower
end ErdosProblems.MulticolourTriangleRamsey
