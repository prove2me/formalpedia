-- Prove2me | solution 1 for ClassicalSchur.schur_six_frontier_structure
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-04T00:31:05.610346+00:00
-- url     : https://prove2.me/submissions/89cf824f-26dc-46a0-94be-702ba9950bad

-- Generated from lean/ClassicalSchur/Midpoint.lean
--   imports : 6 platform node(s), 2 definition bundle(s)
--   inlined : 1 file-scoped / sub-threshold helper(s)
--   rename  : schur_six_frontier_structure -> solution, hoisted out of the namespace
import Definitions.Def_ClassicalSchurColoring
import Definitions.Def_ClassicalSchurRamsey
import Theorems.Thm_ClassicalSchur_card_centralNbhd_of_frontier
import Theorems.Thm_ClassicalSchur_card_colorNbhd_centralNbhd_of_frontier
import Theorems.Thm_ClassicalSchur_card_filter_Icc_eq_of_frontier
import Theorems.Thm_ClassicalSchur_color_reflect_of_frontier
import Theorems.Thm_ClassicalSchur_endpointNbhd_of_frontier
import Theorems.Thm_ClassicalSchur_triangleRamsey_succ
import Mathlib

open Finset

namespace ClassicalSchur

/-- `k + 1` colours force a monochromatic triangle on `(k + 1)u + 2` points
when `k` colours force one on `u + 1` points. -/
private theorem triangleRamsey_of_two_mul {k u t : ℕ} (hR : TriangleRamsey k (u + 1))
    (h2t : 2 * t = (k + 1) * u) : TriangleRamsey (k + 1) (2 * t + 2) := by
  have h := triangleRamsey_succ hR
  rwa [Nat.add_sub_cancel, ← h2t] at h

end ClassicalSchur

open ClassicalSchur in
theorem solution (hR : TriangleRamsey 4 61) {c : ℕ → Fin 6}
    (hc : SchurColoring 1801 c) :
    (∀ j, ((Icc 1 900).filter fun d => c d = j).card = 150) ∧
    (centralNbhd c 900).card = 301 ∧
    (∀ v ∈ centralNbhd c 900, ∀ i ≠ c 901, (colorNbhd c (centralNbhd c 900) v i).card = 60) ∧
    (∀ d, 0 < d → d ≤ 900 → c d = c 901 → c (901 - d) = c (901 + d)) ∧
    ∀ i ≠ c 901, (endpointNbhd c 900 i).card = 60 ∧
      (∀ x ∈ endpointNbhd c 900 i, 1800 - x ∈ endpointNbhd c 900 i ∧ 1800 - x ≠ x) ∧
      ∀ x ∈ endpointNbhd c 900 i, ∀ y ∈ endpointNbhd c 900 i, x ≠ y →
        c (Nat.dist x y) ≠ i ∧ c (Nat.dist x y) ≠ c 901 := by
  have hR' : TriangleRamsey 4 (60 + 1) := hR
  have h2t : 2 * 150 = (4 + 1) * 60 := by norm_num
  have hm : 900 = (4 + 2) * 150 := by norm_num
  have hc' : SchurColoring (2 * 900 + 1) c := hc
  exact ⟨card_filter_Icc_eq_of_frontier (triangleRamsey_of_two_mul hR' h2t) hm hc',
    card_centralNbhd_of_frontier hR' h2t hm hc',
    fun v hv i hi => card_colorNbhd_centralNbhd_of_frontier hR' h2t hm hc' hv hi,
    fun d hd hdm hq => color_reflect_of_frontier hR' h2t hm hc' hd hdm hq,
    fun i hi => endpointNbhd_of_frontier hR' h2t hm hc' hi⟩
