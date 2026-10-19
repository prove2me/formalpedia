-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.no_three_pairwise_palette_disagreements
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/96206249-c596-44af-ae1c-c1bcc91abbb0

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution {α : Type*}
    (P Q R : Finset α) (colour : α)
    (hPQ : (colour ∈ P) ≠ (colour ∈ Q))
    (hQR : (colour ∈ Q) ≠ (colour ∈ R))
    (hRP : (colour ∈ R) ≠ (colour ∈ P)) : False := by
  classical
  by_cases hP : colour ∈ P <;>
    by_cases hQ : colour ∈ Q <;>
      by_cases hR : colour ∈ R <;>
        simp_all
end ErdosProblems.MulticolourTriangleRamsey
