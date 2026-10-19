-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.paletteBall_card_le_binomial_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/9dbc74f0-48d7-44c3-977e-3f7bcce67c06

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_paletteShell_card_le

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (N t s : ℕ)
    (Q : Finset (Fin N)) (hQ : Q.card = t) :
    (paletteBall ((Finset.univ : Finset (Fin N)).powersetCard t) Q s).card ≤
      ∑ d ∈ Finset.range s, t.choose d * (N - t).choose d := by
  classical
  let ambient : Finset (Finset (Fin N)) :=
    (Finset.univ : Finset (Fin N)).powersetCard t
  have hsubset :
      paletteBall ambient Q s ⊆
        (Finset.range s).biUnion (fun d => paletteShell N t Q d) := by
    intro P hP
    have hP' : P ∈ ambient ∧ (P \ Q).card < s := by
      simpa [paletteBall] using hP
    apply Finset.mem_biUnion.mpr
    refine ⟨(P \ Q).card, Finset.mem_range.mpr hP'.2, ?_⟩
    simpa [paletteShell, ambient] using hP'.1
  calc
    (paletteBall ambient Q s).card ≤
        ((Finset.range s).biUnion (fun d => paletteShell N t Q d)).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ d ∈ Finset.range s, (paletteShell N t Q d).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ d ∈ Finset.range s, t.choose d * (N - t).choose d := by
      exact Finset.sum_le_sum fun d _ => paletteShell_card_le N t d Q hQ
end ErdosProblems.MulticolourTriangleRamsey
