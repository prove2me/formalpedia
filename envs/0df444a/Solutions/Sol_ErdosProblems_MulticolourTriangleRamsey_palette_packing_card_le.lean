-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.palette_packing_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/e86b9a5a-db1f-4b98-869b-8269303ace54

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution {α : Type*} [DecidableEq α]
    (ambient family : Finset (Finset α)) (s ballBound : ℕ)
    (hcover : ∀ P ∈ ambient, ∃ Q ∈ family, (P \ Q).card < s)
    (hball : ∀ Q ∈ family, (paletteBall ambient Q s).card ≤ ballBound) :
    ambient.card ≤ family.card * ballBound := by
  classical
  have hsubset : ambient ⊆ family.biUnion (fun Q => paletteBall ambient Q s) := by
    intro P hP
    obtain ⟨Q, hQ, hclose⟩ := hcover P hP
    exact Finset.mem_biUnion.mpr ⟨Q, hQ, by simp [paletteBall, hP, hclose]⟩
  calc
    ambient.card ≤ (family.biUnion (fun Q => paletteBall ambient Q s)).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ Q ∈ family, (paletteBall ambient Q s).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _Q ∈ family, ballBound :=
      Finset.sum_le_sum fun Q hQ => hball Q hQ
    _ = family.card * ballBound := by simp
end ErdosProblems.MulticolourTriangleRamsey
