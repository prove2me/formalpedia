-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.exists_separated_palette_packing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/b5a69118-ee49-4f08-87e8-9514d3e7e996

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_exists_maximal_separated_palette_cover
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_palette_packing_card_le
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_paletteBall_card_le_binomial_sum

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (N t s : ℕ) (hs : 0 < s) :
    ∃ family : Finset (Finset (Fin N)),
      family ⊆ (Finset.univ : Finset (Fin N)).powersetCard t ∧
      IsPaletteSeparated s family ∧
      N.choose t ≤ family.card *
        (∑ d ∈ Finset.range s, t.choose d * (N - t).choose d) := by
  classical
  obtain ⟨family, hfamily, hseparated, hcover⟩ :=
    exists_maximal_separated_palette_cover
      ((Finset.univ : Finset (Fin N)).powersetCard t) s hs
      (fun P hP Q hQ => (Finset.mem_powersetCard.mp hP).2.trans
        (Finset.mem_powersetCard.mp hQ).2.symm)
  refine ⟨family, hfamily, hseparated, ?_⟩
  have hpacking := palette_packing_card_le
    ((Finset.univ : Finset (Fin N)).powersetCard t) family s
    (∑ d ∈ Finset.range s, t.choose d * (N - t).choose d)
    hcover (fun Q hQ => paletteBall_card_le_binomial_sum N t s Q
      (Finset.mem_powersetCard.mp (hfamily hQ)).2)
  simpa using hpacking
end ErdosProblems.MulticolourTriangleRamsey
