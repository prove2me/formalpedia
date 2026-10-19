-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.forcesMonochromaticTriangle_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/499e9fbb-abde-4bea-932e-6a0c41a00c8b

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_cliqueFree_pullback_embedding

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution {m n k : ℕ}
    (hmn : m ≤ n) (hm : ForcesMonochromaticTriangle m k) :
    ForcesMonochromaticTriangle n k := by
  intro C hC
  exact hm (C.pullback (Fin.castLEEmb hmn))
    (cliqueFree_pullback_embedding C (Fin.castLEEmb hmn) hC)
end ErdosProblems.MulticolourTriangleRamsey
