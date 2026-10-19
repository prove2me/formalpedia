-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.PaletteBlockCertificate.noMonochromaticTriangle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/0c1a3e6c-8b7a-4d7a-a76d-59dfba5657f2

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_no_three_pairwise_palette_disagreements

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
open ErdosProblems.MulticolourTriangleRamsey.PaletteBlockCertificate
namespace ErdosProblems.MulticolourTriangleRamsey.PaletteBlockCertificate
theorem _root_.solution {I V K : Type*} [DecidableEq K]
    {C : SimpleGraph.TopEdgeLabeling (I × V) K} {j : ℕ}
    (certificate : PaletteBlockCertificate C j) :
    ∀ colour : K, (C.labelGraph colour).CliqueFree 3 := by
  classical
  intro colour t ht
  obtain ⟨x, y, z, hxy, hxz, hyz, _⟩ :=
    (SimpleGraph.is3Clique_iff).mp ht
  rcases x with ⟨i, u⟩
  rcases y with ⟨i', v⟩
  rcases z with ⟨i'', w⟩
  by_cases hii' : i = i'
  · subst i'
    by_cases hii'' : i = i''
    · subst i''
      exact certificate.internal_no_triangle i colour u v w ⟨hxy, hxz, hyz⟩
    · by_cases hmissing : colour ∈ certificate.palette i
      · exact certificate.missing_has_no_internal_edge i colour hmissing u v hxy
      · have hequal := certificate.cross_edges_force_equal_active_labels
          i i'' colour u v w hii'' hmissing hxz hyz
        exact certificate.internal_labels_proper
          i colour hmissing u v hxy hequal
  · by_cases hii'' : i = i''
    · subst i''
      by_cases hmissing : colour ∈ certificate.palette i
      · exact certificate.missing_has_no_internal_edge i colour hmissing u w hxz
      · have hequal := certificate.cross_edges_force_equal_active_labels
          i i' colour u w v hii' hmissing hxy hyz.symm
        exact certificate.internal_labels_proper
          i colour hmissing u w hxz hequal
    · by_cases hi'i'' : i' = i''
      · subst i''
        by_cases hmissing : colour ∈ certificate.palette i'
        · exact certificate.missing_has_no_internal_edge
            i' colour hmissing v w hyz
        · have hequal := certificate.cross_edges_force_equal_active_labels
            i' i colour v w u (Ne.symm hii') hmissing hxy.symm hxz.symm
          exact certificate.internal_labels_proper
            i' colour hmissing v w hyz hequal
      · exact no_three_pairwise_palette_disagreements
          (certificate.palette i) (certificate.palette i')
          (certificate.palette i'') colour
          (certificate.cross_edge_changes_membership
            i i' colour u v hii' hxy)
          (certificate.cross_edge_changes_membership
            i' i'' colour v w hi'i'' hyz)
          (certificate.cross_edge_changes_membership
            i'' i colour w u (Ne.symm hii'') hxz.symm)
end ErdosProblems.MulticolourTriangleRamsey.PaletteBlockCertificate
