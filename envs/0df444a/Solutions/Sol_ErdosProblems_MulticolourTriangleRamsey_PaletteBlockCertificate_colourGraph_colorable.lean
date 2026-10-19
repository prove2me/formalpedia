-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.PaletteBlockCertificate.colourGraph_colorable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/242b3f74-029f-4d6e-98d7-e1800f2dcf78

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
open ErdosProblems.MulticolourTriangleRamsey.PaletteBlockCertificate
namespace ErdosProblems.MulticolourTriangleRamsey.PaletteBlockCertificate
theorem _root_.solution {I V K : Type*} [DecidableEq K]
    {C : SimpleGraph.TopEdgeLabeling (I × V) K} {j : ℕ}
    (certificate : PaletteBlockCertificate C j) (colour : K) :
    (C.labelGraph colour).Colorable (j + 1) := by
  classical
  refine ⟨SimpleGraph.Coloring.mk (globalLabel certificate colour) ?_⟩
  intro x y hadj
  rcases x with ⟨i, u⟩
  rcases y with ⟨i', v⟩
  by_cases hs : i = i'
  · subst i'
    by_cases hmissing : colour ∈ certificate.palette i
    · exact False.elim
        (certificate.missing_has_no_internal_edge i colour hmissing u v hadj)
    · have hproper := certificate.internal_labels_proper
        i colour hmissing u v hadj
      simp only [globalLabel, dif_neg hmissing]
      exact fun heq => hproper (Fin.castSucc_inj.mp heq)
  · have hchange := certificate.cross_edge_changes_membership
      i i' colour u v hs hadj
    by_cases hi : colour ∈ certificate.palette i
    · have hi' : colour ∉ certificate.palette i' := by
        intro h
        exact hchange (propext ⟨fun _ => h, fun _ => hi⟩)
      simp only [globalLabel, dif_pos hi, dif_neg hi']
      exact Ne.symm (Fin.castSucc_ne_last _)
    · have hi' : colour ∈ certificate.palette i' := by
        by_contra h
        exact hchange (propext ⟨fun h' => (hi h').elim, fun h' => (h h').elim⟩)
      simp only [globalLabel, dif_neg hi, dif_pos hi']
      exact Fin.castSucc_ne_last _
end ErdosProblems.MulticolourTriangleRamsey.PaletteBlockCertificate
