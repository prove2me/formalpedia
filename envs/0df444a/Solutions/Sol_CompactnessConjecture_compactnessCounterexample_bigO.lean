-- Prove2me | solution 1 for CompactnessConjecture.compactnessCounterexample_bigO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/9528066a-9f83-4f82-95ac-93f606c6e7ce

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_proposedFamily_nonempty
import Theorems.Thm_CompactnessConjecture_proposedFamily_isCyclic
import Theorems.Thm_CompactnessConjecture_manuscriptLowerConstant_pos
import Theorems.Thm_CompactnessConjecture_proposedFamily_uniformMemberLower
import Theorems.Thm_CompactnessConjecture_proposedFamily_not_compact
import Theorems.Thm_CompactnessConjecture_not_erdos_180
import Theorems.Thm_CompactnessConjecture_proposedFamily_member_connected
import Theorems.Thm_CompactnessConjecture_proposedFamily_member_isBipartite
import Theorems.Thm_CompactnessConjecture_proposedFamily_familyExtremal_isBigO

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace CompactnessConjecture
theorem _root_.solution :
    ∃ (family : Finset FiniteGraph) (c : ℝ),
      family.Nonempty ∧
      (∀ forbidden ∈ family,
        forbidden.graph.Connected ∧ forbidden.graph.IsBipartite ∧
          ¬ forbidden.graph.IsAcyclic) ∧
      0 < c ∧
      UniformMemberLower family c ∧
      Asymptotics.IsBigO Filter.atTop
        (fun n : ℕ => (familyExtremal family n : ℝ))
        (fun n : ℕ =>
          (n : ℝ) ^ ((4 : ℝ) / 3 - (1 : ℝ) / 48)) ∧
      ¬ IsCompactFamily family ∧
      ¬ CompactnessConjectureStatement := by
  refine ⟨proposedFamily, manuscriptLowerConstant,
    proposedFamily_nonempty, ?_, manuscriptLowerConstant_pos,
    proposedFamily_uniformMemberLower, ?_, proposedFamily_not_compact,
    not_erdos_180⟩
  · intro forbidden hforbidden
    exact ⟨proposedFamily_member_connected hforbidden,
      proposedFamily_member_isBipartite hforbidden,
      proposedFamily_isCyclic forbidden hforbidden⟩
  · convert proposedFamily_familyExtremal_isBigO using 1
    norm_num
end CompactnessConjecture
