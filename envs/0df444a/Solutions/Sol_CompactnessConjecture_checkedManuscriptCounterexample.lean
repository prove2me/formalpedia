-- Prove2me | solution 1 for CompactnessConjecture.checkedManuscriptCounterexample
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/2af6a916-03d9-4288-86f8-8d96fff89d26

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_proposedFamily_nonempty
import Theorems.Thm_CompactnessConjecture_proposedFamily_isCyclic
import Theorems.Thm_CompactnessConjecture_manuscriptLowerConstant_pos
import Theorems.Thm_CompactnessConjecture_proposedFamilyFree_sixteenth_power_host_bound
import Theorems.Thm_CompactnessConjecture_proposedFamily_uniformMemberLower
import Theorems.Thm_CompactnessConjecture_proposedFamily_not_compact
import Theorems.Thm_CompactnessConjecture_not_erdos_180
import Theorems.Thm_CompactnessConjecture_proposedFamily_member_connected
import Theorems.Thm_CompactnessConjecture_proposedFamily_member_isBipartite
import Theorems.Thm_CompactnessConjecture_proposedFamily_familyExtremal_sixteenth_power_le

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace CompactnessConjecture
theorem _root_.solution :
    proposedFamily.Nonempty ∧
      (∀ forbidden ∈ proposedFamily,
        forbidden.graph.Connected ∧ forbidden.graph.IsBipartite ∧
          ¬ forbidden.graph.IsAcyclic) ∧
      (0 : ℝ) < manuscriptLowerConstant ∧
      UniformMemberLower proposedFamily manuscriptLowerConstant ∧
      (∀ (n : ℕ) (host : SimpleGraph (Fin n)),
        FamilyFree proposedFamily host →
          (host.edgeFinset.card : ℝ) ^ 16 ≤
            compactnessHostPowerConstant * (n : ℝ) ^ 21) ∧
      (∀ n : ℕ,
        (familyExtremal proposedFamily n : ℝ) ^ 16 ≤
          compactnessHostPowerConstant * (n : ℝ) ^ 21) ∧
      (0 : ℝ) < 1 / 48 ∧
      (21 : ℝ) / 16 = (4 : ℝ) / 3 - 1 / 48 ∧
      ¬ IsCompactFamily proposedFamily ∧
      ¬ CompactnessConjectureStatement := by
  refine ⟨proposedFamily_nonempty, ?_,
    manuscriptLowerConstant_pos, proposedFamily_uniformMemberLower,
    proposedFamilyFree_sixteenth_power_host_bound,
    proposedFamily_familyExtremal_sixteenth_power_le,
    by norm_num, by norm_num,
    proposedFamily_not_compact, not_erdos_180⟩
  intro forbidden hforbidden
  exact ⟨proposedFamily_member_connected hforbidden,
    proposedFamily_member_isBipartite hforbidden,
    proposedFamily_isCyclic forbidden hforbidden⟩
end CompactnessConjecture
