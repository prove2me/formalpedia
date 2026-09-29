-- Prove2me | solution 1 for Erdos180.not_erdos_180
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:25:10.405763+00:00
-- url     : https://prove2.me/submissions/ba7575fc-5ff6-47bb-8955-655f19f801cb

import Definitions.Def_erdos180_core4
import Init.Prelude
import Theorems.Thm_Erdos180_proposedFamily_familyLittleO
import Theorems.Thm_Erdos180_proposedFamily_isCyclic
import Theorems.Thm_Erdos180_proposedFamily_nonempty
import Theorems.Thm_Erdos180_proposedFamily_not_compact_of_bounds
import Theorems.Thm_Erdos180_proposedFamily_uniformMemberLower

namespace Erdos180

noncomputable section
open Filter Finset SimpleGraph
open scoped Topology

lemma not_compactnessConjecture_of_bounds
    (hupper : FamilyLittleO proposedFamily)
    (hlower : UniformMemberLower proposedFamily manuscriptLowerConstant) :
    ¬ CompactnessConjectureStatement := by
  intro hconjecture
  exact proposedFamily_not_compact_of_bounds hupper hlower
    (hconjecture proposedFamily proposedFamily_nonempty
      proposedFamily_isCyclic)

end

end Erdos180

open Erdos180
open SimpleGraph

theorem solution :
    ¬ CompactnessConjectureStatement :=
  not_compactnessConjecture_of_bounds
    proposedFamily_familyLittleO proposedFamily_uniformMemberLower
