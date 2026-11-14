-- Prove2me | solution 1 for ConsistentSubmodular.randomizedTight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:49:00.32862+00:00
-- url     : https://prove2.me/submissions/3ce5870f-fbd9-4af9-90d0-82acc2f50d56

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements
import Theorems.Thm_ConsistentSubmodular_randomizedUpperLimit
import Theorems.Thm_ConsistentSubmodular_randomizedLower

section

open ConsistentSubmodular

theorem solution : RandomizedTightGoal :=
  ⟨randomizedLower, randomizedUpperLimit⟩

end
