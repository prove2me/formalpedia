-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.level_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:20.334528+00:00
-- url     : https://prove2.me/submissions/e9013c3c-6665-45a5-9372-ab75e2558596

import Definitions.Def_Formalism_BranchSandwichDivisors_DualLevelType
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_StepDiii
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_OrthSum
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Numeric
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Interlace
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_GoodDual
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_GlobalBoundRefinements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution : LevelIncl := by
  intro O K V0 EE _ _ _ _ _ _ _ _ _ _ _ _ io e0 e1 h1 hc A h hA
  have hc' : ∀ v, io (e0 v) = e1 (io v) := fun v => LinearMap.congr_fun hc v
  have h1' : ∀ v, e1 (e1 v) = e1 v := fun v => LinearMap.congr_fun h1 v
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨a, ⟨haA, ⟨b, hb⟩⟩, rfl⟩
    refine ⟨⟨a, haA, rfl⟩, ⟨io b, ?_⟩⟩
    rw [← hc', hb]; rfl
  · rintro _ ⟨⟨a, haA, rfl⟩, ⟨z, hz⟩⟩
    have hz' : e1 z = io a := hz
    refine ⟨(h : O) • e0 a, ⟨hA a haA, ⟨(h : O) • a, ?_⟩⟩, ?_⟩
    · exact LinearMap.map_smul_of_tower e0 _ _
    · change io ((h : O) • e0 a) = (h : O) • io a
      rw [LinearMap.map_smul_of_tower, hc', ← hz', h1']
  · intro hfg
    exact Submodule.FG.of_le (hfg.map _) inf_le_left
end Formalism.BranchingDeterminantCap
