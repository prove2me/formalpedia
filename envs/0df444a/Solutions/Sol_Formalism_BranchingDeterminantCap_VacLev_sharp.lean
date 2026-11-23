-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.VacLev.sharp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:58.428714+00:00
-- url     : https://prove2.me/submissions/059793cb-e706-406b-a0e0-3d205e649ef2

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
import Theorems.Thm_Formalism_BranchingDeterminantCap_level_inclusion
import Theorems.Thm_Formalism_BranchingDeterminantCap_VacLev_hyp1
import Theorems.Thm_Formalism_BranchingDeterminantCap_VacLev_hyp2
import Theorems.Thm_Formalism_BranchingDeterminantCap_VacLev_hyp3

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
open Formalism.BranchingDeterminantCap.VacLev
namespace Formalism.BranchingDeterminantCap.VacLev
theorem _root_.solution :
    (1 : ℚ) ∈ A.map (io.restrictScalars ℤ) ⊓
      (LinearMap.range (LinearMap.id : ℚ →ₗ[ℚ] ℚ)).restrictScalars ℤ ∧
    (1 : ℚ) ∉ (A ⊓ (LinearMap.range e0).restrictScalars ℤ).map (io.restrictScalars ℤ) ∧
    ((2 : ℕ) : ℤ) • (1 : ℚ) ∈
      (A ⊓ (LinearMap.range e0).restrictScalars ℤ).map (io.restrictScalars ℤ) := by
  have m1 : (1 : ℚ) ∈ A.map (io.restrictScalars ℤ) ⊓
      (LinearMap.range (LinearMap.id : ℚ →ₗ[ℚ] ℚ)).restrictScalars ℤ :=
    ⟨⟨(1, 0), ⟨⟨1, by simp⟩, ⟨0, by simp⟩⟩, by simp [io]⟩, ⟨1, rfl⟩⟩
  refine ⟨m1, ?_, (level_inclusion ℤ ℚ (ℚ × ℚ) ℚ io e0 LinearMap.id hyp1 hyp2 A 2 hyp3).2.1 1 m1⟩
  rintro ⟨⟨x, y⟩, ⟨⟨⟨m, hm⟩, ⟨n, hn⟩⟩, ⟨⟨u, v⟩, huv⟩⟩, h1⟩
  simp only [] at hm hn
  simp [io, e0] at huv h1
  have hxy : x = y := by rw [← huv.1, ← huv.2]
  have : (2 : ℚ) * (m : ℚ) = 1 := by
    have hm' : (m : ℚ) = x := by simpa using hm
    rw [hm']; linarith
  have h2 : (2 : ℤ) * m = 1 := by exact_mod_cast this
  omega
end Formalism.BranchingDeterminantCap.VacLev
