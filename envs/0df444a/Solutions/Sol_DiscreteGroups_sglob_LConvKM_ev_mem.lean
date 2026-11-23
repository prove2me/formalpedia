-- Prove2me | solution 1 for DiscreteGroups.sglob.LConvKM.ev_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:38.783867+00:00
-- url     : https://prove2.me/submissions/f04762d0-99b5-4813-96ea-0ff73b16875d

import Mathlib
import Definitions.Def_Development_DiscreteGroups_GlobalIrreducibility_LConvKMCore
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_ev_mem_sesq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set ComplexConjugate
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open DiscreteGroups DiscreteGroups.sglob DiscreteGroups.sglob.LConvKM
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable {G : Type*} [Group G] (ρ : Representation ℂ G M) (c : ℕ → ℝ) (xs : ℕ → M)
namespace DiscreteGroups.sglob.LConvKM
theorem _root_.solution {B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ} (hB : InvF ρ B) (hc : Cap c xs (ev B)) : ev B ∈ capSet ρ c xs :=
  ⟨⟨⟨⟨ev_mem_sesq B, hB.1⟩, hB.2.1⟩, hB.2.2⟩, hc⟩
end DiscreteGroups.sglob.LConvKM
