-- Prove2me | solution 1 for Formalism.L2.Ker.KS.pt_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:40:25.075812+00:00
-- url     : https://prove2.me/submissions/e2bc3eae-606d-4577-a4dd-90de4db7a658

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_KernelLattices_KernelLocalFactors_SelfDualLatticeNorms_HalfPeriodStandardCM
import Theorems.Thm_Formalism_L2_Ker_KS_mem_cmL
import Theorems.Thm_Formalism_L2_Ker_KS_pt_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Ker Formalism.L2.Ker.KS
open Formalism.L2.Th1.H (cmL CmOK)
variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
namespace Formalism.L2.Ker.KS
theorem _root_.solution (u v : ℝ) : pt a b d lam u v ∈ (cmL a b d ha hd lam hlam).lattice ↔ (∃ r : ℤ, u = r) ∧ ∃ s : ℤ, v = s := by
  rw [mem_cmL]
  constructor
  · rintro ⟨r, s, h⟩
    obtain ⟨h1, h2⟩ := pt_inj a b d ha hd lam hlam h
    exact ⟨⟨r, h1⟩, ⟨s, h2⟩⟩
  · rintro ⟨⟨r, rfl⟩, ⟨s, rfl⟩⟩
    exact ⟨r, s, rfl⟩
end Formalism.L2.Ker.KS
