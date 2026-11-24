-- Prove2me | solution 1 for Formalism.L2.Ker.KS.mem_cmL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:26:05.875725+00:00
-- url     : https://prove2.me/submissions/02bb0a61-30de-450c-ab9a-a834abf1b624

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_KernelLattices_KernelLocalFactors_SelfDualLatticeNorms_HalfPeriodStandardCM

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
theorem _root_.solution (z : ℂ) : z ∈ (cmL a b d ha hd lam hlam).lattice ↔ ∃ r s : ℤ, z = pt a b d lam r s := by
  rw [PeriodPair.mem_lattice]
  have e1 : (cmL a b d ha hd lam hlam).ω₁ = lam * (a : ℂ) := rfl
  have e2 : (cmL a b d ha hd lam hlam).ω₂ = lam * Formalism.L2.Th1.F.cmTheta b d := rfl
  rw [e1, e2]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by simp only [pt]; push_cast; ring⟩
  · rintro ⟨r, s, rfl⟩
    exact ⟨r, s, by simp only [pt]; push_cast; ring⟩
end Formalism.L2.Ker.KS
