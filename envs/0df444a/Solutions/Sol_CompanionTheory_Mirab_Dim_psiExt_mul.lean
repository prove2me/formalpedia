-- Prove2me | solution 1 for CompanionTheory.Mirab.Dim.psiExt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:34:45.613199+00:00
-- url     : https://prove2.me/submissions/a47108ba-6d53-459e-9152-4bc97410d2da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_CompanionTheory_AutomorphicTheory_MirabolicRestriction_MirabolicInduction_IndDim
import Theorems.Thm_CompanionTheory_Mirab_Dim_psiExt_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.FiniteGL Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling
open CompanionTheory CompanionTheory.Mirab CompanionTheory.Mirab.Dim
variable {k : Type} [Field k] [Fintype k] (n : ℕ)
variable (ψ₀ : AddChar k ℂ)
namespace CompanionTheory.Mirab.Dim
theorem _root_.solution (u : uniSub k n) (y : mirabSub k n) (hy : y ∈ uniSub k n) :
    psiExt n ψ₀ ((u : mirabSub k n) * y) = genericChar n ψ₀ u * psiExt n ψ₀ y := by
  have h := psiExt_of_mem n ψ₀ (u * ⟨y, hy⟩)
  rw [map_mul, ← psiExt_of_mem n ψ₀ ⟨y, hy⟩] at h
  exact h
end CompanionTheory.Mirab.Dim
