-- Prove2me | solution 1 for CompanionTheory.Mirab.Irr.vanish_off_uni
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:44:27.041431+00:00
-- url     : https://prove2.me/submissions/41bff589-cee9-426d-a9eb-2849a883df6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_CompanionTheory_AutomorphicTheory_MirabolicRestriction_MirabolicInduction_IndIrr
import Theorems.Thm_CompanionTheory_Mirab_Irr_mackey_gap

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
open CompanionTheory CompanionTheory.Mirab CompanionTheory.Mirab.Irr
variable {k : Type} [Field k] [Fintype k] (n : ℕ)
namespace CompanionTheory.Mirab.Irr
theorem _root_.solution (ψ₀ : AddChar k ℂ) (hψ : ψ₀ ≠ 1) (f : mirabSub k n → ℂ)
    (hl : ∀ (u : uniSub k n) (x : mirabSub k n), f ((u : mirabSub k n) * x) = genericChar n ψ₀ u * f x)
    (hr : ∀ (x : mirabSub k n) (u : uniSub k n), f (x * (u : mirabSub k n)) = f x * genericChar n ψ₀ u)
    (h : mirabSub k n) (hh : h ∉ uniSub k n) : f h = 0 := by
  obtain ⟨u, c, hcu, hne⟩ := mackey_gap n ψ₀ hψ h hh
  have h1 := hl u h
  have h2 := hr h c
  have e : h * (c : mirabSub k n) = u * h := by rw [hcu]; group
  rw [e, h1] at h2
  by_contra hf
  exact hne (mul_left_cancel₀ hf (h2.symm.trans (mul_comm _ _)))
end CompanionTheory.Mirab.Irr
