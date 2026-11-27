-- Prove2me | solution 1 for CompanionTheory.Mirab.Irr.mackey_gap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:35:00.735119+00:00
-- url     : https://prove2.me/submissions/3b29022f-ce8c-4be4-82fd-3ee9ec72bd71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_CompanionTheory_AutomorphicTheory_MirabolicRestriction_MirabolicInduction_IndIrr
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_mirabolicIsMackey


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
theorem _root_.solution (ψ₀ : AddChar k ℂ) (hψ : ψ₀ ≠ 1) (h : mirabSub k n) (hh : h ∉ uniSub k n) :
    ∃ u c : uniSub k n, (c : mirabSub k n) = h⁻¹ * u * h ∧ genericChar n ψ₀ c ≠ genericChar n ψ₀ u := by
  obtain ⟨u, hu, hc, hne⟩ := (mirabolicIsMackey k ℂ n ψ₀ hψ (mirabSub k n) (uniSub k n)
    (fun _ => Iff.rfl) (fun _ => Iff.rfl)).2.2 h hh
  exact ⟨⟨u, hu⟩, ⟨_, hc⟩, rfl, hne⟩
end CompanionTheory.Mirab.Irr
