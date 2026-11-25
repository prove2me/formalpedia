-- Prove2me | solution 1 for CompanionTheory.Mirab.Irr.avg_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:20:06.216473+00:00
-- url     : https://prove2.me/submissions/405e994d-a928-4160-9fb8-2bba7b1f9025

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_CompanionTheory_AutomorphicTheory_MirabolicRestriction_MirabolicInduction_IndIrr
import Theorems.Thm_GlobalTheory_FiniteGL_mirabInduced_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FiniteGL.mirabInduced_apply



set_option autoImplicit false
noncomputable section
open GlobalTheory.FiniteGL Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling
open CompanionTheory CompanionTheory.Mirab CompanionTheory.Mirab.Irr
variable {k : Type} [Field k] [Fintype k] (n : ℕ)
namespace CompanionTheory.Mirab.Irr
theorem _root_.solution [Fintype (uniSub k n)] (ψ₀ : AddChar k ℂ) (f : MirabInducedSpace n ψ₀) (x : mirabSub k n) :
    ((∑ u : uniSub k n, genericChar n ψ₀ (u⁻¹) • mirabInduced n ψ₀ (u : mirabSub k n) f :
        MirabInducedSpace n ψ₀) : mirabSub k n → ℂ) x =
      ∑ u : uniSub k n, genericChar n ψ₀ (u⁻¹) * (f : mirabSub k n → ℂ) (x * u) := by
  rw [Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Submodule.coe_smul, Pi.smul_apply, mirabInduced_apply, smul_eq_mul]
end CompanionTheory.Mirab.Irr
