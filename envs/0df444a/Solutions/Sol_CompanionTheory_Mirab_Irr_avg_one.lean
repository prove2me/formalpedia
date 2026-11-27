-- Prove2me | solution 1 for CompanionTheory.Mirab.Irr.avg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:42:19.914772+00:00
-- url     : https://prove2.me/submissions/af1bcaaa-ffd8-4c79-bfc9-cf13a96705b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_CompanionTheory_AutomorphicTheory_MirabolicRestriction_MirabolicInduction_IndIrr
import Theorems.Thm_CompanionTheory_Mirab_Irr_char_inv_mul
import Theorems.Thm_GlobalTheory_FiniteGL_mem_mirabInducedSpace


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
theorem _root_.solution [Fintype (uniSub k n)] (ψ₀ : AddChar k ℂ) (f : mirabSub k n → ℂ)
    (hf : f ∈ MirabInducedSpace n ψ₀) :
    ∑ u : uniSub k n, genericChar n ψ₀ (u⁻¹) * f (1 * u) = (Nat.card (uniSub k n) : ℂ) * f 1 := by
  rw [mem_mirabInducedSpace] at hf
  have e : ∀ u : uniSub k n, genericChar n ψ₀ (u⁻¹) * f (1 * u) = f 1 := by
    intro u
    have h2 : f (u : mirabSub k n) = genericChar n ψ₀ u * f 1 := by rw [← hf u 1, mul_one]
    rw [one_mul, h2]
    linear_combination f 1 * char_inv_mul n ψ₀ u
  rw [Finset.sum_congr rfl (fun u _ => e u), Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card,
    nsmul_eq_mul]
end CompanionTheory.Mirab.Irr
