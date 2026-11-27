-- Prove2me | solution 1 for CompanionTheory.Mirab.Irr.avg_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:42:22.144976+00:00
-- url     : https://prove2.me/submissions/2614a1d9-7116-4f34-9568-ca6122f7be67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_CompanionTheory_AutomorphicTheory_MirabolicRestriction_MirabolicInduction_IndIrr
import Theorems.Thm_CompanionTheory_Mirab_Irr_char_inv_mul

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
theorem _root_.solution [Fintype (uniSub k n)] (ψ₀ : AddChar k ℂ) (f : mirabSub k n → ℂ) (x : mirabSub k n)
    (v : uniSub k n) :
    ∑ u : uniSub k n, genericChar n ψ₀ (u⁻¹) * f (x * (v : mirabSub k n) * u) =
      (∑ u : uniSub k n, genericChar n ψ₀ (u⁻¹) * f (x * u)) * genericChar n ψ₀ v := by
  rw [Finset.sum_mul]
  refine Fintype.sum_equiv (Equiv.mulLeft v) _ _ (fun u => ?_)
  have h3 := char_inv_mul n ψ₀ v
  have e : x * (v : mirabSub k n) * u = x * ((v * u : uniSub k n) : mirabSub k n) := by
    rw [Subgroup.coe_mul, mul_assoc]
  change _ = genericChar n ψ₀ ((v * u)⁻¹) * f (x * ((v * u : uniSub k n) : mirabSub k n)) * genericChar n ψ₀ v
  rw [e, mul_inv_rev, map_mul]
  linear_combination (-(genericChar n ψ₀ (u⁻¹) * f (x * ((v * u : uniSub k n) : mirabSub k n)))) * h3
end CompanionTheory.Mirab.Irr
