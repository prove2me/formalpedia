-- Prove2me | solution 1 for Formalism.L2.Th1.H.Inv.sum_reps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:44.363715+00:00
-- url     : https://prove2.me/submissions/04d232da-85a4-4004-9b01-13ca01ad9f4b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LogarithmEquivalence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open Formalism.L2.Th1.H.Inv
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.L2.Th1.H.Inv
theorem _root_.solution {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} (hS : IsReps Λ₁ Λ₂ S) (g : V → ℂ)
    (hg : ∀ y ∈ S, y ∉ Λ₁ → g y = 0) : ∃ y₀ ∈ S, y₀ ∈ Λ₁ ∧ ∑ y ∈ S, g y = g y₀ := by
  obtain ⟨_, hdist, hcov⟩ := hS
  obtain ⟨y₀, hy₀S, hy₀⟩ := hcov 0 (zero_mem _)
  have hy₀' : y₀ ∈ Λ₁ := by simpa using Λ₁.neg_mem hy₀
  refine ⟨y₀, hy₀S, hy₀', ?_⟩
  exact Finset.sum_eq_single y₀
    (fun y hyS hne => hg y hyS (fun hy => hne (hdist y hyS y₀ hy₀S (Λ₁.sub_mem hy hy₀'))))
    (fun h => absurd hy₀S h)
end Formalism.L2.Th1.H.Inv
