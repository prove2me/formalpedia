-- Prove2me | solution 1 for Formalism.L2.Th1.H.isLat_inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:19.175354+00:00
-- url     : https://prove2.me/submissions/71e70261-044b-4808-85f8-ff5c069ae9e6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexEqAbsDetReal

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
open Module
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {Λ Λ₁ : AddSubgroup V}
    (hL : IsLat Λ) (hi : Λ₁.relIndex Λ ≠ 0) : IsLat (Λ ⊓ Λ₁) := by
  obtain ⟨hd, hs⟩ := hL
  refine ⟨DiscreteTopology.of_subset (s := (Λ : Set V)) hd (fun x hx => hx.1), ?_⟩
  rw [eq_top_iff, ← hs, Submodule.span_le]
  intro x hx
  have hm : (Λ₁.relIndex Λ) • x ∈ Λ ⊓ Λ₁ := by
    refine ⟨Λ.nsmul_mem hx _, ?_⟩
    have := AddSubgroup.nsmul_index_mem (Λ₁.addSubgroupOf Λ) ⟨x, hx⟩
    rw [AddSubgroup.mem_addSubgroupOf] at this
    simpa [AddSubgroup.relIndex] using this
  have hn : ((Λ₁.relIndex Λ : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hi
  have e : x = ((Λ₁.relIndex Λ : ℕ) : ℝ)⁻¹ • ((Λ₁.relIndex Λ) • x) := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hn, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm)
end Formalism.L2.Th1.H
