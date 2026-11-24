-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z3.isCompl_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:54:06.746517+00:00
-- url     : https://prove2.me/submissions/66ca775d-270c-4990-b3c2-f6c0adc2352f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZZLoc
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_mem_orth
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_orth_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z3
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {P : Submodule K V} {S : Subring K} {M M₁ M₂ : AddSubgroup V}
namespace Formalism.L2.SG.Pf.LatDictZ.Z3
theorem _root_.solution (hs : h.IsSymm) (hd : ∀ x, (∀ y, h x y = 0) → x = 0)
    (hM : IsSelfDualMod S h M) (hsp : Splits h P M) : IsCompl P (orth h P) := by
  have hdec : ∀ v : V, ∃ a ∈ P, v - a ∈ orth h P := by
    intro v
    obtain ⟨t, ht0, htv⟩ := hM.span v
    obtain ⟨w₁, -, hw₁P, hw₁⟩ := hsp _ htv
    refine ⟨t⁻¹ • w₁, P.smul_mem _ hw₁P, ?_⟩
    have e : v - t⁻¹ • w₁ = t⁻¹ • (t • v - w₁) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ ht0, one_smul]
    rw [e]
    exact (orth h P).smul_mem _ hw₁
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxP hxW
    apply hd
    intro y
    obtain ⟨a, haP, ha⟩ := hdec y
    have e1 : h x a = 0 := orth_symm hs haP hxW
    have e2 : h x (y - a) = 0 := mem_orth.mp ha x hxP
    rw [map_sub, e1, sub_zero] at e2
    exact e2
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    obtain ⟨a, haP, ha⟩ := hdec v
    have e : v = a + (v - a) := by abel
    rw [e]
    exact Submodule.add_mem_sup haP ha
end Formalism.L2.SG.Pf.LatDictZ.Z3
