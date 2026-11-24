-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z3.res_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:13:58.650795+00:00
-- url     : https://prove2.me/submissions/00b5be09-f802-4d27-b6e8-716ef69b22ef

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZZLoc
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_orth_symm
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_decomp
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_isCompl_orth

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
    (hM : IsSelfDualMod S h M) (hsp : Splits h P M) :
    ∀ x : orth h P, (∀ y, h.domRestrict₁₂ (orth h P) (orth h P) x y = 0) → x = 0 := by
  intro x hx
  have hc := isCompl_orth hs hd hM hsp
  apply Subtype.ext
  rw [Submodule.coe_zero]
  apply hd
  intro y
  obtain ⟨a, haP, b, hbW, rfl⟩ := decomp hc y
  have e1 : h x a = 0 := orth_symm hs haP x.2
  have e2 := hx ⟨b, hbW⟩
  rw [LinearMap.domRestrict₁₂_apply] at e2
  rw [map_add, e1, zero_add]
  exact e2
end Formalism.L2.SG.Pf.LatDictZ.Z3
