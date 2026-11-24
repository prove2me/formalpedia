-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z3.fix_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:43:34.402198+00:00
-- url     : https://prove2.me/submissions/9c19a15c-6098-430b-885d-3a81a4120742

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZZLoc
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_isCompl_orth
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_isSelfDualMod_res
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_res_nondeg
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_glue

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
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.L2.SG.Pf.LatDictZ.Z3
theorem _root_.solution (h1 : SemiGenusLoc) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm)
    (hd : ∀ x, (∀ y, h x y = 0) → x = 0) {p : Ideal (𝓞 K)} (hp : p.IsMaximal) (P : Submodule K V)
    {M₁ M₂ : AddSubgroup V} (hM₁ : IsSelfDualMod (locRing p) h M₁)
    (hM₂ : IsSelfDualMod (locRing p) h M₂)
    (hsp₁ : Splits h P M₁) (hsp₂ : Splits h P M₂) (hag : ∀ w ∈ P, w ∈ M₁ ↔ w ∈ M₂) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ w ∈ P, g w = w) ∧ ∀ x, x ∈ M₁ ↔ g x ∈ M₂ := by
  have hc := isCompl_orth hs hd hM₁ hsp₁
  obtain ⟨g', hg'i, hg'M⟩ := h1 K (orth h P) (h.domRestrict₁₂ (orth h P) (orth h P)) hK
    (hs.domRestrict (orth h P)) (res_nondeg hs hd hM₁ hsp₁) p hp _ _
    (isSelfDualMod_res hM₁ hsp₁) (isSelfDualMod_res hM₂ hsp₂)
  obtain ⟨g, hg, hgP, -, hgM⟩ := glue hs hc hsp₁ hsp₂ hag g' (fun x y => hg'i x y)
    (fun x => hg'M x)
  exact ⟨g, hg, hgP, hgM⟩
end Formalism.L2.SG.Pf.LatDictZ.Z3
