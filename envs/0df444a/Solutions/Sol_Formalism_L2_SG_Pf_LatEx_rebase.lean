-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatEx.rebase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:27:19.936534+00:00
-- url     : https://prove2.me/submissions/fc8463cf-5126-472a-8146-f15179b506ea

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsDefs
import Definitions.Def_Lemmata_MiscLemmasD_Imports
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsSat
import Theorems.Thm_Formalism_L2_SG_Pf_LatEx_mem_lineV
import Theorems.Thm_Formalism_L2_SG_Pf_LatEx_fi_neg_mem
import Theorems.Thm_Formalism_L2_SG_Pf_LatEx_fi_mul_mem
import Theorems.Thm_Formalism_L2_SG_Pf_LatEx_coeffs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatEx
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]
local notation "𝓕" => FractionalIdeal (nonZeroDivisors (𝓞 E)) E
namespace Formalism.L2.SG.Pf.LatEx
theorem _root_.solution (c1 c2 a : 𝓕) (h1 : c1 ≠ 0) (h2 : c2 ≠ 0) (ha : a ≠ 0) (p q : V) :
    ∃ u1 u2 : V, lineV c1 p ⊔ lineV c2 q = lineV a u1 ⊔ lineV (c1 * c2 * a⁻¹) u2 := by
  obtain ⟨α, β, γ, δ, hα, hβ, hγ, hδ, hdet⟩ := coeffs c1 c2 a h1 h2 ha
  have E1 : a * (a⁻¹ * c1) = c1 := mul_inv_cancel_left₀ ha c1
  have E2 : a * (a⁻¹ * c2) = c2 := mul_inv_cancel_left₀ ha c2
  have E3 : c1 * c2 * a⁻¹ * (a * c2⁻¹) = c1 := by
    rw [show c1 * c2 * a⁻¹ * (a * c2⁻¹) = c1 * (c2 * c2⁻¹) * (a⁻¹ * a) by ac_rfl,
      mul_inv_cancel₀ h2, inv_mul_cancel₀ ha, mul_one, mul_one]
  have E4 : c1 * c2 * a⁻¹ * (a * c1⁻¹) = c2 := by
    rw [show c1 * c2 * a⁻¹ * (a * c1⁻¹) = c2 * (c1 * c1⁻¹) * (a⁻¹ * a) by ac_rfl,
      mul_inv_cancel₀ h1, inv_mul_cancel₀ ha, mul_one, mul_one]
  have E5 : c1 * (a * c1⁻¹) = a := by
    rw [show c1 * (a * c1⁻¹) = a * (c1 * c1⁻¹) by ac_rfl, mul_inv_cancel₀ h1, mul_one]
  have E6 : c1 * (a⁻¹ * c2) = c1 * c2 * a⁻¹ := by ac_rfl
  have E7 : c2 * (a * c2⁻¹) = a := by
    rw [show c2 * (a * c2⁻¹) = a * (c2 * c2⁻¹) by ac_rfl, mul_inv_cancel₀ h2, mul_one]
  have E8 : c2 * (a⁻¹ * c1) = c1 * c2 * a⁻¹ := by ac_rfl
  refine ⟨α • p + β • q, γ • p + δ • q, le_antisymm (sup_le ?_ ?_) (sup_le ?_ ?_)⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    have key : (x * (α * δ - β * γ)) • p =
        (x * δ) • (α • p + β • q) - (x * β) • (γ • p + δ • q) := by module
    rw [hdet, mul_one] at key
    rw [SetLike.mem_coe, key]
    exact sub_mem (Submodule.mem_sup_left (mem_lineV _ _ (fi_mul_mem E5 hx hδ)))
      (Submodule.mem_sup_right (mem_lineV _ _ (fi_mul_mem E6 hx hβ)))
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    have key : (x * (α * δ - β * γ)) • q =
        (-(x * γ)) • (α • p + β • q) + (x * α) • (γ • p + δ • q) := by module
    rw [hdet, mul_one] at key
    rw [SetLike.mem_coe, key]
    exact add_mem (Submodule.mem_sup_left (mem_lineV _ _ (fi_neg_mem (fi_mul_mem E7 hx hγ))))
      (Submodule.mem_sup_right (mem_lineV _ _ (fi_mul_mem E8 hx hα)))
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, smul_add, smul_smul, smul_smul]
    exact add_mem (Submodule.mem_sup_left (mem_lineV _ _ (fi_mul_mem E1 hx hα)))
      (Submodule.mem_sup_right (mem_lineV _ _ (fi_mul_mem E2 hx hβ)))
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, smul_add, smul_smul, smul_smul]
    exact add_mem (Submodule.mem_sup_left (mem_lineV _ _ (fi_mul_mem E3 hx hγ)))
      (Submodule.mem_sup_right (mem_lineV _ _ (fi_mul_mem E4 hx hδ)))
end Formalism.L2.SG.Pf.LatEx
