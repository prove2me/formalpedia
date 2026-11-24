-- Prove2me | solution 1 for Formalism.L2.Geo.Def.PC.lg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:14:08.752798+00:00
-- url     : https://prove2.me/submissions/8af04249-86b6-4c43-8a94-783886396fa7

import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassD
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassE
import Theorems.Thm_Formalism_L2_Geo_Def_PC_ie_lat
import Theorems.Thm_Formalism_L2_Geo_Def_PC_unit_away
import Theorems.Thm_Formalism_UG_P_adelstabL_lower
import Theorems.Thm_Formalism_UG_P_afsplit_decomp
import Theorems.Thm_Formalism_UG_P_levelafC_mem
import Theorems.Thm_Formalism_UG_P_levelafC_mul
import Theorems.Thm_Formalism_UG_P_levelaf_denom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Def Formalism.L2.Geo.Def.PC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
namespace Formalism.L2.Geo.Def.PC
theorem _root_.solution (Λ : Submodule (𝓞 E) (n → E)) (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤)
    (y : n → 𝒜) (hy : ∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E := E) v (y i)) ∈ latV v Λ) :
    y ∈ latA (F := F) Λ := by
  classical
  obtain ⟨c₁, hc₁, h₁⟩ := adelstabL_lower (F := F) Λ hspan
  choose d0 hd0 hd0m using fun i => levelaf_denom (F := F) (E := E) (y i)
  have hE : ∀ v, (fun i => afsplitEps E v * y i) ∈ latA (F := F) Λ := by
    intro v
    have := ie_lat v Λ _ (hy v)
    simpa only [afsplit_decomp] using this
  have h3 : ∀ i, levelafC E (∏ j, d0 j) * y i ∈ 𝒮 := by
    intro i
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_comm (d0 i), levelafC_mul, mul_assoc]
    exact mul_mem (levelafC_mem _) (hd0m i)
  have h4 := h₁ _ h3
  obtain ⟨T, u, hu, h1⟩ := unit_away (c₁ * ∏ j, d0 j)
    (mul_ne_zero hc₁ (Finset.prod_ne_zero_iff.2 fun j _ => hd0 j))
  have hu' : (1 : E) ⊗ₜ[F] u ∈ 𝒮 := Subring.subset_closure (Or.inr ⟨⟨u, hu⟩, rfl⟩)
  have hone : (1 : 𝒜) = ((1 : E) ⊗ₜ[F] u) * levelafC E (c₁ * ∏ j, d0 j) + ∑ v ∈ T, afsplitEps E v := by
    rw [Algebra.TensorProduct.one_def]
    conv_lhs => rw [h1]
    rw [TensorProduct.tmul_add, TensorProduct.tmul_sum]
    congr 1
    rw [levelafC, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm u]
  have hy' : y = (⟨_, hu'⟩ : 𝒮) • (fun i => levelafC E c₁ * (levelafC E (∏ j, d0 j) * y i)) +
      ∑ v ∈ T, (fun i => afsplitEps E v * y i) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, Subring.smul_def, smul_eq_mul]
    conv_lhs => rw [← one_mul (y i), hone]
    rw [levelafC_mul, add_mul, Finset.sum_mul]
    ring
  rw [hy']
  exact add_mem (Submodule.smul_mem _ _ h4) (sum_mem fun v _ => hE v)
end Formalism.L2.Geo.Def.PC
