-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.Cell.exists_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:52:56.887859+00:00
-- url     : https://prove2.me/submissions/9e6afc9d-ba2e-46a2-aad8-b23dd277ce11

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOfNormRepCountNeZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandG
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormalise
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_symm0
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_form_smul_smul
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_exists_alpha
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_exists_scale
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_exists_scale_int
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_localizedQuotients_star___0cafaf6bb2bd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.Cell
open LocalSpans idealPowerSpanBounds localizedQuotients WCA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)}
namespace Formalism.HermitianLattices.Ext.L3.Cell
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {z e : V} {c a : 𝓞 F} (hze : h z e = 0)
    (hz : h z z = κ (ι c)) (he : h e e = κ (ι a)) (hc2 : c ∉ 𝔭 ^ 2) (ha2 : a ∉ 𝔭 ^ 2) (hcp : c ∈ 𝔭)
    (hap : a ∈ 𝔭) :
    ∃ u w : V, ∃ b₁ b₂ : 𝓞 F, h u u = κ (ι b₁) ∧ h w w = κ (ι b₂) ∧ b₁ ∉ 𝔭 ∧ b₂ ∉ 𝔭 ^ 2 ∧
      h w u = 0 ∧ ∀ v, h z v = 0 → h e v = 0 → h u v = 0 ∧ h w v = 0 := by
  have hez := symm0 hs hze
  obtain ⟨α, ν, hν, hW2, hW3⟩ := exists_alpha hK hF h𝔭 hcp hc2 hap ha2
  have hν' : star (κ α) * κ α = κ (ι ν) := by rw [← hν, map_mul]; rfl
  set W := c * ν + a with hW
  have hW0 : W ≠ 0 := fun h0 => hW3 (h0 ▸ zero_mem _)
  have hc0 : c ≠ 0 := fun h0 => hc2 (h0 ▸ zero_mem _)
  have ha0 : a ≠ 0 := fun h0 => ha2 (h0 ▸ zero_mem _)
  obtain ⟨μ₁, -, hμ₁s, b₁, hb₁, hb₁'⟩ := exists_scale (K := K) (r := 1) (k := 0) hF h𝔭
    (by simpa using hW2) (by simpa using hW3)
  obtain ⟨μ₂, -, hμ₂s, b₂, hb₂, hb₂'⟩ := exists_scale_int (K := K) hF h𝔭
    (mul_ne_zero (mul_ne_zero hc0 ha0) hW0)
  have hsι : ∀ t : 𝓞 F, star (κ (ι t)) = κ (ι t) := star_ι hF
  refine ⟨μ₁ • (κ α • z + e), μ₂ • ((-κ (ι a)) • z + (star (κ α) * κ (ι c)) • e), b₁, b₂,
    ?_, ?_, by simpa using hb₁', hb₂', ?_, fun v hzv hev => ⟨?_, ?_⟩⟩
  · rw [form_smul_smul, hμ₁s, ← hb₁]
    congr 1
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, starRingEnd_apply, hz, he, hze, hez, hW, map_mul]
    linear_combination κ (ι c) * hν'
  · rw [form_smul_smul, hμ₂s, ← hb₂]
    congr 1
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, starRingEnd_apply, hz, he, hze, hez, hW, map_mul, star_neg, star_star, hsι]
    linear_combination (κ (ι c) * κ (ι c) * κ (ι a)) * hν'
  · rw [form_smul_smul]
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, starRingEnd_apply, hz, he, hze, hez, star_neg, star_mul', star_star, hsι]
    ring
  · simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, hzv, hev, mul_zero, add_zero]
  · simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, hzv, hev, mul_zero, add_zero]
end Formalism.HermitianLattices.Ext.L3.Cell
