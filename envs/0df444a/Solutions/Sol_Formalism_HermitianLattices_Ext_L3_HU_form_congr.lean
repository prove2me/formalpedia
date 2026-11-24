-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.form_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:46:55.642202+00:00
-- url     : https://prove2.me/submissions/9da04e74-b243-4169-b02b-a3aaf530af4a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CoeCmbSingle
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLiftBasis
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_form_inP
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_mem_smul_zero
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


section
open NumberField Module Matrix
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
private theorem inP_add {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {k : ℕ} {a b : K} (ha : InP 𝔭 k a)
    (hb : InP 𝔭 k b) : InP 𝔭 k (a + b) := by
  obtain ⟨s, hs, y, hy, hya⟩ := ha
  obtain ⟨t, ht, z, hz, hzb⟩ := hb
  refine ⟨s * t, fun hst => (‹𝔭.IsPrime›.mem_or_mem hst).elim hs ht, ι t * y + ι s * z,
    Ideal.add_mem _ (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_left _ _ hz), ?_⟩
  simp only [map_add, map_mul]
  linear_combination (jK (ι t)) * hya + (jK (ι s)) * hzb
end Formalism.HermitianLattices.Ext.L3.HU
end
end

set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {k : ℕ} {x x₁ y y₁ : V}
    (hx₁ : x₁ ∈ locF 𝔭 (spanO b)) (hy : y ∈ locF 𝔭 (spanO b))
    (hxx : x - x₁ ∈ (extP K 𝔭 ^ k • locF 𝔭 (spanO b) : Submodule (𝓞 K) V))
    (hyy : y - y₁ ∈ (extP K 𝔭 ^ k • locF 𝔭 (spanO b) : Submodule (𝓞 K) V)) :
    InP 𝔭 k (h x y - h x₁ y₁) := by
  have e : h x y - h x₁ y₁ = h (x - x₁) y + h x₁ (y - y₁) := by
    simp only [map_sub, LinearMap.sub_apply]; ring
  rw [e]
  have h1 := form_inP hF b hH hxx (mem_smul_zero hy)
  have h2 := form_inP hF b hH (mem_smul_zero hx₁) hyy
  rw [zero_add] at h2
  exact inP_add h1 h2
end Formalism.HermitianLattices.Ext.L3.HU
