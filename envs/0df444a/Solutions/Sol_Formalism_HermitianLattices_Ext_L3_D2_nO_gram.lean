-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.nO_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:46:54.726268+00:00
-- url     : https://prove2.me/submissions/292ba0e8-5e8b-41cb-bd3c-9ee23de32e34

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulMemPrimePower
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_gram_det
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_D2_c__ne_zero_3faafbcab9f8
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_nO_of_rel
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_det
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_le_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_locF_idem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_locF_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalSpans_mem_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_exists_common
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_form_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_vd_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_vd_locF
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (a : Basis (Fin (finrank K V)) K V)
    (ha : locF 𝔭 (Submodule.span (𝓞 K) (Set.range a)) = locF 𝔭 A₀) :
    (Matrix.of fun i j => h (a i) (a j)).det ∈ pK K 𝔭 0 ∧
      (Matrix.of fun i j => h (a i) (a j)).det ≠ 0 ∧
      nO 𝔭 (Matrix.of fun i j => h (a i) (a j)).det =
        Ideal.absNorm 𝔭 ^ (2 * vd h (locF 𝔭 A₀) 𝔭) := by
  classical
  have hpr := h𝔭.isPrime
  have haL : ∀ i, a i ∈ locF 𝔭 A₀ := fun i =>
    ha ▸ LocF.le_locF 𝔭 _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨t, ht, htL⟩ := localizedQuotients.exists_common h𝔭 A₀ a haL
  have ht0 : t ≠ 0 := fun h0 => ht (h0 ▸ zero_mem _)
  have hτ0 : algebraMap (𝓞 K) K (ι t) ≠ 0 := cι_ne_zero ht0
  obtain ⟨b, hbi⟩ : ∃ b : Basis (Fin (finrank K V)) K V, ∀ i, b i = ι t • a i :=
    ⟨a.isUnitSMul (w := fun _ => algebraMap (𝓞 K) K (ι t)) (fun _ => hτ0.isUnit), fun i => by
      rw [Basis.isUnitSMul_apply, algebraMap_smul]⟩
  have hbL : ∀ i, b i ∈ A₀ := fun i => by rw [hbi]; exact htL i
  have hb : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 A₀ := by
    rw [← ha]
    apply le_antisymm
    · apply LocF.locF_mono
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [hbi]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [← LocF.locF_idem 𝔭 (Submodule.span (𝓞 K) (Set.range b))]
      apply LocF.locF_mono
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (LocalSpans.mem_locF 𝔭 _ _).2 ⟨t, ht, by rw [← hbi]; exact Submodule.subset_span ⟨i, rfl⟩⟩
  obtain ⟨D, hD0, hdet, hv⟩ := exists_gram_det hF hs hd hA₀i h𝔭 b hbL hb
  have hs𝔭 : (t * t) ^ finrank K V ∉ 𝔭 := fun hm =>
    (hpr.mem_or_mem (hpr.mem_of_pow_mem _ hm)).elim ht ht
  have hrel : algebraMap (𝓞 K) K (ι D) = algebraMap (𝓞 K) K (ι ((t * t) ^ finrank K V)) *
      (Matrix.of fun i j => h (a i) (a j)).det := by
    have : (Matrix.of fun i j => h (b i) (b j)) =
        algebraMap (𝓞 K) K (ι (t * t)) • (Matrix.of fun i j => h (a i) (a j)) := by
      ext i j
      simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
      rw [hbi, hbi]
      exact localizedQuotients.form_smul hF h t t _ _
    rw [← hdet, this, Matrix.det_smul, Fintype.card_fin, map_pow, map_pow]
  rw [localizedQuotients.vd_locF hF h A₀ h𝔭, hv]
  exact nO_of_rel hK hF h𝔭 hD0 hs𝔭 hrel
end Formalism.HermitianLattices.Ext.L3.D2
