-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.localizedQuotients.vd_locF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:32:59.749822+00:00
-- url     : https://prove2.me/submissions/cb1b7f8b-3693-4168-8c4e-42ef9e98c687

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsBasisLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_form_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_exists_common
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_of_mul_mem
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.localizedQuotients
open LocalSpans idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.localizedQuotients
theorem _root_.solution (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : vd h (locF 𝔭 L) 𝔭 = vd h L 𝔭 := by
  have := h𝔭.isPrime
  unfold vd
  congr 1
  ext e
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hle
    refine le_trans (Ideal.span_mono ?_) hle
    rintro z ⟨x, hx, e⟩
    exact ⟨x, fun i => le_locF 𝔭 L (hx i), e⟩
  · intro hle
    unfold discrIdeal
    rw [Ideal.span_le]
    rintro z ⟨x, hx, ez⟩
    obtain ⟨t, ht, htL⟩ := exists_common h𝔭 L x hx
    have h1 : ι ((t * t) ^ finrank K V) * z ∈ discrIdeal h L := by
      apply Ideal.subset_span
      refine ⟨fun i => ι t • x i, htL, ?_⟩
      have : (Matrix.of fun i j => h (ι t • x i) (ι t • x j)) =
          algebraMap (𝓞 K) K (ι (t * t)) • (Matrix.of fun i j => h (x i) (x j)) := by
        ext i j
        simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
        exact form_smul hF h t t _ _
      rw [this, Matrix.det_smul, Fintype.card_fin, map_mul, ez, map_pow, map_pow]
    have h2 : (t * t) ^ finrank K V ∉ 𝔭 ^ (0 + 1) := by
      rw [zero_add, pow_one]
      intro hm
      exact (h𝔭.isPrime.mem_or_mem (h𝔭.isPrime.mem_of_pow_mem _ hm)).elim ht ht
    exact mem_of_mul_mem h𝔭 h2 (by rw [zero_add]; exact hle h1)
end Formalism.HermitianLattices.Ext.L3.localizedQuotients
