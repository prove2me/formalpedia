-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.localizedQuotients.nkCount_locF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:14.210666+00:00
-- url     : https://prove2.me/submissions/f68c7ce8-fdd6-41b3-9a8b-309e2f215d0d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsBasisLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_quotLocF_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_form_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_congrP_mul_left_of_sub_one_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
    (𝔭 : Ideal (𝓞 F)) (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (n : 𝓞 F) :
    nkCount h (locF 𝔭 L) 𝔭 k n = nkCount h L 𝔭 k n := by
  have := h𝔭.isPrime
  unfold nkCount
  symm
  refine Nat.card_congr ((quotLocF h𝔭 L k).toEquiv.subtypeEquiv fun x => ?_)
  constructor
  · rintro ⟨y, rfl, hy⟩
    exact ⟨⟨y, le_locF 𝔭 L y.2⟩, rfl, hy⟩
  · rintro ⟨w, hw, hc⟩
    obtain ⟨c, hc1, hcL⟩ := exists_approx h𝔭 L k w.2
    refine ⟨⟨_, hcL⟩, ?_, ?_⟩
    · apply (quotLocF h𝔭 L k).injective
      rw [quotLocF_mk h𝔭 L k _ (le_locF 𝔭 L hcL)]
      refine Eq.trans ?_ hw
      rw [Submodule.Quotient.eq, Submodule.mem_smul_top_iff]
      have : (((⟨ι c • (w : V), le_locF 𝔭 L hcL⟩ : ↥(locF 𝔭 L)) - w : ↥(locF 𝔭 L)) : V) =
          ι (c - 1) • (w : V) := by
        rw [map_sub, map_one, sub_smul, one_smul]; rfl
      rw [this]
      exact Submodule.smul_mem_smul (ι_mem_pow hc1) w.2
    · show CongrP 𝔭 k (h (ι c • (w : V)) (ι c • (w : V))) _
      rw [form_smul hF]
      refine congrP_mul_left_of_sub_one_mem ?_ hc
      have : c * c - 1 = (c - 1) * (c + 1) := by ring
      rw [this]
      exact Ideal.mul_mem_right _ _ hc1
end Formalism.HermitianLattices.Ext.L3.localizedQuotients
