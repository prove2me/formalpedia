-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.localizedQuotients.congrP_mul_left_of_sub_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:54.634626+00:00
-- url     : https://prove2.me/submissions/625a37cf-65a0-4ff6-acda-1fdd7a3ae558

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsBasisLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_algebraMap_comp
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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} {k : ℕ} {c : 𝓞 F} (hc : c - 1 ∈ 𝔭 ^ k) {a : K} {n : 𝓞 F}
    (h : CongrP 𝔭 k a (algebraMap F K (n : F))) :
    CongrP 𝔭 k (algebraMap (𝓞 K) K (ι c) * a) (algebraMap F K (n : F)) := by
  obtain ⟨u, hu, z, hz, e⟩ := h
  refine ⟨u, hu, ι c * z + ι (u * (c - 1) * n), ?_, ?_⟩
  · refine add_mem (Ideal.mul_mem_left _ _ hz) (ι_mem_pow ?_)
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hc)
  · rw [map_add, map_mul, e]
    simp only [MeanB.algebraMap_comp, map_mul, map_sub, map_one]
    ring
end Formalism.HermitianLattices.Ext.L3.localizedQuotients
