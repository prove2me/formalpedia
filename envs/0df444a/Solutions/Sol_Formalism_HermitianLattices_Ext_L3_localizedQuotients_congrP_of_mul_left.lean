-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.localizedQuotients.congrP_of_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:54.886156+00:00
-- url     : https://prove2.me/submissions/d42b5298-404d-4b0b-bcb9-842fc98ea41f

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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {t : 𝓞 F} (ht : t ∉ 𝔭) {a b : K}
    (h : CongrP 𝔭 k (algebraMap (𝓞 K) K (ι t) * a) (algebraMap (𝓞 K) K (ι t) * b)) :
    CongrP 𝔭 k a b := by
  obtain ⟨u, hu, z, hz, e⟩ := h
  refine ⟨u * t, fun h => (h𝔭.isPrime.mem_or_mem h).elim hu ht, z, hz, ?_⟩
  rw [e, ← mul_sub, ← mul_assoc]
  congr 1
  simp [MeanB.algebraMap_comp]
end Formalism.HermitianLattices.Ext.L3.localizedQuotients
