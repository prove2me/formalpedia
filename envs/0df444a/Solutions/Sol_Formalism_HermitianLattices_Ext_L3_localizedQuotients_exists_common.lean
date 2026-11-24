-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.localizedQuotients.exists_common
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:29.419014+00:00
-- url     : https://prove2.me/submissions/428be5c1-3958-4e02-890e-d11dc4ffe90b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsBasisLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalSpans_mem_locF


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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (L : Submodule (𝓞 K) V) {ι' : Type*}
    [Finite ι'] (w : ι' → V) (hw : ∀ i, w i ∈ locF 𝔭 L) : ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∀ i, ι t • w i ∈ L := by
  classical
  have := h𝔭.isPrime
  have := Fintype.ofFinite ι'
  choose t ht h using fun i => (mem_locF 𝔭 L (w i)).1 (hw i)
  refine ⟨∏ i, t i, ?_, fun i => ?_⟩
  · intro hmem
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff).1 hmem
    exact ht i hi
  · rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_comm, map_mul, mul_smul]
    exact L.smul_mem _ (h i)
end Formalism.HermitianLattices.Ext.L3.localizedQuotients
