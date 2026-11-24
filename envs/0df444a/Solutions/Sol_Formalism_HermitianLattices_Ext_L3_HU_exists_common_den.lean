-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.exists_common_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:42:48.03265+00:00
-- url     : https://prove2.me/submissions/915f8546-70bb-45b0-8e31-3b2083a619a7

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeMapMk
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryReduction
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeEqOfSymm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_mem_SP
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_mem_SP


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} [hp : 𝔭.IsPrime] {α : Type*} [Fintype α] (f : α → K)
    (hf : ∀ a, f a ∈ SP K 𝔭) : ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∀ a, ∃ z : 𝓞 K, jK z = jK (ι t) * f a := by
  classical
  choose t ht z hz using fun a => mem_SP.1 (hf a)
  refine ⟨∏ a, t a, ?_, fun a => ⟨ι (∏ a' ∈ Finset.univ.erase a, t a') * z a, ?_⟩⟩
  · intro hmem
    obtain ⟨a, -, ha⟩ := (Ideal.IsPrime.prod_mem_iff).1 hmem
    exact ht a ha
  · rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), map_mul, hz, map_mul ι, map_mul jK]
    ring
end Formalism.HermitianLattices.Ext.L3.HU
