-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.mem_pK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:29:01.376041+00:00
-- url     : https://prove2.me/submissions/6b388130-8e02-45d6-91ba-42f0d773c6d6

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalSpans_mem_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_algebraMap_comp


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {a : K} :
    a ∈ pK K 𝔭 k ↔ ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ z ∈ extP K 𝔭 ^ k,
      algebraMap (𝓞 K) K z = algebraMap F K (t : F) * a := by
  have := h𝔭.isPrime
  unfold pK
  rw [LocalSpans.mem_locF]
  constructor
  · rintro ⟨t, ht, z, hz, e⟩
    refine ⟨t, ht, z, hz, ?_⟩
    rw [Algebra.linearMap_apply] at e
    rw [e, Algebra.smul_def, MeanB.algebraMap_comp]
  · rintro ⟨t, ht, z, hz, e⟩
    exact ⟨t, ht, z, hz, by rw [Algebra.linearMap_apply, e, Algebra.smul_def, MeanB.algebraMap_comp]⟩
end Formalism.HermitianLattices.Ext.L3.D2
