-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.unif_pow_mem_pK_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:41:11.458735+00:00
-- url     : https://prove2.me/submissions/bf5a0be5-8952-4fb7-a388-fb47e83a54d1

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsEquivOfMemEndL
import Theorems.Thm_Formalism_H_dualEquiv_apply
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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} {π : 𝓞 F} (hπ : π ∈ 𝔭) (k : ℕ) :
    algebraMap F K (π : F) ^ k ∈ pK K 𝔭 0 := by
  refine ⟨1, Submonoid.one_mem _, ?_⟩
  rw [one_smul]
  refine ⟨ι (π ^ k), by simp, ?_⟩
  show algebraMap (𝓞 K) K (ι (π ^ k)) = _
  rw [map_pow, map_pow]
  rfl
end Formalism.HermitianLattices.Ext.L3.D2
