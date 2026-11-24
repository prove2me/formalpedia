-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.NO.zR_unif_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:11:45.892613+00:00
-- url     : https://prove2.me/submissions/1e44beab-04f2-46c9-81a5-b4d45ec1e098

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_pK_iff_unif


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
open Formalism.HermitianLattices.Ext.L3.D2.NO
namespace Formalism.HermitianLattices.Ext.L3.D2.NO
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π : 𝓞 F} (hπ : π ∈ 𝔭) (hπ' : π ∉ 𝔭 ^ 2)
    (k : ℕ) : zR 𝔭 (algebraMap F K (π : F) ^ k) = (pK K 𝔭 k).toAddSubgroup := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact (mem_pK_iff_unif h𝔭 hπ hπ').2 ⟨b, hb, rfl⟩
  · intro ha
    obtain ⟨b, hb, e⟩ := (mem_pK_iff_unif h𝔭 hπ hπ').1 ha
    exact ⟨b, hb, e.symm⟩
end Formalism.HermitianLattices.Ext.L3.D2.NO
