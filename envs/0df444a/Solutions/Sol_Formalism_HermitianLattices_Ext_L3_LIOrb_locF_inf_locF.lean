-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.locF_inf_locF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:41:07.194087+00:00
-- url     : https://prove2.me/submissions/783dce1c-6f8a-49ca-a196-055518cb8886

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FormRightMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqOfCover
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmulOfMemAutSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_locF_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalSpans_mem_locF


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.LIOrb
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (A B : Submodule (𝓞 K) V) :
    locF 𝔭 (A ⊓ B) = locF 𝔭 A ⊓ locF 𝔭 B := by
  have := h𝔭.isPrime
  apply le_antisymm
  · exact le_inf (LocF.locF_mono 𝔭 inf_le_left) (LocF.locF_mono 𝔭 inf_le_right)
  · rintro x ⟨h1, h2⟩
    obtain ⟨s, hs, hsx⟩ := (LocalSpans.mem_locF 𝔭 A x).1 h1
    obtain ⟨t, ht, htx⟩ := (LocalSpans.mem_locF 𝔭 B x).1 h2
    refine (LocalSpans.mem_locF 𝔭 _ x).2 ⟨s * t, fun h => (h𝔭.isPrime.mem_or_mem h).elim hs ht, ?_, ?_⟩
    · rw [mul_comm, map_mul, mul_smul]
      exact A.smul_mem _ hsx
    · rw [map_mul, mul_smul]
      exact B.smul_mem _ htx
end Formalism.HermitianLattices.Ext.L3.LIOrb
