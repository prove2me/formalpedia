-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.IA.locF_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:31:06.432605+00:00
-- url     : https://prove2.me/submissions/a9efdaa2-f0b1-4ea1-882c-85c5ca0b1faf

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormDiscrIdealOfLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinrankRingOfIntegers
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardEqRelIndex
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_locF_idem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_locF_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_mem_locF_iff


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb Formalism.HermitianLattices.Ext.L3.LIOrb.IA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.LIOrb.IA
theorem _root_.solution (𝔭 : Ideal (𝓞 F)) (hp : 𝔭.IsPrime) (M N : Submodule (𝓞 K) V) :
    locF 𝔭 (M ⊓ locF 𝔭 N) = locF 𝔭 M ⊓ locF 𝔭 N := by
  apply le_antisymm
  · refine le_inf (LocF.locF_mono 𝔭 inf_le_left) ?_
    calc locF 𝔭 (M ⊓ locF 𝔭 N) ≤ locF 𝔭 (locF 𝔭 N) := LocF.locF_mono 𝔭 inf_le_right
      _ = locF 𝔭 N := LocF.locF_idem 𝔭 N
  · intro x hx
    obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp M x).1 (Submodule.mem_inf.1 hx).1
    exact (LocF.mem_locF_iff hp _ x).2 ⟨t, ht, Submodule.mem_inf.2
      ⟨htx, (locF 𝔭 N).smul_mem _ (Submodule.mem_inf.1 hx).2⟩⟩
end Formalism.HermitianLattices.Ext.L3.LIOrb.IA
