-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.locF_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:41:11.276802+00:00
-- url     : https://prove2.me/submissions/ef98a12c-0637-4e03-88a7-a1bb448c26b3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FormRightMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqOfCover
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmulOfMemAutSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_le_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_locF_mono


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
set_option linter.unusedVariables false
namespace Formalism.HermitianLattices.Ext.L3.LIOrb
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {A B : Submodule (𝓞 K) V}
    (hA : locF 𝔭 A = A) (hB : locF 𝔭 B = B) : locF 𝔭 (A ⊓ B) = A ⊓ B := by
  apply le_antisymm
  · refine le_inf ?_ ?_
    · exact (LocF.locF_mono 𝔭 inf_le_left).trans hA.le
    · exact (LocF.locF_mono 𝔭 inf_le_right).trans hB.le
  · exact LocF.le_locF 𝔭 _
end Formalism.HermitianLattices.Ext.L3.LIOrb
