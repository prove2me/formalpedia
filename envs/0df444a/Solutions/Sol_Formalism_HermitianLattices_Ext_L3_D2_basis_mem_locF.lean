-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.basis_mem_locF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:44:29.282293+00:00
-- url     : https://prove2.me/submissions/6ef432b9-ddbe-4360-b009-c102e76e013e

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulSpanIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_le_locF


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
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution {κ : Type} (a : Basis κ K V) (𝔭 : Ideal (𝓞 F)) (i : κ) :
    a i ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range a)) :=
  LocF.le_locF 𝔭 _ (Submodule.subset_span ⟨i, rfl⟩)
end Formalism.HermitianLattices.Ext.L3.D2
