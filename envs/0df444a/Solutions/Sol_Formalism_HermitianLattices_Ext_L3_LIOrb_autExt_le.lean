-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.autExt_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:22:24.320808+00:00
-- url     : https://prove2.me/submissions/e66fae03-97dc-49f3-969c-2a4de7cb83b0

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulTopIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatioHolds
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SumOrbitsEquivariant
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLatticeOfFibLocNeZeroGood
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtHomInjective
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StabilizerLattices_cut_gmap_extOf
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsASD_cut
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsLatIn_cut
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsSD_cut
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_SplitBAux_extOf___ee27e8a53762


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
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.LIOrb
theorem _root_.solution (S : VecSplit h h') (M : Submodule (𝓞 K) V) :
    autExt S M ≤ autSub h' (S.cut M) := by
  intro g' hg
  obtain ⟨h1, h2⟩ : SplitBAux.extOf S g' ∈ Formalism.HermitianLatticesTheory.isom h ∧
    Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') M = M := hg
  refine ⟨fun a b => ?_, ?_⟩
  · rw [← S.isom, ← S.isom, ← SplitBAux.extOf_ι, ← SplitBAux.extOf_ι, h1]
  · rw [← StabilizerLattices.cut_gmap_extOf, h2]
end Formalism.HermitianLattices.Ext.L3.LIOrb
