-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G9.vJof_eq_of_jordan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:57:10.569545+00:00
-- url     : https://prove2.me/submissions/c3c1bbcd-25ed-427d-86c9-3be9a9ec8622

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_JordanExists
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsRepsOfCover
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSmulMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InvMemLocROfUnimod
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NondegenerateOnOrthCompl
import Theorems.Thm_Formalism_L2_SG_Pf_G9_sum_eq_of_min
import Theorems.Thm_Formalism_L2_SG_Pf_G9_card_ne_zero_eq

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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G9
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.L2.SG.Pf.G9
theorem _root_.solution (h2 : JordanInv) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {X X' : Submodule K V} {L L' : Submodule (𝓞 K) V}
    (hL : IsLatIn X L) (hL' : IsLatIn X' L') {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {b a b' a'}
    (hJ : IsJordanIn h X L 𝔭 b a) (hJ' : IsJordanIn h X' L' 𝔭 b' a')
    (hiso : Nonempty (DiscMod h X L 𝔭 ≃ₗ[𝓞 K] DiscMod h X' L' 𝔭)) :
    vJof 𝔭 a = vJof 𝔭 a' ∧ cJof 𝔭 a = cJof 𝔭 a' := by
  have H := h2 K F V V hK hF h h hs hs X X' L L' hL hL' 𝔭 h𝔭 b a b' a' hJ hJ' hiso
  refine ⟨sum_eq_of_min _ _ H, ?_⟩
  unfold cJof
  rw [card_ne_zero_eq (fun i => vF 𝔭 (a i)), card_ne_zero_eq (fun i => vF 𝔭 (a' i))]
  exact H 1
end Formalism.L2.SG.Pf.G9
