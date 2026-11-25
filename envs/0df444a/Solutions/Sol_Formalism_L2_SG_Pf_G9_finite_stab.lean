-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G9.finite_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:31:13.38916+00:00
-- url     : https://prove2.me/submissions/d2bfdee6-7fd9-4e22-86f3-d50f6ad25047

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_JordanExists
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsRepsOfCover
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSmulMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InvMemLocROfUnimod
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NondegenerateOnOrthCompl

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
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {Λ : Submodule (𝓞 K) V}
    (hfin : (stabFix h U Λ).Finite) :
    ((MulAction.stabilizer (isomFix h U) Λ : Set (isomFix h U))).Finite := by
  have := hfin.to_subtype
  exact Set.finite_coe_iff.mp (Finite.of_equiv _ (stabEquiv h U Λ).symm)
end Formalism.L2.SG.Pf.G9
