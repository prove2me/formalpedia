-- Prove2me | solution 1 for Formalism.L2.SG.Pf.TemperedBoundGL3.mem_locRing_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:07:47.750246+00:00
-- url     : https://prove2.me/submissions/a81f86ec-b813-4916-b749-5373e959d440

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_JordanExists
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLatticeOfFibLocNeZeroGood
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsHermSemilocalLocRing
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOfNormRepCountNeZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountExtP
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLatticeVdLeOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DivMemLocRingOfVFEq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_mem_locF_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_UnimodularLocalization_locR_eq_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_mem_locRing


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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.TemperedBoundGL3
open Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
include hK hF
namespace Formalism.L2.SG.Pf.TemperedBoundGL3
theorem _root_.solution {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (z : K) :
    z ∈ WA.locRing P ↔ ∃ t : 𝓞 F, t ∉ P.comap ι ∧ ∃ r : 𝓞 K, κ r = κ (ι t) * z := by
  have hp : (P.comap ι).IsPrime := Ideal.comap_isPrime _ _
  rw [WA.mem_locRing, UnimodularLocalization.locR_eq_locF hK hF hP, LocF.mem_locF_iff hp]
  refine exists_congr fun t => and_congr_right fun _ => ?_
  rw [Submodule.mem_one, Algebra.smul_def]
end Formalism.L2.SG.Pf.TemperedBoundGL3
