-- Prove2me | solution 1 for Formalism.L2.SG.Pf.TemperedBoundGL3.mem_locF_span_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:38:21.790477+00:00
-- url     : https://prove2.me/submissions/de562598-aade-4a40-b217-91c240981755

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
import Theorems.Thm_P2M_Formalism_L2_SG_Pf_TemperedBoundGL3____ne_zero_0231ee1bf980
import Theorems.Thm_Formalism_L2_SG_Pf_TemperedBoundGL3_mem_locRing_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_mem_locF_iff
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_WCA____ne_zero_cf941fa073ca


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
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.L2.SG.Pf.TemperedBoundGL3
theorem _root_.solution {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (x z : V) :
    z ∈ locF (P.comap ι) (Submodule.span (𝓞 K) {x}) ↔ ∃ c ∈ WA.locRing P, z = c • x := by
  have hp : (P.comap ι).IsPrime := Ideal.comap_isPrime _ _
  rw [LocF.mem_locF_iff hp]
  constructor
  · rintro ⟨t, ht, hz⟩
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hz
    have ht0 : κ (ι t) ≠ 0 := κι_ne_zero (fun h => ht (h ▸ Ideal.zero_mem _))
    refine ⟨κ r / κ (ι t), (mem_locRing_iff hK hF hP _).2 ⟨t, ht, r, by field_simp⟩, ?_⟩
    have e1 : r • x = κ r • x := (algebraMap_smul K r x).symm
    have e2 : ι t • z = κ (ι t) • z := (algebraMap_smul K (ι t) z).symm
    rw [e1, e2] at hr
    rw [div_eq_inv_mul, mul_smul, hr, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨t, ht, r, hr⟩ := (mem_locRing_iff hK hF hP c).1 hc
    refine ⟨t, ht, Submodule.mem_span_singleton.2 ⟨r, ?_⟩⟩
    rw [← algebraMap_smul K r x, ← algebraMap_smul K (ι t) (c • x), smul_smul, hr]
end Formalism.L2.SG.Pf.TemperedBoundGL3
