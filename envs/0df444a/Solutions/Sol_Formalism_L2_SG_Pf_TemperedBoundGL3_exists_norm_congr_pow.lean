-- Prove2me | solution 1 for Formalism.L2.SG.Pf.TemperedBoundGL3.exists_norm_congr_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:45:23.770805+00:00
-- url     : https://prove2.me/submissions/2a1f60b5-e980-4332-ad86-b0d44743af4b

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
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_one_lt_absNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_exists_of_normRepCount_ne_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_one_lt_absNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanC_one_lt_absNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_ThirdPropositionSlot_extP_split
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_ThirdPropositionSlot_map_comap_eq_of_inert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_maximal_over
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localDensity
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_extP_split
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_map_comap_eq_of_inert


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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ∉ 𝔭) {k : ℕ}
    (hk : 1 ≤ k) : ∃ α : 𝓞 K, conjO K α * α - ι c ∈ extP K 𝔭 ^ k := by
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  have hcP : ι c ∉ P := fun h => hc (Ideal.mem_comap.2 h)
  have hN := IdealNormInequalities.one_lt_absNorm hP
  obtain ⟨h1, h2⟩ := localDensity K hK P hP 1 k le_rfl hk (ι c) (idealPowerSpanBounds.conjO_map hF c) hcP
  by_cases hc' : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P
  · have h3 := h1 hc'
    have hs : 0 < Real.sqrt (Ideal.absNorm P : ℝ) := Real.sqrt_pos.2 (by linarith)
    have hpos : (0 : ℝ) < (normRepCount K (P ^ k) 1 (ι c) : ℝ) := by
      rw [h3]
      refine mul_pos (pow_pos hs _) ?_
      have : (0 : ℝ) < Real.sqrt (Ideal.absNorm P : ℝ) ^ (-((1 : ℕ) : ℤ)) := zpow_pos hs _
      linarith
    obtain ⟨α, hα⟩ := Cell.exists_of_normRepCount_ne_zero (by exact_mod_cast hpos.ne')
    refine ⟨α, ?_⟩
    rw [ThirdPropositionSlot.map_comap_eq_of_inert hK hF hP hc']
    exact hα
  · have h3 := h2 hc'
    have hpos : (0 : ℝ) < (normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ k) 1 (ι c) : ℝ) := by
      rw [h3]
      refine mul_pos (pow_pos (by linarith) _) ?_
      have : (Ideal.absNorm P : ℝ) ^ (-((1 : ℕ) : ℤ)) < 1 := by
        rw [Nat.cast_one, zpow_neg_one]
        exact inv_lt_one_of_one_lt₀ hN
      linarith
    obtain ⟨α, hα⟩ := Cell.exists_of_normRepCount_ne_zero (by exact_mod_cast hpos.ne')
    refine ⟨α, ?_⟩
    rw [ThirdPropositionSlot.extP_split hK hF hP hc']
    exact hα
end Formalism.L2.SG.Pf.TemperedBoundGL3
