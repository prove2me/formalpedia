-- Prove2me | solution 1 for Formalism.L2.SG.Pf.TemperedBoundGL3.exists_norm_one_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:43:25.787046+00:00
-- url     : https://prove2.me/submissions/541cd144-c4f5-45bc-80c0-f76754ac6845

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
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_exists_norm_one_mul_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_isHermSemilocal_locRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_zero
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_zero



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
theorem _root_.solution {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {μ : K} (hμ : μ ≠ 0)
    (hN : star μ * μ ∈ WA.locRing P) (hN' : (star μ * μ)⁻¹ ∈ WA.locRing P) :
    ∃ b : K, star b * b = 1 ∧ b * μ⁻¹ ∈ WA.locRing P ∧ μ * b⁻¹ ∈ WA.locRing P := by
  have hS := WA.isHermSemilocal_locRing hK hP
  have h1 : star μ⁻¹ * μ⁻¹ ∈ WA.locRing P := by
    rw [star_inv₀, ← mul_inv]
    exact hN'
  obtain ⟨b, hb, hbm⟩ := WA.exists_norm_one_mul_mem hS h1
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hb
  have hsb : star b = b⁻¹ := eq_inv_of_mul_eq_one_left hb
  refine ⟨b, hb, by rw [mul_comm]; exact hbm, ?_⟩
  have e : μ * b⁻¹ = star (μ⁻¹ * b) * (star μ * μ) := by
    rw [star_mul', star_inv₀, hsb]
    have hsμ : star μ ≠ 0 := star_ne_zero.2 hμ
    field_simp
  rw [e]
  exact (WA.locRing P).mul_mem (hS.star_mem _ hbm) hN
end Formalism.L2.SG.Pf.TemperedBoundGL3
