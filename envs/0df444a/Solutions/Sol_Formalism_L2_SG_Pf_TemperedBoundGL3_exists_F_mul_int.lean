-- Prove2me | solution 1 for Formalism.L2.SG.Pf.TemperedBoundGL3.exists_F_mul_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:02:56.880001+00:00
-- url     : https://prove2.me/submissions/841c3d0d-0716-4558-8764-655915318cb6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SplitAtOf
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DivMemLocRingOfVFEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNearRepresentation
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFracOfFixed
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsNearOfSmul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_IsUnif0_ne_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_eq_iff_mem_range


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
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA Formalism.HermitianLattices.Ext.L3.WCA Formalism.HermitianLattices.Ext.L3.Cell
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
namespace Formalism.L2.SG.Pf.TemperedBoundGL3
theorem _root_.solution (hF : IsFixF K F) (z : K) :
    ∃ s : 𝓞 F, s ≠ 0 ∧ ∃ r : 𝓞 K, κ (ι s) * z = κ r := by
  obtain ⟨a, m, hm, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) z
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  have hκm : κ m ≠ 0 := fun h0 =>
    hm0 (FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero]))
  obtain ⟨s, hs⟩ := (conjO_eq_iff_mem_range hF (conjO K m * m)).1
    (by rw [map_mul, WA.conjO_conjO, mul_comm])
  refine ⟨s, ?_, conjO K m * a, ?_⟩
  · rintro rfl
    rw [map_zero] at hs
    rcases mul_eq_zero.1 hs.symm with h0 | h0
    · exact hm0 (by rw [← WA.conjO_conjO m, h0, map_zero])
    · exact hm0 h0
  · rw [hs, map_mul, map_mul]
    field_simp
end Formalism.L2.SG.Pf.TemperedBoundGL3
