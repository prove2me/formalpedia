-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G2.exists_common
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:23:51.45774+00:00
-- url     : https://prove2.me/submissions/2c7d0dbb-31cb-44f0-bd50-c45f8d9b8285

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SameGenusFix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SpanPowMulLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsSubDivMemSP
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_mem_SP
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_mem_SP
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G2
open Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
namespace Formalism.L2.SG.Pf.G2
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {ι' : Type} (s : Finset ι') (r : ι' → K)
    (hr : haveI := h𝔭.isPrime; ∀ i ∈ s, r i ∈ HU.SP K 𝔭) :
    ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∀ i ∈ s, ∃ w : 𝓞 K, jK w = jK (ι t) * r i := by
  classical
  have := h𝔭.isPrime
  induction s using Finset.induction_on with
  | empty => exact ⟨1, fun h => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  | insert j s hj ih =>
    obtain ⟨t, ht, hts⟩ := ih (fun i hi => hr i (Finset.mem_insert_of_mem hi))
    obtain ⟨t', ht', w', hw'⟩ := HU.mem_SP.1 (hr j (Finset.mem_insert_self j s))
    refine ⟨t * t', fun hm => (h𝔭.isPrime.mem_or_mem hm).elim ht ht', fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · refine ⟨ι t * w', ?_⟩
      rw [map_mul, hw', map_mul, map_mul]
      ring
    · obtain ⟨w, hw⟩ := hts i hi
      refine ⟨ι t' * w, ?_⟩
      rw [map_mul, hw, map_mul, map_mul]
      ring
end Formalism.L2.SG.Pf.G2
