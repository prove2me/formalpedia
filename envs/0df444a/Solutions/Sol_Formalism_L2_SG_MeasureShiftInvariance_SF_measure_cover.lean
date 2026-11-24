-- Prove2me | solution 1 for Formalism.L2.SG.MeasureShiftInvariance.SF_measure_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:17:50.725159+00:00
-- url     : https://prove2.me/submissions/10555ca2-b63b-49b4-9e89-82c490691a4c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_CountableConjSub
import Theorems.Thm_Formalism_L2_SG_MeasureShiftInvariance_isFD_of_SF
import Theorems.Thm_Formalism_L2_SG_MeasureShiftInvariance_fd_instances

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.MeasureShiftInvariance
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
namespace Formalism.L2.SG.MeasureShiftInvariance
theorem _root_.solution (Γ : Subgroup G) [Countable Γ] (ν : Measure G)
    (hν : ∀ s ∈ Γ, ν.map (fun x => s * x) = ν) {Ω T K : Set G} (hΩ : SF (Γ : Set G) Ω)
    (hT : ∀ x ∈ T, ∃ s ∈ Γ, s * x ∈ K) : ν (Ω ∩ T) ≤ ν K := by
  obtain ⟨i1, i2⟩ := fd_instances Γ ν hν
  have hfd := isFD_of_SF Γ hΩ ν
  calc ν (Ω ∩ T) ≤ ν (⋃ g : Γ, g⁻¹ • (K ∩ g • Ω)) := by
        refine measure_mono ?_
        rintro x ⟨hxΩ, hxT⟩
        obtain ⟨s, hs, hsx⟩ := hT x hxT
        refine Set.mem_iUnion.2 ⟨⟨s, hs⟩, ?_⟩
        rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
        exact ⟨hsx, Set.smul_mem_smul_set hxΩ⟩
    _ ≤ ∑' g : Γ, ν (g⁻¹ • (K ∩ g • Ω)) := measure_iUnion_le _
    _ = ∑' g : Γ, ν (K ∩ g • Ω) := by
        first
        | simp only [measure_smul]
        | (congr 1; funext g; exact measure_smul _ _)
    _ = ν K := (hfd.measure_eq_tsum' K).symm
end Formalism.L2.SG.MeasureShiftInvariance
