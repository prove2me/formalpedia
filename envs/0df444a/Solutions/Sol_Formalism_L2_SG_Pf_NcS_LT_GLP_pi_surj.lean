-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NcS.LT.GLP.pi_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:17:25.776442+00:00
-- url     : https://prove2.me/submissions/0f5ed335-142d-4e77-8098-3569fcb2d468

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NcSGLP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.SG.Pf.NcS.LT.GLP
variable {K : Type*} [Field K]
private theorem dual_apply_eq_sum_mul_single {a : ℕ} (μ : Module.Dual K (Fin a → K)) (t : Fin a → K) :
    μ t = ∑ i, t i * μ (Pi.single i 1) := by
  have ht : t = ∑ i, t i • (Pi.single i 1 : Fin a → K) := by
    ext j
    first
    | simp [Finset.sum_apply, Pi.single_apply]
    | simp [Finset.sum_apply, Pi.single_apply, eq_comm]
  calc μ t = μ (∑ i, t i • (Pi.single i 1 : Fin a → K)) := congrArg μ ht
    _ = ∑ i, t i * μ (Pi.single i 1) := by simp [map_sum, map_smul]
end Formalism.L2.SG.Pf.NcS.LT.GLP
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcS Formalism.L2.SG.Pf.NcS.LT Formalism.L2.SG.Pf.NcS.LT.GLP
variable {K : Type*} [Field K]
namespace Formalism.L2.SG.Pf.NcS.LT.GLP
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module K V] {a : ℕ} (ψ : Fin a → Module.Dual K V)
    (hψ : LinearIndependent K ψ) : Function.Surjective (LinearMap.pi ψ) := by
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨μ, hμ0, hμ⟩ : ∃ μ : Module.Dual K (Fin a → K), μ ≠ 0 ∧ ∀ v, μ (LinearMap.pi ψ v) = 0 := by
    first
    | (obtain ⟨μ, hμ0, hμ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
       exact ⟨μ, hμ0, fun v => LinearMap.mem_ker.mp (hμ (LinearMap.mem_range_self _ v))⟩)
    | (obtain ⟨μ, hμ0, hμ⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne)
       refine ⟨μ, hμ0, fun v => ?_⟩
       have hm : μ (LinearMap.pi ψ v) ∈ (LinearMap.range (LinearMap.pi ψ)).map μ :=
         Submodule.mem_map_of_mem (LinearMap.mem_range_self _ v)
       rw [hμ] at hm
       simpa using hm)
  have hsum : ∑ i, μ (Pi.single i 1) • ψ i = 0 := by
    refine LinearMap.ext fun v => ?_
    have hv := hμ v
    rw [dual_apply_eq_sum_mul_single] at hv
    simpa [LinearMap.sum_apply, mul_comm] using hv
  have hzero := Fintype.linearIndependent_iff.mp hψ _ hsum
  exact hμ0 (LinearMap.ext fun t => by rw [dual_apply_eq_sum_mul_single μ t]; simp [hzero])
end Formalism.L2.SG.Pf.NcS.LT.GLP
