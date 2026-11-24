-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenyPAux.ext_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:36:47.127884+00:00
-- url     : https://prove2.me/submissions/e36ab5fb-5b0a-46b4-8142-8dde438ae582

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Elliptic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenyP
import Theorems.Thm_Formalism_L2_Th1_F_IsogenyPAux_P_local
import Theorems.Thm_Formalism_L2_Th1_F_IsogenyPAux_analyticAt_P
import Theorems.Thm_Formalism_L2_Th1_F_IsogenyPAux_analyticAt_PExcept

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.IsogenyPAux
namespace Formalism.L2.Th1.F.IsogenyPAux
theorem _root_.solution (L : PeriodPair) (α : ℂ) (T : Finset ℂ) (hα : α ≠ 0) (hst : MulStable L α)
    (h1 : ∀ P ∈ T, α * P ∈ L.lattice)
    (h2 : ∀ P ∈ T, ∀ Q ∈ T, P - Q ∈ L.lattice → P = Q)
    (z₀ P' : ℂ) (hP' : P' ∈ T) (hz : z₀ + P' ∈ L.lattice) :
    AnalyticAt ℂ (fun w => α ^ 2 * L.weierstrassPExcept 0 (α * (w - z₀))
        - L.weierstrassPExcept 0 (1 * (w - z₀)) - ∑ P ∈ T.erase P', L.weierstrassP (1 * w + P)) z₀ ∧
    (fun w => α ^ 2 * L.weierstrassP (α * w) - ∑ P ∈ T, L.weierstrassP (w + P)) =ᶠ[𝓝[≠] z₀]
      (fun w => α ^ 2 * L.weierstrassPExcept 0 (α * (w - z₀))
        - L.weierstrassPExcept 0 (1 * (w - z₀)) - ∑ P ∈ T.erase P', L.weierstrassP (1 * w + P)) := by
  constructor
  · refine ((analyticAt_const.mul (analyticAt_PExcept L α z₀)).sub (analyticAt_PExcept L 1 z₀)).sub ?_
    refine Finset.analyticAt_fun_sum _ fun P hP => analyticAt_P L 1 P z₀ ?_
    intro hmem
    rw [one_mul] at hmem
    refine (Finset.mem_erase.1 hP).1 (h2 P (Finset.mem_erase.1 hP).2 P' hP' ?_)
    have := L.lattice.sub_mem hmem hz
    simpa using this
  · have hαz : α * z₀ ∈ L.lattice := by
      have := L.lattice.sub_mem (hst _ hz) (h1 P' hP')
      have e : α * (z₀ + P') - α * P' = α * z₀ := by ring
      rwa [e] at this
    filter_upwards [self_mem_nhdsWithin] with w hne
    have hne' : w - z₀ ≠ 0 := sub_ne_zero.2 hne
    rw [← Finset.add_sum_erase T _ hP', P_local L (α * z₀) hαz (α * w),
      P_local L (z₀ + P') hz (w + P')]
    have e1 : α * w - α * z₀ = α * (w - z₀) := by ring
    have e2 : w + P' - (z₀ + P') = w - z₀ := by ring
    rw [e1, e2]
    simp only [one_mul]
    field_simp
    ring
end Formalism.L2.Th1.F.IsogenyPAux
