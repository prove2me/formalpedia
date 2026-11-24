-- Prove2me | solution 1 for Formalism.L2.Th1.F.HalfPeriodDerivative.derivWeierstrassP_not_eventually_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:35:24.054479+00:00
-- url     : https://prove2.me/submissions/a3586826-bcdb-41a1-b2d5-6ca0010449b9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassPSecondDerivative
import Theorems.Thm_Formalism_L2_Th1_F_HalfPeriodDerivative_isOpen_compl
import Theorems.Thm_Formalism_L2_Th1_F_HalfPeriodDerivative_isPreconnected_compl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.HalfPeriodDerivative
namespace Formalism.L2.Th1.F.HalfPeriodDerivative
theorem _root_.solution (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    ¬ ∀ᶠ w in 𝓝 z, L.derivWeierstrassP w = 0 := by
  intro h
  have h0 : Set.EqOn L.derivWeierstrassP 0 (L.lattice : Set ℂ)ᶜ :=
    L.analyticOnNhd_derivWeierstrassP.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (isPreconnected_compl L) hz h
  obtain ⟨c, hc⟩ : ∃ c, ∀ w ∈ (L.lattice : Set ℂ)ᶜ, L.weierstrassP w = c :=
    (isOpen_compl L).exists_is_const_of_deriv_eq_zero (isPreconnected_compl L)
      L.differentiableOn_weierstrassP (fun w hw => by rw [L.deriv_weierstrassP]; exact h0 hw)
  have h1 : L.weierstrassP =ᶠ[𝓝[≠] 0] fun _ => c := by
    have h2 : ((L.lattice : Set ℂ) \ {0})ᶜ ∈ 𝓝[≠] (0 : ℂ) :=
      mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0)
    filter_upwards [h2, self_mem_nhdsWithin] with w hw hw0
    exact hc w (fun hwL => hw ⟨hwL, hw0⟩)
  have h3 := meromorphicOrderAt_congr h1
  rw [L.order_weierstrassP 0 (zero_mem _)] at h3
  classical
  rw [meromorphicOrderAt_const] at h3
  split_ifs at h3
  · exact absurd h3 (by simp)
  · exact absurd h3 (by decide)
end Formalism.L2.Th1.F.HalfPeriodDerivative
