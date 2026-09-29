-- Prove2me | solution 1 for DrinfeldCurve.LocalChart.ChartPresentation.exists_swap_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/fe52bb6c-ff25-51d4-8bc1-3f878a92788b

import Mathlib.RingTheory.MvPowerSeries.Rename
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_LocalChart_ChartPresentation_exists_swap_ringEquiv

set_option autoImplicit false

open MvPowerSeries IsLocalRing DrinfeldCurve DrinfeldCurve.LocalChart

namespace S7Swap

variable {q : ℕ} {O : Type} [CommRing O]

abbrev sw : Fin 2 ≃ Fin 2 := Equiv.swap (0 : Fin 2) 1

lemma rename_X0 : rename (⇑sw) (X 0 : MvPowerSeries (Fin 2) O) = X 1 := by
  rw [rename_X]; simp [sw]

lemma rename_X1 : rename (⇑sw) (X 1 : MvPowerSeries (Fin 2) O) = X 0 := by
  rw [rename_X]; simp [sw]

variable (q) in
lemma rename_drinfeldForm :
    rename (⇑sw) (drinfeldForm q O) = -drinfeldForm q O := by
  unfold drinfeldForm
  rw [map_sub, map_mul, map_mul, map_pow, map_pow, rename_X0, rename_X1]
  ring

lemma map_span_X :
    Ideal.map (rename (R := O) (⇑sw)).toRingHom
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) O), X 1}) =
      Ideal.span {(X 0 : MvPowerSeries (Fin 2) O), X 1} := by
  rw [Ideal.map_span]
  have : (⇑(rename (R := O) (⇑sw)).toRingHom '' {(X 0 : MvPowerSeries (Fin 2) O), X 1}) =
      {(X 1 : MvPowerSeries (Fin 2) O), X 0} := by
    rw [Set.image_pair]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X0, rename_X1]
  rw [this, Set.pair_comm]

lemma rename_mem_pow {g : MvPowerSeries (Fin 2) O} {n : ℕ}
    (hg : g ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) O), X 1}) ^ n) :
    rename (⇑sw) g ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) O), X 1}) ^ n := by
  have h := Ideal.mem_map_of_mem (rename (R := O) (⇑sw)).toRingHom hg
  rw [Ideal.map_pow, map_span_X] at h
  exact h

variable {ϖ : O}

noncomputable def swapPres (pr : ChartPresentation q O ϖ) : ChartPresentation q O ϖ where
  f := -rename (⇑sw) pr.f
  u := -rename (⇑sw) pr.u
  v := rename (⇑sw) pr.v
  isUnit_u := (pr.isUnit_u.map (rename (R := O) (⇑sw))).neg
  isUnit_v := pr.isUnit_v.map (rename (R := O) (⇑sw))
  f_sub_mem := by
    have h := rename_mem_pow pr.f_sub_mem (n := q + 2)
    rw [map_sub, rename_drinfeldForm q] at h
    have : -rename (⇑sw) pr.f - drinfeldForm q O = -(rename (⇑sw) pr.f - -drinfeldForm q O) := by ring
    rw [this]
    exact neg_mem h

lemma swapPres_rel (pr : ChartPresentation q O ϖ) :
    (swapPres pr).rel = rename (⇑sw) pr.rel := by
  simp only [ChartPresentation.rel, swapPres, map_sub, map_mul, rename_C]
  ring

noncomputable def swapEquiv (pr : ChartPresentation q O ϖ) : pr.Ring ≃+* (swapPres pr).Ring :=
  Ideal.quotientEquiv (Ideal.span {pr.rel}) (Ideal.span {(swapPres pr).rel})
    (renameEquiv O sw).toRingEquiv (by
      rw [Ideal.map_span, Set.image_singleton, swapPres_rel]
      congr 2
      )

lemma swapEquiv_mk (pr : ChartPresentation q O ϖ) (g : MvPowerSeries (Fin 2) O) :
    swapEquiv pr (Ideal.Quotient.mk _ g) = Ideal.Quotient.mk _ (rename (⇑sw) g) := by
  simp [swapEquiv]

end S7Swap

open S7Swap in
theorem solution
    (q : ℕ) [Fact q.Prime] (O : Type) [CommRing O] (ϖ : O) (pr : ChartPresentation q O ϖ) :
    ∃ (pr' : ChartPresentation q O ϖ) (e : pr.Ring ≃+* pr'.Ring),
      (∀ o : O, e (Ideal.Quotient.mk _ (C o)) = Ideal.Quotient.mk _ (C o)) ∧
      e (Ideal.Quotient.mk _ (X 0)) = Ideal.Quotient.mk _ (X 1) ∧
      e (Ideal.Quotient.mk _ (X 1)) = Ideal.Quotient.mk _ (X 0) ∧
      pr'.v = MvPowerSeries.rename (Equiv.swap (0 : Fin 2) 1) pr.v ∧
      pr'.u = -MvPowerSeries.rename (Equiv.swap (0 : Fin 2) 1) pr.u ∧
      pr'.f = -MvPowerSeries.rename (Equiv.swap (0 : Fin 2) 1) pr.f := by
  refine ⟨swapPres pr, swapEquiv pr, fun o => ?_, ?_, ?_, rfl, rfl, rfl⟩
  · rw [swapEquiv_mk, rename_C]
  · rw [swapEquiv_mk, rename_X0]
  · rw [swapEquiv_mk, rename_X1]

end S_DrinfeldCurve_LocalChart_ChartPresentation_exists_swap_ringEquiv
end P2MW
export P2MW.S_DrinfeldCurve_LocalChart_ChartPresentation_exists_swap_ringEquiv (solution)
