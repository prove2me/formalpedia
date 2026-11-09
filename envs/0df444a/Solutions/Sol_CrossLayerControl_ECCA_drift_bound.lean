-- Prove2me | solution 1 for CrossLayerControl.ECCA.drift_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T11:32:51.397742+00:00
-- url     : https://prove2.me/submissions/b4625f3a-916b-4993-bfc7-dd77a5bd59b2

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_Downlink
import Definitions.Def_CrossLayerControl_ECCA_IsFeasiblePower
import Definitions.Def_CrossLayerControl_ECCA_RateHyp
import Definitions.Def_CrossLayerControl_ECCA_B

namespace Aux_CLC_db

theorem queue_sq (U C R : ℝ) (hU : 0 ≤ U) (hC : 0 ≤ C) (hR : 0 ≤ R) :
    (max (U - C) 0 + R) ^ 2 ≤ U ^ 2 + C ^ 2 + R ^ 2 - 2 * U * (C - R) := by
  rcases le_total (U - C) 0 with h | h
  · rw [max_eq_right h]
    nlinarith
  · rw [max_eq_left h]
    nlinarith

end Aux_CLC_db

open CrossLayerControl.ECCA in
theorem solution {L : ℕ} {𝒮 : Type*} (M : Downlink L 𝒮) (hM : RateHyp M) (V : ℝ)
    (U : Fin L → ℝ) (D : ℝ) (hU : ∀ i, 0 ≤ U i) (hD : 0 ≤ D)
    (s : 𝒮) (R P : Fin L → ℝ) (hR : ∀ i, 0 ≤ R i ∧ R i ≤ M.Rhat) (hP : IsFeasiblePower M P) :
    (∑ i, (max (U i - M.C i P s) 0 + R i) ^ 2 + (max (D - M.Pav) 0 + ∑ i, P i) ^ 2) / 2 -
        (∑ i, U i ^ 2 + D ^ 2) / 2 - V * ∑ i, R i ≤
      B M + ∑ i, (U i - V) * R i - ∑ i, (U i * M.C i P s - D * P i) - D * M.Pav := by
  have hC0 : ∀ i, 0 ≤ M.C i P s := fun i => hM.rate_nonneg P hP s i
  have hC1 : ∀ i, M.C i P s ≤ M.muMax := fun i => hM.rate_le P hP s i
  have hPsum0 : 0 ≤ ∑ i, P i := Finset.sum_nonneg (fun i _ => hP.1 i)
  have hPsum1 := hP.2
  have hPav := hM.Pav_nonneg
  -- queue terms
  have hq : ∑ i, (max (U i - M.C i P s) 0 + R i) ^ 2 ≤
      ∑ i, (U i ^ 2 + M.muMax ^ 2 + M.Rhat ^ 2 - 2 * U i * (M.C i P s - R i)) := by
    apply Finset.sum_le_sum
    intro i _
    have h1 := Aux_CLC_db.queue_sq (U i) (M.C i P s) (R i) (hU i) (hC0 i) (hR i).1
    have h2 : M.C i P s ^ 2 ≤ M.muMax ^ 2 := by nlinarith [hC0 i, hC1 i]
    have h3 : R i ^ 2 ≤ M.Rhat ^ 2 := by nlinarith [(hR i).1, (hR i).2]
    linarith
  -- energy queue
  have he : (max (D - M.Pav) 0 + ∑ i, P i) ^ 2 ≤
      D ^ 2 + M.Pav ^ 2 + M.Pmax ^ 2 - 2 * D * (M.Pav - ∑ i, P i) := by
    have h1 := Aux_CLC_db.queue_sq D M.Pav (∑ i, P i) hD hPav hPsum0
    have h3 : (∑ i, P i) ^ 2 ≤ M.Pmax ^ 2 := by nlinarith
    linarith
  have hsum : ∑ i, (U i ^ 2 + M.muMax ^ 2 + M.Rhat ^ 2 - 2 * U i * (M.C i P s - R i)) =
      ∑ i, U i ^ 2 + (L : ℝ) * (M.muMax ^ 2 + M.Rhat ^ 2) -
        2 * ∑ i, U i * M.C i P s + 2 * ∑ i, U i * R i := by
    have e : ∀ i, (U i ^ 2 + M.muMax ^ 2 + M.Rhat ^ 2 - 2 * U i * (M.C i P s - R i)) =
        U i ^ 2 + (M.muMax ^ 2 + M.Rhat ^ 2) - 2 * (U i * M.C i P s) + 2 * (U i * R i) :=
      fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 : ∑ i, (U i - V) * R i = ∑ i, U i * R i - V * ∑ i, R i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have h2 : ∑ i, (U i * M.C i P s - D * P i) = ∑ i, U i * M.C i P s - D * ∑ i, P i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [h1, h2]
  unfold B
  linarith
