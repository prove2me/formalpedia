-- Prove2me | solution 1 for ContJRP.Align.eq_3_density
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T22:08:24.429334+00:00
-- url     : https://prove2.me/submissions/f5a96525-b8e2-488d-bfb2-3210166dba18

import Mathlib
import Definitions.Def_ContJRP_Align_Model
import Definitions.Def_ContJRP_Align_Alignment
import Definitions.Def_ContJRP_Align_Policy
import Theorems.Thm_ContJRP_Align_lemma_1_2_density
import Theorems.Thm_ContJRP_Align_observation_2_2_rep_orders
import Theorems.Thm_ContJRP_Align_lemma_3_1_joint_orders

open ContJRP.Align

theorem solution (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {n : ℕ} [NeZero n] (Tstar : Fin n → ℝ) (hTstar : ∀ i, 0 < Tstar i)
    (Tt : ℝ) (hTt1 : (1 - ε / 2) * tmin Tstar ≤ Tt) (hTt2 : Tt ≤ tmin Tstar)
    (Rstar : ℕ → ℝ) (hR : IsRepChoice ε Tt Tstar Rstar)
    (R : ℕ → ℝ) (hfeas : IsLPFeasible ε Tt Tstar Rstar R)
    (hmis : CrossMisaligned ε Tt Tstar Rstar R) :
    ∃ dR dT : ℝ,
      Filter.Tendsto (fun Δ : ℝ => (numOrders (active ε Tt Tstar) R Δ : ℝ) / Δ) Filter.atTop (nhds dR) ∧
      Filter.Tendsto (fun Δ : ℝ => (numOrders Finset.univ Tstar Δ : ℝ) / Δ) Filter.atTop
        (nhds dT) ∧
      dR ≤ (1 + 5 * ε) * dT := by
  have htmin_pos : 0 < tmin Tstar := by
    unfold tmin
    rw [Finset.lt_inf'_iff]
    intro i _; exact hTstar i
  have hTt_pos : 0 < Tt := by
    have : 0 < (1 - ε / 2) * tmin Tstar := mul_pos (by linarith) htmin_pos
    linarith
  have hRpos : ∀ ℓ ∈ active ε Tt Tstar, 0 < R ℓ := by
    intro ℓ hℓ
    have := (hfeas.1 ℓ hℓ).1
    have : 0 < (1 + ε) ^ ℓ * Tt := by
      have : 0 < 1 + ε := by linarith
      positivity
    linarith
  have hdR := lemma_1_2_density (active ε Tt Tstar) R hRpos
  have hdT := lemma_1_2_density Finset.univ Tstar (fun i _ => hTstar i)
  refine ⟨_, _, hdR, hdT, ?_⟩
  set c : ℝ := 5 * ((active ε Tt Tstar).card : ℝ) ^ 2 * 2 ^ (active ε Tt Tstar).card with hc
  have h31 := lemma_3_1_joint_orders ε hε0 hε1 Tstar hTstar Tt hTt1 hTt2 Rstar hR R hfeas hmis
  have h22 := observation_2_2_rep_orders ε hε0 hε1 Tstar hTstar Tt hTt1 hTt2 Rstar hR
  have hup : Filter.Tendsto
      (fun Δ : ℝ => (1 + 5 * ε) * ((numOrders Finset.univ Tstar Δ : ℝ) / Δ) + c / Δ)
      Filter.atTop (nhds ((1 + 5 * ε) *
        (∑ N ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun N => N.Nonempty),
          (-1 : ℝ) ^ (N.card + 1) * invLcm N Tstar))) := by
    have h1 := (tendsto_const_nhds (x := c)).div_atTop Filter.tendsto_id
    simpa using (hdT.const_mul (1 + 5 * ε)).add h1
  apply le_of_tendsto_of_tendsto hdR hup
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with Δ hΔ
  have a1 := h31 Δ hΔ.le
  have a2 : (numOrders (active ε Tt Tstar) Rstar Δ : ℝ) ≤ numOrders Finset.univ Tstar Δ := by
    exact_mod_cast h22 Δ hΔ.le
  have a3 : (numOrders (active ε Tt Tstar) R Δ : ℝ) ≤
      (1 + 5 * ε) * (numOrders Finset.univ Tstar Δ : ℝ) + c := by
    have : (1 + 5 * ε) * (numOrders (active ε Tt Tstar) Rstar Δ : ℝ) ≤
        (1 + 5 * ε) * (numOrders Finset.univ Tstar Δ : ℝ) :=
      mul_le_mul_of_nonneg_left a2 (by linarith)
    linarith
  have e : (1 + 5 * ε) * ((numOrders Finset.univ Tstar Δ : ℝ) / Δ) + c / Δ =
      ((1 + 5 * ε) * (numOrders Finset.univ Tstar Δ : ℝ) + c) / Δ := by
    field_simp
  show (numOrders (active ε Tt Tstar) R Δ : ℝ) / Δ ≤ _
  rw [e]
  exact div_le_div_of_nonneg_right a3 hΔ.le
