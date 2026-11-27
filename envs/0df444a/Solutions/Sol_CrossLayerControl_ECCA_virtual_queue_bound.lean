-- Prove2me | solution 1 for CrossLayerControl.ECCA.virtual_queue_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T06:09:09.512254+00:00
-- url     : https://prove2.me/submissions/0180c0c8-862b-4b1a-bc76-3ebef2c9a535

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_Downlink
import Definitions.Def_CrossLayerControl_ECCA_DownlinkHyp
import Definitions.Def_CrossLayerControl_ECCA_virtD
import Definitions.Def_CrossLayerControl_ECCA_IsECCARun
import Theorems.Thm_CrossLayerControl_ECCA_queue_bound
import Theorems.Thm_CrossLayerControl_ECCA_zero_power_rule

open CrossLayerControl.ECCA

theorem solution {L : ℕ} {𝒮 : Type*} (M : Downlink L 𝒮) (hM : DownlinkHyp M)
    (V : ℝ) (hV : 0 < V) (u₀ : Fin L → ℝ) (hu₀ : ∀ i, 0 ≤ u₀ i ∧ u₀ i ≤ V + M.Rhat)
    (a : ℕ → Fin L → ℝ) (s : ℕ → 𝒮) (r p : ℕ → Fin L → ℝ)
    (ha : ∀ t i, 0 ≤ a t i ∧ a t i ≤ M.Rhat) (hrun : IsECCARun M V u₀ a s r p) :
    ∀ t, virtD M p t ≤ M.β * V + M.β * M.Rhat + M.Pmax := by
  have hβ := hM.beta_pos
  have hR := hM.Rhat_nonneg
  have hPm := hM.Pmax_nonneg
  have hPav := hM.Pav_nonneg
  have hU := queue_bound M hM.rate_nonneg V u₀ hu₀ a s r p ha hrun
  have hZ := zero_power_rule M hM V u₀ (fun i => (hu₀ i).1) a s r p hrun
  have hstep : ∀ t, virtD M p (t + 1) = max (virtD M p t - M.Pav) 0 + ∑ i, p t i := by
    intro t; rfl
  have hpnn : ∀ t i, 0 ≤ p t i := fun t i => ((hrun t).2.2.1).1 i
  have hpsum : ∀ t, ∑ i, p t i ≤ M.Pmax := fun t => ((hrun t).2.2.1).2
  have hDnn : ∀ t, 0 ≤ virtD M p t := by
    intro t
    cases t with
    | zero => show (0:ℝ) ≤ 0; exact le_rfl
    | succ t =>
      rw [hstep]
      have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hpnn t i)
      have := le_max_right (virtD M p t - M.Pav) 0
      linarith
  have hβV : 0 ≤ M.β * V := by positivity
  have hβR : 0 ≤ M.β * M.Rhat := by positivity
  intro t
  induction t with
  | zero => show (0:ℝ) ≤ _; linarith
  | succ t ih =>
    rw [hstep]
    by_cases hc : M.β * V + M.β * M.Rhat < virtD M p t
    · have hz : ∀ i, p t i = 0 := by
        intro i
        apply hZ t i
        have := (hU t i).2
        nlinarith
      have : ∑ i, p t i = 0 := Finset.sum_eq_zero (fun i _ => hz i)
      rw [this, add_zero]
      apply max_le _ (by linarith)
      linarith
    · replace hc := not_lt.mp hc
      have h1 := hpsum t
      have h2 : max (virtD M p t - M.Pav) 0 ≤ M.β * V + M.β * M.Rhat :=
        max_le (by linarith) (by linarith)
      linarith
