-- Prove2me | solution 1 for CrossLayerControl.ECCA.energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T06:11:52.522824+00:00
-- url     : https://prove2.me/submissions/d0f88314-2e6e-4ac4-93ac-40aec3eac2f6

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_Downlink
import Definitions.Def_CrossLayerControl_ECCA_DownlinkHyp
import Definitions.Def_CrossLayerControl_ECCA_IsECCARun
import Theorems.Thm_CrossLayerControl_ECCA_virtual_queue_bound

open Filter CrossLayerControl.ECCA

theorem solution {L : ℕ} {𝒮 : Type*} (M : Downlink L 𝒮) (hM : DownlinkHyp M)
    (V : ℝ) (hV : 0 < V) (u₀ : Fin L → ℝ) (hu₀ : ∀ i, 0 ≤ u₀ i ∧ u₀ i ≤ V + M.Rhat)
    (a : ℕ → Fin L → ℝ) (s : ℕ → 𝒮) (r p : ℕ → Fin L → ℝ)
    (ha : ∀ t i, 0 ≤ a t i ∧ a t i ≤ M.Rhat) (hrun : IsECCARun M V u₀ a s r p) :
    (∀ t₀ T : ℕ, ∑ τ ∈ Finset.Ico t₀ (t₀ + T), ∑ i, p τ i ≤
        M.Pav * T + (M.β * V + M.β * M.Rhat + M.Pmax)) ∧
    limsup (fun T : ℕ => (((T : ℝ)⁻¹ * ∑ τ ∈ Finset.range T, ∑ i, p τ i : ℝ) : EReal)) atTop ≤
      (M.Pav : EReal) := by
  set Dm := M.β * V + M.β * M.Rhat + M.Pmax with hDm
  have hDb := virtual_queue_bound M hM V hV u₀ hu₀ a s r p ha hrun
  have hstep : ∀ t, virtD M p (t + 1) = max (virtD M p t - M.Pav) 0 + ∑ i, p t i := by
    intro t; rfl
  have hpnn : ∀ t i, 0 ≤ p t i := fun t i => ((hrun t).2.2.1).1 i
  have hDnn : ∀ t, 0 ≤ virtD M p t := by
    intro t
    cases t with
    | zero => show (0:ℝ) ≤ 0; exact le_rfl
    | succ t =>
      rw [hstep]
      have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hpnn t i)
      have := le_max_right (virtD M p t - M.Pav) 0
      linarith
  have hinc : ∀ t, ∑ i, p t i ≤ virtD M p (t + 1) - virtD M p t + M.Pav := by
    intro t
    rw [hstep]
    have := le_max_left (virtD M p t - M.Pav) 0
    linarith
  have hwin : ∀ t₀ T : ℕ, ∑ τ ∈ Finset.Ico t₀ (t₀ + T), ∑ i, p τ i ≤
      virtD M p (t₀ + T) - virtD M p t₀ + M.Pav * T := by
    intro t₀ T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [← add_assoc, Finset.sum_Ico_succ_top (by omega)]
      have := hinc (t₀ + T)
      push_cast
      linarith
  have hA : ∀ t₀ T : ℕ, ∑ τ ∈ Finset.Ico t₀ (t₀ + T), ∑ i, p τ i ≤ M.Pav * T + Dm := by
    intro t₀ T
    have := hwin t₀ T
    have := hDb (t₀ + T)
    have := hDnn t₀
    linarith
  refine ⟨hA, ?_⟩
  have hlim : Tendsto (fun T : ℕ => (((M.Pav + Dm * (T : ℝ)⁻¹ : ℝ)) : EReal)) atTop
      (nhds (M.Pav : EReal)) := by
    have h1 : Tendsto (fun T : ℕ => (M.Pav + Dm * (T : ℝ)⁻¹ : ℝ)) atTop (nhds M.Pav) := by
      have := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul Dm
      simpa using this.const_add M.Pav
    exact (continuous_coe_real_ereal.tendsto _).comp h1
  rw [← hlim.limsup_eq]
  apply limsup_le_limsup _ (by isBoundedDefault) (by isBoundedDefault)
  filter_upwards [eventually_ge_atTop 1] with T hT
  apply EReal.coe_le_coe_iff.mpr
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have := hA 0 T
  simp only [zero_add, Finset.range_eq_Ico] at this ⊢
  rw [inv_mul_le_iff₀ hTpos]
  calc ∑ τ ∈ Finset.Ico 0 T, ∑ i, p τ i ≤ M.Pav * T + Dm := this
    _ = T * (M.Pav + Dm * (T : ℝ)⁻¹) := by field_simp
