-- Prove2me | solution 1 for CrossLayerControl.ECCA.zero_power_rule
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:49:12.434203+00:00
-- url     : https://prove2.me/submissions/bd667259-31bf-47bb-908f-e784f2d5a57d

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_Downlink
import Definitions.Def_CrossLayerControl_ECCA_DownlinkHyp
import Definitions.Def_CrossLayerControl_ECCA_queueU
import Definitions.Def_CrossLayerControl_ECCA_virtD
import Definitions.Def_CrossLayerControl_ECCA_IsECCARun

open CrossLayerControl.ECCA in
theorem solution {L : ℕ} {𝒮 : Type*} (M : Downlink L 𝒮) (hM : DownlinkHyp M)
    (V : ℝ) (u₀ : Fin L → ℝ) (hu₀ : ∀ i, 0 ≤ u₀ i)
    (a : ℕ → Fin L → ℝ) (s : ℕ → 𝒮) (r p : ℕ → Fin L → ℝ)
    (hrun : IsECCARun M V u₀ a s r p) :
    ∀ t i, queueU M u₀ s r p t i * M.β < virtD M p t → p t i = 0 := by
  have hU : ∀ t k, 0 ≤ queueU M u₀ s r p t k := by
    intro t k
    cases t with
    | zero => exact hu₀ k
    | succ t =>
      simp only [queueU, queueLaw]
      exact add_nonneg (le_max_right _ _) ((hrun t).1 k).1
  intro t i hlt
  obtain ⟨-, -, hfeas, hopt⟩ := hrun t
  have hP'i : zeroAt (p t) i i = 0 := Function.update_self _ _ _
  have hP'k : ∀ k, k ≠ i → zeroAt (p t) i k = p t k := fun k hk => Function.update_of_ne hk _ _
  have hle : ∀ k, zeroAt (p t) i k ≤ p t k := by
    intro k
    by_cases hk : k = i
    · rw [hk, hP'i]; exact hfeas.1 i
    · rw [hP'k k hk]
  have hfeas' : IsFeasiblePower M (zeroAt (p t) i) := by
    refine ⟨fun k => ?_, le_trans (Finset.sum_le_sum (fun k _ => hle k)) hfeas.2⟩
    by_cases hk : k = i
    · rw [hk, hP'i]
    · rw [hP'k k hk]; exact hfeas.1 k
  have h := hopt _ hfeas'
  have hterm : ∀ k,
      (queueU M u₀ s r p t k * M.C k (p t) (s t) - virtD M p t * p t k) -
        (queueU M u₀ s r p t k * M.C k (zeroAt (p t) i) (s t) - virtD M p t * zeroAt (p t) i k)
      ≤ if k = i then queueU M u₀ s r p t i * M.β * p t i - virtD M p t * p t i else 0 := by
    intro k
    by_cases hk : k = i
    · rw [if_pos hk, hk, hP'i]
      have hb := hM.beta_cond (p t) hfeas (s t) i
      have := mul_le_mul_of_nonneg_left
        (by linarith : M.C i (p t) (s t) - M.C i (zeroAt (p t) i) (s t) ≤ M.β * p t i) (hU t i)
      nlinarith
    · rw [if_neg hk, hP'k k hk]
      have hc := hM.cross_mono (p t) hfeas (s t) i k hk
      have := mul_le_mul_of_nonneg_left hc (hU t k)
      linarith
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hterm k)
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at hsum
  rw [Finset.sum_sub_distrib] at hsum
  have hp0 := hfeas.1 i
  rcases hp0.lt_or_eq with hpos | h0
  · have : (queueU M u₀ s r p t i * M.β - virtD M p t) * p t i < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hpos
    nlinarith
  · exact h0.symm
