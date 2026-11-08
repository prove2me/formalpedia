-- Prove2me | solution 1 for CrossLayerControl.ECCA.queue_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:38:31.021919+00:00
-- url     : https://prove2.me/submissions/d4b63204-d832-4f6a-8cbf-4b163ffe4479

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_Downlink
import Definitions.Def_CrossLayerControl_ECCA_IsFeasiblePower
import Definitions.Def_CrossLayerControl_ECCA_queueU
import Definitions.Def_CrossLayerControl_ECCA_IsECCARun

open CrossLayerControl.ECCA in
theorem solution {L : ℕ} {𝒮 : Type*} (M : Downlink L 𝒮)
    (hC : ∀ P, IsFeasiblePower M P → ∀ s i, 0 ≤ M.C i P s)
    (V : ℝ) (u₀ : Fin L → ℝ) (hu₀ : ∀ i, 0 ≤ u₀ i ∧ u₀ i ≤ V + M.Rhat)
    (a : ℕ → Fin L → ℝ) (s : ℕ → 𝒮) (r p : ℕ → Fin L → ℝ)
    (ha : ∀ t i, 0 ≤ a t i ∧ a t i ≤ M.Rhat) (hrun : IsECCARun M V u₀ a s r p) :
    ∀ t i, 0 ≤ queueU M u₀ s r p t i ∧ queueU M u₀ s r p t i ≤ V + M.Rhat := by
  intro t
  induction t with
  | zero => intro i; exact hu₀ i
  | succ t ih =>
    intro i
    have hU : queueU M u₀ s r p (t + 1) i =
        max (queueU M u₀ s r p t i - M.C i (p t) (s t)) 0 + r t i := rfl
    obtain ⟨hr, hopt, hfeas, _⟩ := hrun t
    have hμ := hC (p t) hfeas (s t) i
    have hri := hr i
    have hai := ha t i
    have ihi := ih i
    rw [hU]
    constructor
    · have := le_max_right (queueU M u₀ s r p t i - M.C i (p t) (s t)) 0
      linarith [hri.1]
    · by_cases hV : queueU M u₀ s r p t i ≤ V
      · have : max (queueU M u₀ s r p t i - M.C i (p t) (s t)) 0 ≤ V :=
          max_le (by linarith) (by linarith [ihi.1])
        linarith [hri.2, hai.2]
      · push_neg at hV
        have hr0 : r t i = 0 := by
          have h1 := hopt (Function.update (r t) i 0) (fun j => by
            by_cases hj : j = i
            · subst hj
              simp [(ha t j).1]
            · rw [Function.update_of_ne hj]
              exact hr j)
          have hupd : ∀ j, (queueU M u₀ s r p t j - V) * Function.update (r t) i 0 j =
              (queueU M u₀ s r p t j - V) * r t j -
                (if j = i then (queueU M u₀ s r p t i - V) * r t i else 0) := by
            intro j
            by_cases hj : j = i
            · subst hj
              simp
            · rw [Function.update_of_ne hj, if_neg hj, sub_zero]
          rw [Finset.sum_congr rfl (fun j _ => hupd j), Finset.sum_sub_distrib,
            Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ i)] at h1
          by_contra hne
          have hpos : 0 < r t i := lt_of_le_of_ne hri.1 (Ne.symm hne)
          have := mul_pos (sub_pos.mpr hV) hpos
          linarith
        rw [hr0]
        have : max (queueU M u₀ s r p t i - M.C i (p t) (s t)) 0 ≤ queueU M u₀ s r p t i :=
          max_le (by linarith) ihi.1
        linarith [ihi.2]
