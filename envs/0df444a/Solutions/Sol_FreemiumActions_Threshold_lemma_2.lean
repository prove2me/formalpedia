-- Prove2me | solution 1 for FreemiumActions.Threshold.lemma_2
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T10:02:17.314272+00:00
-- url     : https://prove2.me/submissions/a8827d31-74d6-4e2a-936b-7258b7054ae2

import Mathlib
import Definitions.Def_FreemiumActions_Threshold_Values
open scoped ENNReal
open FreemiumActions.Threshold

namespace S228FR

lemma sum_pa (g : PlayerAction → ℝ) :
    ∑ a, g a = g .monetize + g .incented + g .quit := by
  rw [show (Finset.univ : Finset PlayerAction) = {.monetize, .incented, .quit} from rfl]
  simp [Finset.sum_insert, add_assoc]

noncomputable def dd : Data 2 where
  pM := fun _ => 9/10
  pI := fun _ => 0
  pQ := fun _ => 1/10
  qM := fun _ => 9/10
  qQ := fun _ => 1/10
  alpha := fun _ => 0
  tauM := 1/2
  tauI := 0
  muM := 1
  muI := 0

lemma hA : Assumptions14 dd := by
  refine ⟨⟨fun e => ?_, ?_, ?_, ?_⟩, fun e => ?_, ⟨?_, ?_, ?_, ?_, fun e => ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp [dd, A4, Set.mem_Icc, monotone_const, antitone_const] <;> norm_num

lemma tr (y : Policy 2) (f : Level 2) :
    transient dd y 1 f = if f = 0 then 0 else 9/20 := by
  fin_cases f <;>
    simp [transient, toMDP, transition, sum_pa, choice, actionTransition, dd] <;>
    cases y 1 <;> norm_num

lemma rw' (y : Policy 2) (f : Level 2) : reward dd f (y f) = 9/10 := by
  simp [reward, dd]

lemma geo (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) :
    ∑' t : ℕ, (ENNReal.ofReal x) ^ t = ENNReal.ofReal (1 / (1 - x)) := by
  rw [ENNReal.tsum_geometric, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ h0,
    ← ENNReal.ofReal_inv_of_pos (by linarith), one_div]

lemma pv (y : Policy 2) : policyValue dd y 1 = ENNReal.ofReal (9/10 + 2 * (9/10 * (20/11))) := by
  have hv : ∀ f, visits dd y 1 f = ∑' t : ℕ, (ENNReal.ofReal (transient dd y 1 f)) ^ t :=
    fun _ => rfl
  unfold policyValue
  simp only [hv, tr, rw', Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp
  have e1 : (1 - ENNReal.ofReal (9 / 20))⁻¹ = ENNReal.ofReal (20/11) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num),
      ← ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  rw [e1, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

end S228FR

open S228FR in
theorem solution : ¬ (∀ {N : ℕ} (d : FreemiumActions.Threshold.Data N)
    (h : FreemiumActions.Threshold.Assumptions14 d)
    (e : FreemiumActions.Threshold.Level N) (he : 1 ≤ e.val),
    ENNReal.ofReal (d.qM e * d.muM / (1 - d.qM e)) ≤
        FreemiumActions.Threshold.constrainedValue d e false ∧
      ENNReal.ofReal ((d.pM e * d.muM + d.pI e * d.muI) /
        (1 - d.pM e - d.pI e)) ≤ FreemiumActions.Threshold.constrainedValue d e true) := by
  intro H
  have h1 := (H dd hA 1 (by decide)).1
  have h2 : FreemiumActions.Threshold.constrainedValue dd 1 false ≤
      ENNReal.ofReal (9/10 + 2 * (9/10 * (20/11))) :=
    iSup_le fun y => (pv y.val).le
  have h3 := h1.trans h2
  rw [ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h3
  simp [dd] at h3
  norm_num at h3
