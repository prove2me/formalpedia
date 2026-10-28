-- Prove2me | solution 1 for CorruptRobustRL.ElimLB.noElim_regret_eq
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:20:31.364126+00:00
-- url     : https://prove2.me/submissions/a057ddb3-2eeb-4746-91d6-d6ccb60f11d5

import Mathlib
import Definitions.Def_CorruptRobustRL_ElimLB_MDP
import Definitions.Def_CorruptRobustRL_ElimLB_Setting
import Definitions.Def_CorruptRobustRL_ElimLB_ComboLock

namespace Aux_ElimLB2
open CorruptRobustRL.ElimLB

lemma pure_sum {H : ℕ} (y : Fin (H + 1)) (f : Fin (H + 1) → ℝ) :
    ∑ x, ((PMF.pure y) x).toReal * f x = f y := by
  simp only [PMF.pure_apply]
  rw [Finset.sum_eq_single y]
  · simp
  · intro b _ hb; simp [hb]
  · simp

lemma rbar_eq (H A : ℕ) [NeZero A] (s : Fin (H + 1)) (a : Fin A) :
    (comboLock H A).rbar s a = if (s : ℕ) = H ∧ a = 0 then 1 else 0 := by
  unfold Instance.rbar
  have hc : ∀ c : ℝ, (∑' r : ℝ, ((PMF.pure c) r).toReal * r) = c := by
    intro c
    have : (fun r : ℝ => ((PMF.pure c) r).toReal * r) = fun r => if r = c then c else 0 := by
      funext r
      by_cases h : r = c
      · subst h; simp [PMF.pure_apply]
      · simp [PMF.pure_apply, h]
    rw [this, tsum_ite_eq]
  have hR : (comboLock H A).R s a =
      if (s : ℕ) = H ∧ a = 0 then PMF.pure (1:ℝ) else PMF.pure 0 := rfl
  rw [hR]
  split_ifs
  · exact hc 1
  · exact hc 0

lemma trans_sum (H A : ℕ) [NeZero A] (s : Fin (H + 1)) (a : Fin A) (f : Fin (H + 1) → ℝ) :
    ∑ x, ((comboLock H A).p s a x).toReal * f x =
      if h : 1 ≤ (s : ℕ) ∧ (s : ℕ) < H ∧ a = 0 then f ⟨(s : ℕ) + 1, by omega⟩ else f 0 := by
  have hp : (comboLock H A).p s a = comboTrans H A s a := rfl
  rw [hp]
  unfold comboTrans
  split_ifs with h
  · exact pure_sum _ f
  · exact pure_sum _ f

lemma vopt_eq (H A : ℕ) [NeZero A] (hH : 1 ≤ H) (n : ℕ) (s : Fin (H + 1)) :
    Vopt (comboLock H A) n s = if 1 ≤ (s : ℕ) ∧ H + 1 ≤ (s : ℕ) + n then 1 else 0 := by
  induction n generalizing s with
  | zero =>
    simp only [Vopt]
    have := s.isLt
    rw [if_neg (by omega)]
  | succ k ih =>
    simp only [Vopt]
    simp_rw [rbar_eq, trans_sum, ih]
    have hs := s.isLt
    apply le_antisymm
    · apply Finset.sup'_le
      intro a _
      split_ifs <;> simp_all <;> omega
    · refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ (0 : Fin A)))
      split_ifs <;> simp_all <;> omega

lemma unif_val (H A : ℕ) [NeZero A] (T : Supervisor (Fin (H + 1)) (Fin A) H) (hT : NoElim T)
    (h : ℕ) (hh : h < H) (x : Fin (H + 1)) (a : Fin A) :
    (unifPlaus T h x a).toReal = (A : ℝ)⁻¹ := by
  have hmem : ∀ b, b ∈ plaus T h x := by
    intro b
    obtain ⟨hact, hq⟩ := hT h hh x
    unfold plaus
    simp only [Finset.mem_filter, hact, Finset.mem_univ, true_and]
    intro a' _
    exact le_trans (Finset.le_sup' (T.Qlow h x) (Finset.mem_univ a')) (hq b)
  have huniv : plaus T h x = Finset.univ := Finset.eq_univ_of_forall hmem
  have hne : (plaus T h x).Nonempty := ⟨a, hmem a⟩
  unfold unifPlaus
  rw [dif_pos hne, PMF.uniformOfFinset_apply_of_mem hne (hmem a), huniv, Finset.card_univ,
    Fintype.card_fin, ENNReal.toReal_inv, ENNReal.toReal_natCast]

lemma vunif_eq (H A : ℕ) [NeZero A] (hH : 1 ≤ H) (T : Supervisor (Fin (H + 1)) (Fin A) H)
    (hT : NoElim T) (n : ℕ) : ∀ (h : ℕ) (s : Fin (H + 1)), h + n ≤ H →
    Vunif (comboLock H A) T n h s =
      if 1 ≤ (s : ℕ) ∧ H + 1 ≤ (s : ℕ) + n then ((A : ℝ)⁻¹) ^ (H + 1 - (s : ℕ)) else 0 := by
  induction n with
  | zero =>
    intro h s _
    simp only [Vunif]
    have := s.isLt
    rw [if_neg (by omega)]
  | succ k ih =>
    intro h s hle
    simp only [Vunif]
    have hlt : h < H := by omega
    simp_rw [unif_val H A T hT h hlt, rbar_eq, trans_sum, ih (h + 1) _ (by omega)]
    have hs := s.isLt
    have hV0 : (if 1 ≤ ((0 : Fin (H + 1)) : ℕ) ∧ H + 1 ≤ ((0 : Fin (H + 1)) : ℕ) + k then
        ((A : ℝ)⁻¹) ^ (H + 1 - ((0 : Fin (H + 1)) : ℕ)) else 0) = 0 := if_neg (by simp)
    rw [← Finset.mul_sum, Finset.sum_eq_single (0 : Fin A)]
    · rw [hV0]
      by_cases h1 : (s : ℕ) = H
      · rw [if_pos ⟨h1, rfl⟩, dif_neg (fun hc => by have := hc.2.1; omega),
          if_pos (by omega), h1, Nat.add_sub_cancel_left, pow_one]
        ring
      · rw [if_neg (fun hc => h1 hc.1), zero_add]
        by_cases h2 : (s : ℕ) = 0
        · rw [dif_neg (fun hc => by have := hc.1; omega), if_neg (by omega), mul_zero]
        · rw [dif_pos ⟨by omega, by omega, rfl⟩]
          by_cases h3 : H + 1 ≤ (s : ℕ) + (k + 1)
          · rw [if_pos (by omega), if_pos (by omega)]
            have e : H + 1 - (s : ℕ) = (H + 1 - ((s : ℕ) + 1)) + 1 := by omega
            rw [e, pow_succ]
            ring
          · rw [if_neg (by omega), if_neg (by omega), mul_zero]
    · intro b _ hb
      rw [if_neg (fun hc => hb hc.2), dif_neg (fun hc => hb hc.2.2), hV0, add_zero]
    · intro h0; exact absurd (Finset.mem_univ _) h0

end Aux_ElimLB2

open CorruptRobustRL.ElimLB in
theorem solution (H A : ℕ) [NeZero A] (hH : 1 ≤ H) (hA : 2 ≤ A)
    (T : Supervisor (Fin (H + 1)) (Fin A) H) (hT : NoElim T) :
    Vstar (comboLock H A) H - valueUnif (comboLock H A) T = 1 - ((A : ℝ)⁻¹) ^ H := by
  have h1v : ((1 : Fin (H + 1)) : ℕ) = 1 := by
    simp [Fin.val_one', Nat.mod_eq_of_lt (show 1 < H + 1 by omega)]
  have hp0 : (comboLock H A).p0 = PMF.pure 1 := rfl
  unfold Vstar valueUnif
  rw [hp0, Aux_ElimLB2.pure_sum, Aux_ElimLB2.pure_sum, Aux_ElimLB2.vopt_eq H A hH,
    Aux_ElimLB2.vunif_eq H A hH T hT H 0 1 (by omega), h1v, if_pos (by omega),
    if_pos (by omega), Nat.add_sub_cancel]
