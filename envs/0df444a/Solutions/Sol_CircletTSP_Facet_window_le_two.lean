-- Prove2me | solution 1 for CircletTSP.Facet.window_le_two
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:07:15.313891+00:00
-- url     : https://prove2.me/submissions/4d6ccefa-23b2-4c95-8b3b-1660fe9c3a59

import Mathlib
import Definitions.Def_MetricTSP_tour_vector
import Definitions.Def_CircletTSP_Facet_Setting

set_option autoImplicit false

namespace CircletTSP.Facet.WindowBoundProof

lemma rotate_twice_ne_self {n : ℕ} (hn : 2 < n) (i : Fin n) :
    finRotate n (finRotate n i) ≠ i := by
  let : NeZero n := ⟨by omega⟩
  intro h
  have hv := congrArg Fin.val h
  simp only [finRotate_apply, Fin.val_add, Fin.val_one'] at hv
  rw [Nat.mod_eq_of_lt (show 1 < n by omega)] at hv
  have hi := i.isLt
  by_cases h₁ : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt h₁] at hv
    by_cases h₂ : i.val + 1 + 1 < n
    · rw [Nat.mod_eq_of_lt h₂] at hv
      omega
    · have heq : i.val + 1 + 1 = n := by omega
      rw [heq, Nat.mod_self] at hv
      omega
  · have heq : i.val + 1 = n := by omega
    rw [heq, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (show 1 < n by omega)] at hv
    omega

lemma tourVec_zero_or_one {n : ℕ} (hn : 2 < n) (π : Equiv.Perm (Fin n))
    (u v : Fin n) : MetricTSP.tourVec π u v = 0 ∨ MetricTSP.tourVec π u v = 1 := by
  have hc : (MetricTSP.tourSteps π u v).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    simp only [MetricTSP.tourSteps, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    rcases hi with ⟨hiu, hiv⟩ | ⟨hiv, hiu⟩ <;>
      rcases hj with ⟨hju, hjv⟩ | ⟨hjv, hju⟩
    · exact π.injective (hiu.trans hju.symm)
    · have h₁ : finRotate n i = j := π.injective (hiv.trans hjv.symm)
      have h₂ : finRotate n j = i := π.injective (hju.trans hiu.symm)
      exact (rotate_twice_ne_self hn i (by rw [h₁, h₂])).elim
    · have h₁ : finRotate n i = j := π.injective (hiu.trans hju.symm)
      have h₂ : finRotate n j = i := π.injective (hjv.trans hiv.symm)
      exact (rotate_twice_ne_self hn i (by rw [h₁, h₂])).elim
    · exact π.injective (hiv.trans hjv.symm)
  have heq : (MetricTSP.tourSteps π u v).card = 0 ∨
      (MetricTSP.tourSteps π u v).card = 1 := by omega
  simpa only [MetricTSP.tourVec, Nat.cast_eq_zero, Nat.cast_eq_one] using heq

lemma tourVec_symm {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    MetricTSP.tourVec π u v = MetricTSP.tourVec π v u := by
  simp [MetricTSP.tourVec, MetricTSP.tourSteps, or_comm]

lemma shift_shift {n : ℕ} (u : Fin n) (a b : ℕ) :
    shift (shift u a) b = shift u (a + b) := by
  apply Fin.ext
  change ((u.val + a) % n + b) % n = (u.val + (a + b)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]

lemma shift_add_n {n : ℕ} (u : Fin n) (a : ℕ) : shift u (a + n) = shift u a := by
  apply Fin.ext
  simp [shift, Nat.add_mod]

lemma shift_zero {n : ℕ} (u : Fin n) : shift u 0 = u := by
  apply Fin.ext
  simpa only [shift, Nat.add_zero] using Nat.mod_eq_of_lt u.isLt

lemma window_le_two_direct (n : ℕ) (hn : 8 ≤ n) (h4 : 4 ∣ n)
    (π : Equiv.Perm (Fin n))
    (hno : ∀ u : Fin n, ¬ IsStructA π u ∧ ¬ IsStructB1 π u ∧ ¬ IsStructB2 π u) :
    ∀ u : Fin n, window π u ≤ 2 := by
  intro u
  have hn3 : 2 < n := by omega
  have hd : n / 2 + n / 2 = n := by omega
  have hs₀ : shift (shift u (n / 2)) (n / 2) = u := by
    rw [shift_shift, hd]
    simpa only [Nat.zero_add, shift_zero] using shift_add_n u 0
  have hs₁ : shift (shift u (n / 2)) 1 = shift u (n / 2 + 1) := shift_shift _ _ _
  have hs₂ : shift (shift u (n / 2)) (1 + n / 2) = shift u 1 := by
    rw [shift_shift, show n / 2 + (1 + n / 2) = 1 + n by omega, shift_add_n]
  have hA : ¬ (MetricTSP.tourVec π u (shift u 1) = 1 ∧
      MetricTSP.tourVec π u (shift u (n / 2)) = 1 ∧
      MetricTSP.tourVec π (shift u 1) (shift u (1 + n / 2)) = 1) := by
    rintro ⟨hp, hr, hs⟩
    apply (hno u).1
    exact ⟨(tourVec_symm π _ _).trans hr, hp, hs⟩
  have hB₁ : ¬ (MetricTSP.tourVec π u (shift u 1) = 1 ∧
      MetricTSP.tourVec π (shift u (n / 2)) (shift u (n / 2 + 1)) = 1 ∧
      MetricTSP.tourVec π u (shift u (n / 2)) = 1) := by
    rintro ⟨hp, hq, hr⟩
    apply (hno u).2.1
    exact ⟨(tourVec_symm π _ _).trans hp, hr, by simpa [Adj, Nat.add_comm] using hq⟩
  have hB₂ : ¬ (MetricTSP.tourVec π u (shift u 1) = 1 ∧
      MetricTSP.tourVec π (shift u (n / 2)) (shift u (n / 2 + 1)) = 1 ∧
      MetricTSP.tourVec π (shift u 1) (shift u (1 + n / 2)) = 1) := by
    rintro ⟨hp, hq, hs⟩
    apply (hno u).2.2
    exact ⟨hp, hs, by simpa [Adj, Nat.add_comm] using (tourVec_symm π _ _).trans hq⟩
  have hA' : ¬ (MetricTSP.tourVec π (shift u (n / 2)) (shift u (n / 2 + 1)) = 1 ∧
      MetricTSP.tourVec π u (shift u (n / 2)) = 1 ∧
      MetricTSP.tourVec π (shift u 1) (shift u (1 + n / 2)) = 1) := by
    rintro ⟨hq, hr, hs⟩
    apply (hno (shift u (n / 2))).1
    simp only [IsStructA, Adj, hs₀, hs₁, hs₂]
    exact ⟨hr, hq, by simpa [Nat.add_comm] using (tourVec_symm π _ _).trans hs⟩
  rcases tourVec_zero_or_one hn3 π u (shift u 1) with hp | hp <;>
    rcases tourVec_zero_or_one hn3 π (shift u (n / 2)) (shift u (n / 2 + 1)) with hq | hq <;>
    rcases tourVec_zero_or_one hn3 π u (shift u (n / 2)) with hr | hr <;>
    rcases tourVec_zero_or_one hn3 π (shift u 1) (shift u (1 + n / 2)) with hs | hs <;>
    simp_all [window] <;> norm_num

end CircletTSP.Facet.WindowBoundProof

open CircletTSP.Facet

theorem solution (n : ℕ) (hn : 8 ≤ n) (h4 : 4 ∣ n) (π : Equiv.Perm (Fin n))
    (hno : ∀ u : Fin n, ¬ IsStructA π u ∧ ¬ IsStructB1 π u ∧ ¬ IsStructB2 π u) :
    ∀ u : Fin n, window π u ≤ 2 :=
  WindowBoundProof.window_le_two_direct n hn h4 π hno
