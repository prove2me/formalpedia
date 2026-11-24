-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.up_num_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:53:04.1888+00:00
-- url     : https://prove2.me/submissions/3d08f029-6db5-472b-b3f3-088ec344bddb

import Definitions.Def_Formalism_LogVandermondeBounds_UpperPlace
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_UpperPlaceHolds
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_up_sign_lo
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_up_nB_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.LogVandermondeBounds.StandardLattice
open Finset
private theorem prod_le_pow_of_card_le_of_le (s : Finset ℕ) (G : ℕ → ℝ) (Bd : ℝ) (e : ℕ) (he : s.card ≤ e)
    (hBd : 1 ≤ Bd) (h : ∀ c ∈ s, 0 ≤ G c ∧ G c ≤ Bd) : ∏ c ∈ s, G c ≤ Bd ^ e := by
  calc ∏ c ∈ s, G c ≤ ∏ _c ∈ s, Bd :=
        Finset.prod_le_prod (fun c hc => (h c hc).1) (fun c hc => (h c hc).2)
    _ = Bd ^ s.card := Finset.prod_const Bd
    _ ≤ Bd ^ e := pow_le_pow_right₀ hBd he
end Formalism.LogVandermondeBounds.StandardLattice
end

set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution (n m : ℕ) (lam v : ℕ → ℝ) (Bd : ℝ) (hBd : 1 ≤ Bd)
    (hlamv : ∀ i, i < n + 1 → lam i = v i)
    (hpos : ∀ a c, a < c → c < n + 1 + m → 0 < lam a - lam c + (nBetween (n + 2) a c : ℝ))
    (hle : ∀ a c, a < c → c < n + 1 + m → lam a - lam c + (nBetween (n + 2) a c : ℝ) ≤ Bd) :
    ∏ a ∈ range (n + 1 + m), ∏ c ∈ (Ico (a + 1) (n + 1 + m)).filter
        (fun c => plusSign (n + 2) c = plusSign (n + 2) a),
        (lam a - lam c + (nBetween (n + 2) a c : ℝ))
      ≤ vandN v (n + 1) * Bd ^ (m * (n + 1 + m)) := by
  have hBd0 : 0 ≤ Bd := by linarith
  have hvv : ∀ a c, a < c → c < n + 1 → 0 < v a - v c := by
    intro a c hac hc
    have h1 := hpos a c hac (by omega)
    have h2 : ((nBetween (n + 2) a c : ℕ) : ℝ) = 0 := by
      rw [up_nB_zero n a c hac hc]; simp
    rw [hlamv a (by omega), hlamv c hc, h2] at h1
    linarith
  have rownonneg : ∀ a, 0 ≤ ∏ c ∈ (Ico (a + 1) (n + 1 + m)).filter
      (fun c => plusSign (n + 2) c = plusSign (n + 2) a),
      (lam a - lam c + (nBetween (n + 2) a c : ℝ)) := by
    intro a
    apply Finset.prod_nonneg
    intro c hc
    rw [Finset.mem_filter, Finset.mem_Ico] at hc
    exact (hpos a c (by omega) hc.1.2).le
  have hrow1 : ∀ a, a < n + 1 →
      ∏ c ∈ (Ico (a + 1) (n + 1 + m)).filter (fun c => plusSign (n + 2) c = plusSign (n + 2) a),
        (lam a - lam c + (nBetween (n + 2) a c : ℝ))
      ≤ (∏ c ∈ Ico (a + 1) (n + 1), (v a - v c)) * Bd ^ m := by
    intro a ha
    rw [Finset.prod_filter, ← Finset.prod_Ico_consecutive _ (show a + 1 ≤ n + 1 by omega)
      (show n + 1 ≤ n + 1 + m by omega)]
    apply mul_le_mul
    · apply le_of_eq
      apply Finset.prod_congr rfl
      intro c hc
      rw [Finset.mem_Ico] at hc
      have hcond : plusSign (n + 2) c = plusSign (n + 2) a := by
        rw [up_sign_lo n c (by omega), up_sign_lo n a ha]
      have h2 : ((nBetween (n + 2) a c : ℕ) : ℝ) = 0 := by
        rw [up_nB_zero n a c (by omega) hc.2]; simp
      rw [if_pos hcond, h2, hlamv a ha, hlamv c hc.2]
      ring
    · refine prod_le_pow_of_card_le_of_le _ _ Bd m ?_ hBd ?_
      · rw [Nat.card_Ico]; omega
      · intro c hc
        rw [Finset.mem_Ico] at hc
        split_ifs
        · exact ⟨(hpos a c (by omega) hc.2).le, hle a c (by omega) hc.2⟩
        · exact ⟨zero_le_one, hBd⟩
    · apply Finset.prod_nonneg
      intro c hc
      rw [Finset.mem_Ico] at hc
      split_ifs
      · exact (hpos a c (by omega) hc.2).le
      · exact zero_le_one
    · apply Finset.prod_nonneg
      intro c hc
      rw [Finset.mem_Ico] at hc
      exact (hvv a c (by omega) hc.2).le
  have hrow2 : ∀ a, n + 1 ≤ a →
      ∏ c ∈ (Ico (a + 1) (n + 1 + m)).filter (fun c => plusSign (n + 2) c = plusSign (n + 2) a),
        (lam a - lam c + (nBetween (n + 2) a c : ℝ)) ≤ Bd ^ m := by
    intro a ha
    rw [Finset.prod_filter]
    refine prod_le_pow_of_card_le_of_le _ _ Bd m ?_ hBd ?_
    · rw [Nat.card_Ico]; omega
    · intro c hc
      rw [Finset.mem_Ico] at hc
      split_ifs
      · exact ⟨(hpos a c (by omega) hc.2).le, hle a c (by omega) hc.2⟩
      · exact ⟨zero_le_one, hBd⟩
  rw [Finset.prod_range_add]
  calc _ ≤ (∏ a ∈ range (n + 1), ((∏ c ∈ Ico (a + 1) (n + 1), (v a - v c)) * Bd ^ m)) *
          ∏ _x ∈ range m, Bd ^ m := by
        apply mul_le_mul
        · apply Finset.prod_le_prod
          · intro a _; exact rownonneg a
          · intro a ha; exact hrow1 a (Finset.mem_range.mp ha)
        · apply Finset.prod_le_prod
          · intro x _; exact rownonneg (n + 1 + x)
          · intro x _; exact hrow2 (n + 1 + x) (by omega)
        · exact Finset.prod_nonneg (fun x _ => rownonneg (n + 1 + x))
        · apply Finset.prod_nonneg
          intro a ha
          rw [Finset.mem_range] at ha
          refine mul_nonneg ?_ (pow_nonneg hBd0 m)
          apply Finset.prod_nonneg
          intro c hc
          rw [Finset.mem_Ico] at hc
          exact (hvv a c (by omega) hc.2).le
    _ = vandN v (n + 1) * Bd ^ (m * (n + 1 + m)) := by
        simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
        unfold vandN
        ring
end Formalism.LogVandermondeBounds.StandardLattice
