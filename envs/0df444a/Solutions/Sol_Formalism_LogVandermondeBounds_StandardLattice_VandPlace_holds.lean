-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.VandPlace_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:59:09.846333+00:00
-- url     : https://prove2.me/submissions/e39fe04a-766b-4198-a834-58280c03b910

import Definitions.Def_Formalism_LogVandermondeBounds_VandPlace
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_VandNSuccRight
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_anti_of_step
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_gap_of_step
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_vandN_pos
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_vandN_congr
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_vandN_succ_right
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_vandN_succ_left
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
private lemma vandN_mul_prod_pow_le_vandN_rowPar (k M : ℕ) (v b : ℕ → ℝ)
    (hv : ∀ i, i < k - 1 → 0 ≤ v i) (hbpos : ∀ j, j < M → 0 < b j)
    (hgap : ∀ i j, i < j → j < M → 1 ≤ b j - b i) (hV : 0 < vandN v (k - 1)) :
    ∀ m, m ≤ M → vandN v (k - 1) * ∏ j ∈ range m, b j ^ (k - 1)
      ≤ vandN (rowPar k v b) (k - 1 + m) := by
  have hr : ∀ i, i < k - 1 → rowPar k v b i = v i := fun i hi => by simp [rowPar, hi]
  have hr2 : ∀ i, rowPar k v b (k - 1 + i) = - b i := fun i => by simp [rowPar]
  intro m
  induction m with
  | zero =>
    intro _
    simp only [range_zero, prod_empty, mul_one, add_zero]
    exact le_of_eq (vandN_congr _ _ _ (fun i hi => (hr i hi).symm))
  | succ m ih =>
    intro hm
    have ih' := ih (by omega)
    have hbm : 0 < b m := hbpos m (by omega)
    rw [show k - 1 + (m + 1) = (k - 1 + m) + 1 by omega, vandN_succ_right, prod_range_succ]
    have hA : b m ^ (k - 1) ≤ ∏ i ∈ range (k - 1), (rowPar k v b i - rowPar k v b (k - 1 + m)) := by
      calc b m ^ (k - 1) = ∏ _i ∈ range (k - 1), b m := by simp
        _ ≤ _ := by
          apply prod_le_prod (fun i _ => hbm.le)
          intro i hi
          rw [mem_range] at hi
          rw [hr i hi, hr2 m]
          linarith [hv i hi]
    have hB : (1 : ℝ) ≤ ∏ i ∈ range m, (rowPar k v b (k - 1 + i) - rowPar k v b (k - 1 + m)) := by
      calc (1 : ℝ) = ∏ _i ∈ range m, (1 : ℝ) := by simp
        _ ≤ _ := by
          apply prod_le_prod (fun i _ => zero_le_one)
          intro i hi
          rw [mem_range] at hi
          rw [hr2 i, hr2 m]
          linarith [hgap i m hi (by omega)]
    have hF : b m ^ (k - 1) ≤ ∏ i ∈ range (k - 1 + m), (rowPar k v b i - rowPar k v b (k - 1 + m)) := by
      rw [prod_range_add]
      have hA0 : 0 ≤ ∏ i ∈ range (k - 1), (rowPar k v b i - rowPar k v b (k - 1 + m)) :=
        le_trans (pow_nonneg hbm.le _) hA
      calc b m ^ (k - 1) = b m ^ (k - 1) * 1 := by ring
        _ ≤ _ := mul_le_mul hA hB zero_le_one hA0
    have hL0 : 0 ≤ vandN v (k - 1) * ∏ j ∈ range m, b j ^ (k - 1) :=
      mul_nonneg hV.le (prod_nonneg fun j hj => pow_nonneg (hbpos j (by rw [mem_range] at hj; omega)).le _)
    rw [← mul_assoc]
    exact mul_le_mul ih' hF (pow_nonneg hbm.le _) (le_trans hL0 ih')
private lemma vandN_le_pow_mul_pow_mul_vandN_of_interlace (p : ℕ) (u v : ℕ → ℝ) (D : ℝ)
    (hu : ∀ i j, i < j → j < p + 2 → u j < u i)
    (hint : ∀ i, i < p + 1 → v i < u i ∧ u (i + 1) < v i)
    (hst : ∀ i, i + 1 < p + 1 → 1 ≤ v i - v (i + 1))
    (hD : ∀ i j, i < j → j ≤ p + 1 → u i - u j ≤ D) :
    vandN u (p + 2) ≤ D ^ (p + 1) * D ^ p * vandN v (p + 1) := by
  have hvsplit : vandN v (p + 1) = (∏ i ∈ range p, ∏ j ∈ Ico (i + 1) p, (v i - v (j + 1)))
      * ∏ i ∈ range p, (v i - v (i + 1)) := by
    unfold vandN
    rw [prod_range_succ, Ico_self, prod_empty, mul_one, ← prod_mul_distrib]
    refine prod_congr rfl (fun i hi => ?_)
    rw [mem_range] at hi
    rw [prod_eq_prod_Ico_succ_bot (by omega : i + 1 < p + 1),
      ← prod_Ico_add' (fun j => v i - v j) (i + 1) p 1, mul_comm]
  have hD0 : 0 ≤ D := le_trans (by linarith [hu 0 1 (by omega) (by omega)]) (hD 0 1 (by omega) (by omega))
  rw [hvsplit, show p + 2 = (p + 1) + 1 from rfl, vandN_succ_left, vandN_succ_right]
  beta_reduce
  have hP0 : ∏ j ∈ Ico 1 (p + 1 + 1), (u 0 - u j) ≤ D ^ (p + 1) := by
    calc _ ≤ ∏ _j ∈ Ico 1 (p + 1 + 1), D := by
          apply prod_le_prod
          · intro j hj
            rw [mem_Ico] at hj
            linarith [hu 0 j (by omega) (by omega)]
          · intro j hj
            rw [mem_Ico] at hj
            exact hD 0 j (by omega) (by omega)
      _ = D ^ (p + 1) := by simp
  have hC0 : 0 ≤ ∏ i ∈ range p, (u (i + 1) - u (p + 1)) := by
    apply prod_nonneg
    intro i hi
    rw [mem_range] at hi
    linarith [hu (i + 1) (p + 1) (by omega) (by omega)]
  have hC : ∏ i ∈ range p, (u (i + 1) - u (p + 1)) ≤ D ^ p := by
    calc _ ≤ ∏ _i ∈ range p, D := by
          apply prod_le_prod
          · intro i hi
            rw [mem_range] at hi
            linarith [hu (i + 1) (p + 1) (by omega) (by omega)]
          · intro i hi
            rw [mem_range] at hi
            exact hD (i + 1) (p + 1) (by omega) (by omega)
      _ = D ^ p := by simp
  have hV0 : 0 ≤ ∏ i ∈ range p, ∏ j ∈ Ico (i + 1) p, (u (i + 1) - u (j + 1)) := by
    apply prod_nonneg
    intro i hi
    apply prod_nonneg
    intro j hj
    rw [mem_range] at hi
    rw [mem_Ico] at hj
    linarith [hu (i + 1) (j + 1) (by omega) (by omega)]
  have hW0 : 0 ≤ ∏ i ∈ range p, ∏ j ∈ Ico (i + 1) p, (v i - v (j + 1)) := by
    apply prod_nonneg
    intro i hi
    apply prod_nonneg
    intro j hj
    rw [mem_range] at hi
    rw [mem_Ico] at hj
    linarith [(hint i (by omega)).2, (hint (j + 1) (by omega)).1, hu (i + 1) (j + 1) (by omega) (by omega)]
  have hVW : ∏ i ∈ range p, ∏ j ∈ Ico (i + 1) p, (u (i + 1) - u (j + 1))
      ≤ ∏ i ∈ range p, ∏ j ∈ Ico (i + 1) p, (v i - v (j + 1)) := by
    apply prod_le_prod
    · intro i hi
      apply prod_nonneg
      intro j hj
      rw [mem_range] at hi
      rw [mem_Ico] at hj
      linarith [hu (i + 1) (j + 1) (by omega) (by omega)]
    · intro i hi
      apply prod_le_prod
      · intro j hj
        rw [mem_range] at hi
        rw [mem_Ico] at hj
        linarith [hu (i + 1) (j + 1) (by omega) (by omega)]
      · intro j hj
        rw [mem_range] at hi
        rw [mem_Ico] at hj
        linarith [(hint i (by omega)).2, (hint (j + 1) (by omega)).1]
  have hAdj : (1 : ℝ) ≤ ∏ i ∈ range p, (v i - v (i + 1)) := by
    calc (1 : ℝ) = ∏ _i ∈ range p, (1 : ℝ) := by simp
      _ ≤ _ := by
        apply prod_le_prod (fun i _ => zero_le_one)
        intro i hi
        rw [mem_range] at hi
        exact hst i (by omega)
  calc (∏ j ∈ Ico 1 (p + 1 + 1), (u 0 - u j)) *
        ((∏ i ∈ range p, ∏ j ∈ Ico (i + 1) p, (u (i + 1) - u (j + 1))) *
          ∏ i ∈ range p, (u (i + 1) - u (p + 1)))
      ≤ D ^ (p + 1) * ((∏ i ∈ range p, ∏ j ∈ Ico (i + 1) p, (v i - v (j + 1))) * D ^ p) :=
        mul_le_mul hP0 (mul_le_mul hVW hC hC0 hW0) (mul_nonneg hV0 hC0) (pow_nonneg hD0 _)
    _ = D ^ (p + 1) * D ^ p * ((∏ i ∈ range p, ∏ j ∈ Ico (i + 1) p, (v i - v (j + 1))) * 1) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAdj hW0)
        (mul_nonneg (pow_nonneg hD0 _) (pow_nonneg hD0 _))
end Formalism.LogVandermondeBounds.StandardLattice
end

set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution : VandPlace := by
  intro ε x hε hx k m Δ u v b w hk hm hΔ hP
  obtain ⟨hv, hvstep, hint, hb0u, hcase, hw, hbstep, hkb, hwB⟩ := hP
  obtain ⟨p, rfl⟩ : ∃ p, k = p + 2 := ⟨k - 2, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, m = q + 1 := ⟨m - 1, by omega⟩
  have e1 : p + 2 - 1 = p + 1 := by omega
  have e2 : p + 2 - 2 = p := by omega
  have e3 : q + 1 - 1 = q := by omega
  simp only [e1, e2, e3] at hv hvstep hint hb0u hcase hwB ⊢
  push_cast at hv hcase hkb ⊢
  have hx0 : 0 < x := by linarith
  have hB1 : 1 ≤ Real.exp (x ^ ε) := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have haB : Real.exp (x ^ ε) ≤ x * Real.exp (x ^ ε) := le_mul_of_one_le_left (by linarith) hx
  have ha1 : 1 ≤ x * Real.exp (x ^ ε) := le_trans hB1 haB
  have hbgap : ∀ i j, i < j → j < q + 1 → 1 ≤ b j - b i := gap_of_step b (q + 1) (fun i hi => (hbstep i hi).2)
  have hK0 : 0 < ((p : ℝ) + 2) * (4 * Δ) := by positivity
  have hb0 : 0 < b 0 := (div_pos_iff_of_pos_right hx0).1 (lt_of_lt_of_le hK0 hkb)
  have hbpos : ∀ j, j < q + 1 → 0 < b j := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; exact hb0
    · linarith [hbgap 0 j h hj]
  have hu : ∀ i j, i < j → j < p + 2 → u j < u i :=
    anti_of_step u (p + 2) (fun i hi => by
      have := hint i (by omega)
      linarith [this.1, this.2])
  have hvdec : ∀ i j, i < j → j < p + 1 → v j < v i :=
    anti_of_step v (p + 1) (fun i hi => by
      have := hvstep i hi
      linarith)
  have hVv : 0 < vandN v (p + 1) := vandN_pos v _ hvdec
  have hVu : 0 < vandN u (p + 2) := vandN_pos u _ hu
  have hbq : b 0 ≤ b q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h]
    · linarith [hbgap 0 q h (by omega)]
  have hD8 : u 0 - u (p + 1) ≤ 8 * (x * Real.exp (x ^ ε)) := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · linarith
    · have hwq := (hw q (by omega)).1
      have hdiv : b 0 / x ≤ b 0 := div_le_self hb0.le hx
      have hv0 := (hv 0 (by omega)).2
      have hvp := (hv p (by omega)).1
      linarith
  have hDpair : ∀ i j, i < j → j ≤ p + 1 → u i - u j ≤ 8 * (x * Real.exp (x ^ ε)) := by
    intro i j hij hj
    have h1 : u i ≤ u 0 := by
      rcases Nat.eq_zero_or_pos i with h | h
      · rw [h]
      · exact (hu 0 i h (by omega)).le
    have h2 : u (p + 1) ≤ u j := by
      rcases Nat.lt_or_ge j (p + 1) with h | h
      · exact (hu j (p + 1) h (by omega)).le
      · rw [show j = p + 1 by omega]
    linarith
  have huv := vandN_le_pow_mul_pow_mul_vandN_of_interlace p u v _ hu hint (fun i hi => by linarith [hvstep i hi]) hDpair
  have hrow := vandN_mul_prod_pow_le_vandN_rowPar (p + 2) (q + 1) v b (by simpa only [e1] using fun i hi => (hv i hi).1) hbpos hbgap
    (by simpa only [e1] using hVv) (q + 1) le_rfl
  simp only [e1] at hrow
  have hP : 0 < ∏ j ∈ range (q + 1), b j ^ (p + 1) :=
    prod_pos fun j hj => pow_pos (hbpos j (mem_range.1 hj)) _
  have hrow0 : 0 < vandN (rowPar (p + 2) v b) (p + 1 + (q + 1)) := lt_of_lt_of_le (mul_pos hVv hP) hrow
  refine ⟨hVu, hrow0, ?_⟩
  have h8 : 0 < 8 * (x * Real.exp (x ^ ε)) := by linarith
  have hlr : Real.log (vandN v (p + 1)) + (p + 1) * ∑ j ∈ range (q + 1), Real.log (b j)
      ≤ Real.log (vandN (rowPar (p + 2) v b) (p + 1 + (q + 1))) := by
    have := Real.log_le_log (mul_pos hVv hP) hrow
    rw [Real.log_mul hVv.ne' hP.ne', Real.log_prod (fun j hj => (pow_pos (hbpos j (mem_range.1 hj)) _).ne')] at this
    simp only [Real.log_pow] at this
    rw [← mul_sum] at this
    push_cast at this
    linarith
  have hlu : Real.log (vandN u (p + 2))
      ≤ (p + 1) * Real.log (8 * (x * Real.exp (x ^ ε))) + p * Real.log (8 * (x * Real.exp (x ^ ε)))
        + Real.log (vandN v (p + 1)) := by
    have := Real.log_le_log hVu huv
    rw [Real.log_mul (by positivity) hVv.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow] at this
    push_cast at this
    linarith
  have hl8 : 0 ≤ Real.log (8 * (x * Real.exp (x ^ ε))) := Real.log_nonneg (by linarith)
  have hlk : 0 ≤ Real.log ((p : ℝ) + 2) := Real.log_nonneg (by linarith [(p.cast_nonneg : (0 : ℝ) ≤ p)])
  have hpk : 0 ≤ ((p : ℝ) + 2) * (1 + Real.log ((p : ℝ) + 2)) :=
    mul_nonneg (by positivity) (by linarith)
  nlinarith [hl8, hlk, hpk, (p.cast_nonneg : (0 : ℝ) ≤ p)]
end Formalism.LogVandermondeBounds.StandardLattice
