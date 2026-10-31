-- Prove2me | solution 1 for FairRentFPTAS.Approx.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T12:17:48.563676+00:00
-- url     : https://prove2.me/submissions/9352e3da-3d6b-4c5e-854a-961cce1e02a8

import Mathlib
import Definitions.Def_FairRentFPTAS_Approx_Model
import Theorems.Thm_FairRentFPTAS_Approx_theorem_1
import Theorems.Thm_FairRentFPTAS_Approx_lemma_9

open FairRentFPTAS.Approx

namespace FRFThm2Aux

lemma refineAux_length (h : ℝ) (l : List (ℝ × ℝ)) :
    (refineAux h l).length ≤ 2 * l.length := by
  induction l generalizing h with
  | nil => simp [refineAux]
  | cons e t ih =>
    cases t with
    | nil =>
      simp only [refineAux]
      split_ifs <;> simp
    | cons e' rest =>
      simp only [refineAux]
      have := ih (h - e.2 * (e'.1 - e.1))
      split_ifs <;> simp at this ⊢ <;> omega

lemma roundAux_length (ε : ℝ) (l : List (ℝ × ℝ)) :
    (roundAux ε l).length ≤ 2 * l.length := by
  induction l with
  | nil => simp [roundAux]
  | cons e t ih =>
    cases t with
    | nil => simp [roundAux]
    | cons e' rest =>
      simp only [roundAux]
      split_ifs <;> simp at ih ⊢ <;> omega

lemma refineAux_mem (h : ℝ) (l : List (ℝ × ℝ)) :
    ∀ x ∈ refineAux h l, ∃ e ∈ l, x.2 = e.2 := by
  induction l generalizing h with
  | nil => simp [refineAux]
  | cons e t ih =>
    cases t with
    | nil =>
      simp only [refineAux]
      split_ifs
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with hx | hx
        · exact ⟨e, by simp, by rw [hx]⟩
        · exact ⟨e, by simp, by rw [hx]⟩
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        exact ⟨e, by simp, by rw [hx]⟩
    | cons e' rest =>
      simp only [refineAux]
      have ih' := ih (h - e.2 * (e'.1 - e.1))
      split_ifs
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with hx | hx | hx
        · exact ⟨e, by simp, by rw [hx]⟩
        · exact ⟨e, by simp, by rw [hx]⟩
        · obtain ⟨y, hy, hy2⟩ := ih' x hx
          exact ⟨y, List.mem_cons_of_mem _ hy, hy2⟩
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with hx | hx
        · exact ⟨e, by simp, by rw [hx]⟩
        · obtain ⟨y, hy, hy2⟩ := ih' x hx
          exact ⟨y, List.mem_cons_of_mem _ hy, hy2⟩

lemma roundAux_mem (ε : ℝ) (l : List (ℝ × ℝ)) :
    ∀ x ∈ roundAux ε l, ∃ e ∈ l, x.2 = roundUp ε e.2 ∨ x.2 = roundUp ε e.2 / (1 + ε) := by
  induction l with
  | nil => simp [roundAux]
  | cons e t ih =>
    cases t with
    | nil =>
      intro x hx
      simp [roundAux] at hx
      exact ⟨e, by simp, Or.inr (by rw [hx])⟩
    | cons e' rest =>
      simp only [roundAux]
      intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · split_ifs at hx
        · simp at hx; exact ⟨e, by simp, Or.inl (by rw [hx])⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with hx | hx
          · exact ⟨e, by simp, Or.inr (by rw [hx])⟩
          · exact ⟨e, by simp, Or.inl (by rw [hx])⟩
      · obtain ⟨y, hy, hy2⟩ := ih x hx
        exact ⟨y, List.mem_cons_of_mem _ hy, hy2⟩

lemma log_roundUp (ε l : ℝ) (hε : 0 < ε) (hl : 0 < l) :
    Real.log l ≤ Real.log (roundUp ε l) ∧
      Real.log (roundUp ε l) ≤ Real.log l + Real.log (1 + ε) := by
  have h1 : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
  unfold roundUp
  rw [Real.log_zpow]
  set y := Real.logb (1 + ε) l with hy
  have hyl : y * Real.log (1 + ε) = Real.log l := by
    rw [hy, Real.logb, div_mul_cancel₀ _ (ne_of_gt h1)]
  have c1 := Int.le_ceil y
  have c2 := Int.ceil_lt_add_one y
  constructor
  · rw [← hyl]; exact mul_le_mul_of_nonneg_right c1 h1.le
  · rw [← hyl]
    have : ((⌈y⌉ : ℤ) : ℝ) * Real.log (1 + ε) ≤ (y + 1) * Real.log (1 + ε) :=
      mul_le_mul_of_nonneg_right c2.le h1.le
    linarith

lemma slope_bound (ε β l : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hl : 0 < l) (hβ : |Real.log l| ≤ β) :
    |Real.log (roundUp ε l)| ≤ β + 1 ∧ |Real.log (roundUp ε l / (1 + ε))| ≤ β + 1 := by
  obtain ⟨h1, h2⟩ := log_roundUp ε l hε hl
  have hlog : Real.log (1 + ε) ≤ ε := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + ε by linarith); linarith
  have hlog0 : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
  have hR : 0 < roundUp ε l := by unfold roundUp; positivity
  have hab := abs_le.mp hβ
  obtain ⟨hab1, hab2⟩ := hab
  constructor
  · rw [abs_le]; constructor <;> nlinarith
  · rw [Real.log_div (ne_of_gt hR) (by linarith), abs_le]
    constructor <;> nlinarith

end FRFThm2Aux

open FRFThm2Aux in
theorem solution : ∃ c : ℕ, ∀ (n : ℕ) (I : Instance n) (ε β M : ℝ),
    1 ≤ n → Standing I → 0 < ε → ε < 1 →
    (∀ a r, ∀ e ∈ (I.v a r).pieces, |Real.log e.2| ≤ β) →
    IsThreshold (roundInst ε I) M →
    (∃ (T : ℕ) (π : ℕ → Equiv.Perm (Fin n)) (p : ℕ → Fin n → ℝ),
        IsRun (roundInst ε I) M T π p ∧ Halted p T) ∧
    (∀ (T : ℕ) (π : ℕ → Equiv.Perm (Fin n)) (p : ℕ → Fin n → ℝ), IsRun (roundInst ε I) M T π p →
        (T : ℝ) ≤ c * ((n : ℝ) + totalPieces I + β + 1 / ε + 1) ^ c) ∧
    (∀ (T : ℕ) (π : ℕ → Equiv.Perm (Fin n)) (p : ℕ → Fin n → ℝ), IsRun (roundInst ε I) M T π p →
        Halted p T → (∀ r, 0 ≤ p T r) ∧ IsEpsEF I ε (π T) (p T)) := by
  obtain ⟨c1, hc1⟩ := FairRentFPTAS.Approx.theorem_1
  refine ⟨c1 * 4 ^ c1 + c1, ?_⟩
  intro n I ε β M hn hI hε hε1 hβ hM
  obtain ⟨hJ, hpow, h9⟩ := FairRentFPTAS.Approx.lemma_9 I ε hI hε hε1
  -- slope bound for the rounded instance
  have hβ' : ∀ a r, ∀ e ∈ ((roundInst ε I).v a r).pieces, |Real.log e.2| ≤ β + 1 := by
    intro a r e he
    obtain ⟨e1, he1, he1'⟩ := roundAux_mem ε _ e he
    obtain ⟨e2, he2, he2'⟩ := refineAux_mem _ _ e1 he1
    have hpos : 0 < e2.2 := (hI a r).2.2.2 e2 he2
    obtain ⟨b1, b2⟩ := slope_bound ε β e2.2 hε hε1 hpos (hβ a r e2 he2)
    rcases he1' with h | h <;> rw [h, he2'] <;> assumption
  -- β ≥ 0
  have hβ0 : 0 ≤ β := by
    have a0 : Fin n := ⟨0, by omega⟩
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ (hI a0 a0).1
    exact le_trans (abs_nonneg _) (hβ a0 a0 e he)
  -- piece count
  have hℓ : (totalPieces (roundInst ε I) : ℝ) ≤ 4 * totalPieces I := by
    have : totalPieces (roundInst ε I) ≤ 4 * totalPieces I := by
      unfold totalPieces
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro r _
      show (roundAux ε (refineAux (I.v a r).base (I.v a r).pieces)).length ≤ _
      have := roundAux_length ε (refineAux (I.v a r).base (I.v a r).pieces)
      have := refineAux_length (I.v a r).base (I.v a r).pieces
      omega
    exact_mod_cast this
  obtain ⟨P1, P2, P3⟩ := hc1 n (roundInst ε I) ε (β + 1) M hn hJ hε hpow hβ' hM
  refine ⟨P1, ?_, ?_⟩
  · intro T π p hrun
    have hT := P2 T π p hrun
    set X : ℝ := (n : ℝ) + totalPieces I + β + 1 / ε + 1 with hX
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hε' : 0 < 1 / ε := by positivity
    have hℓ0 : (0 : ℝ) ≤ totalPieces I := by positivity
    have hX1 : 1 ≤ X := by rw [hX]; linarith
    have hY : (n : ℝ) + totalPieces (roundInst ε I) + (β + 1) + 1 / ε + 1 ≤ 4 * X := by
      rw [hX]; linarith
    have hY0 : 0 ≤ (n : ℝ) + totalPieces (roundInst ε I) + (β + 1) + 1 / ε + 1 := by
      have : (0 : ℝ) ≤ totalPieces (roundInst ε I) := by positivity
      linarith
    calc (T : ℝ) ≤ c1 * ((n : ℝ) + totalPieces (roundInst ε I) + (β + 1) + 1 / ε + 1) ^ c1 := hT
      _ ≤ c1 * (4 * X) ^ c1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ hY0 hY c1
      _ = (c1 * 4 ^ c1 : ℝ) * X ^ c1 := by rw [mul_pow]; ring
      _ ≤ (c1 * 4 ^ c1 : ℝ) * X ^ (c1 * 4 ^ c1 + c1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_right₀ hX1 (by omega)
      _ ≤ ((c1 * 4 ^ c1 + c1 : ℕ) : ℝ) * X ^ (c1 * 4 ^ c1 + c1) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          push_cast; linarith [show (0:ℝ) ≤ c1 by positivity]
  · intro T π p hrun hhalt
    obtain ⟨h0, hEF⟩ := P3 T π p hrun hhalt
    exact ⟨h0, h9 (π T) (p T) h0 hEF⟩
