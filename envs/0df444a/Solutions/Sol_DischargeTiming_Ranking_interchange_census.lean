-- Prove2me | solution 1 for DischargeTiming.Ranking.interchange_census
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T00:06:43.362981+00:00
-- url     : https://prove2.me/submissions/54b54b29-aaae-4b69-8cec-5716b972c934

import Mathlib
import Definitions.Def_DischargeTiming_Ranking_Model

namespace DischargeTiming.Ranking
namespace DTcore

variable {M J : ℕ}

lemma traj_succ_zero (x0 : State M J) (arr : ℕ → Fin M → ℕ) (D : ℕ → Action M J) (i : ℕ)
    (m : Fin M) (h : 0 < J + 1) : traj x0 arr D (i + 1) m ⟨0, h⟩ = arr i m := by
  simp [traj, step]

lemma traj_succ_pos (x0 : State M J) (arr : ℕ → Fin M → ℕ) (D : ℕ → Action M J) (i j : ℕ)
    (m : Fin M) (h : j + 1 < J + 1) (h' : j < J + 1) :
    traj x0 arr D (i + 1) m ⟨j + 1, h⟩
      = traj x0 arr D i m ⟨j, h'⟩ - D i m ⟨j, h'⟩ := by
  simp [traj, step]

lemma unit_apply (m0 : Fin M) (j0 : Fin (J + 1)) (m : Fin M) (j : Fin (J + 1)) :
    unitAction m0 j0 m j = if m.val = m0.val ∧ j.val = j0.val then 1 else 0 := by
  simp [unitAction, Fin.ext_iff]

lemma inter_apply (D : ℕ → Action M J) (k k' : ℕ) (hkk : k < k') (m1 : Fin M)
    (t1 p1 : Fin (J + 1)) (m2 : Fin M) (t2 p2 : Fin (J + 1)) (i : ℕ) (m : Fin M)
    (j : Fin (J + 1)) :
    interchange D k k' m1 t1 p1 m2 t2 p2 i m j =
      if i = k then D i m j + (if m.val = m1.val ∧ j.val = t1.val then 1 else 0)
          - (if m.val = m2.val ∧ j.val = t2.val then 1 else 0)
      else if i = k' then D i m j - (if m.val = m1.val ∧ j.val = p1.val then 1 else 0)
          + (if m.val = m2.val ∧ j.val = p2.val then 1 else 0)
      else D i m j := by
  unfold interchange
  by_cases h : i = k
  · subst h; simp [unit_apply]
  · by_cases h' : i = k'
    · subst h'; simp [h, unit_apply]
    · simp [h, h']

lemma step_arith (i k k' H j0 t1 t2 m m1 m2 X' X d : ℕ) (hkk' : k < k') (hi : i + 1 ≤ H)
    (IH : (X' + if k < i ∧ i ≤ k' ∧ m = m1 ∧ j0 + k = t1 + i then 1 else 0) =
      X + if k < i ∧ i ≤ k' ∧ m = m2 ∧ j0 + k = t2 + i then 1 else 0)
    (hd2 : i = k ∧ m = m2 ∧ j0 = t2 → 1 ≤ d)
    (hdl : i = k' ∧ i < H ∧ m = m1 ∧ j0 = t1 + (k' - k) → 1 ≤ d)
    (hle : d ≤ X)
    (hc : k ≤ i ∧ i < k' ∧ m = m1 ∧ j0 + k = t1 + i → d + 1 ≤ X) :
    ((X' -
        if i = k then (d + if m = m1 ∧ j0 = t1 then 1 else 0) - if m = m2 ∧ j0 = t2 then 1 else 0
        else
          if i = k' then
            (d - if m = m1 ∧ j0 = t1 + (k' - k) then 1 else 0)
              + if m = m2 ∧ j0 = t2 + (k' - k) then 1 else 0
          else d) +
      if k < i + 1 ∧ i + 1 ≤ k' ∧ m = m1 ∧ j0 + 1 + k = t1 + (i + 1) then 1 else 0) =
    X - d + if k < i + 1 ∧ i + 1 ≤ k' ∧ m = m2 ∧ j0 + 1 + k = t2 + (i + 1) then 1 else 0 := by
  rcases (show i < k ∨ i = k ∨ (k < i ∧ i < k') ∨ i = k' ∨ k' < i by omega) with
        hpos | hpos | hpos | hpos | hpos <;>
  by_cases hm1 : m = m1 <;> by_cases hm2 : m = m2 <;>
  · simp only [hm1, hm2, true_and, false_and, and_true, and_false, if_false] at IH hc hd2 hdl ⊢
    try simp (disch := omega) only [if_pos, if_neg] at IH ⊢
    (try split_ifs at IH ⊢) <;> omega

lemma feas_arith (i k k' H j t1 t2 m m1 m2 X' X d : ℕ) (hkk' : k < k') (hi : i < H)
    (IH : (X' + if k < i ∧ i ≤ k' ∧ m = m1 ∧ j + k = t1 + i then 1 else 0) =
      X + if k < i ∧ i ≤ k' ∧ m = m2 ∧ j + k = t2 + i then 1 else 0)
    (hdl : i = k' ∧ i < H ∧ m = m1 ∧ j = t1 + (k' - k) → 1 ≤ d)
    (hle : d ≤ X)
    (hc : k ≤ i ∧ i < k' ∧ m = m1 ∧ j + k = t1 + i → d + 1 ≤ X) :
    (if i = k then (d + if m = m1 ∧ j = t1 then 1 else 0) - if m = m2 ∧ j = t2 then 1 else 0
        else
          if i = k' then
            (d - if m = m1 ∧ j = t1 + (k' - k) then 1 else 0)
              + if m = m2 ∧ j = t2 + (k' - k) then 1 else 0
          else d) ≤ X' := by
  rcases (show i < k ∨ i = k ∨ (k < i ∧ i < k') ∨ i = k' ∨ k' < i by omega) with
        hpos | hpos | hpos | hpos | hpos <;>
  by_cases hm1 : m = m1 <;> by_cases hm2 : m = m2 <;>
  · simp only [hm1, hm2, true_and, false_and, and_true, and_false, if_false] at IH hc hdl ⊢
    try simp (disch := omega) only [if_pos, if_neg] at IH ⊢
    (try split_ifs at IH ⊢) <;> omega

lemma last_arith (i k k' H J t1 t2 m m1 m2 X' X d : ℕ) (hkk' : k < k') (hi : i < H)
    (h1 : t1 + (k' - k) ≤ J) (h2 : t2 + (k' - k) ≤ J)
    (IH : (X' + if k < i ∧ i ≤ k' ∧ m = m1 ∧ J + k = t1 + i then 1 else 0) =
      X + if k < i ∧ i ≤ k' ∧ m = m2 ∧ J + k = t2 + i then 1 else 0)
    (hdl : i = k' ∧ i < H ∧ m = m1 ∧ J = t1 + (k' - k) → 1 ≤ d)
    (hle : d = X)
    (hc : k ≤ i ∧ i < k' ∧ m = m1 ∧ J + k = t1 + i → d + 1 ≤ X) :
    (if i = k then (d + if m = m1 ∧ J = t1 then 1 else 0) - if m = m2 ∧ J = t2 then 1 else 0
        else
          if i = k' then
            (d - if m = m1 ∧ J = t1 + (k' - k) then 1 else 0)
              + if m = m2 ∧ J = t2 + (k' - k) then 1 else 0
          else d) = X' := by
  rcases (show i < k ∨ i = k ∨ (k < i ∧ i < k') ∨ i = k' ∨ k' < i by omega) with
        hpos | hpos | hpos | hpos | hpos <;>
  by_cases hm1 : m = m1 <;> by_cases hm2 : m = m2 <;>
  · simp only [hm1, hm2, true_and, false_and, and_true, and_false, if_false] at IH hc hdl ⊢
    try simp (disch := omega) only [if_pos, if_neg] at IH ⊢
    (try split_ifs at IH ⊢) <;> omega

/-- Indicator of the shifted cohort `(m0, t0 + (i - k))` inside the window `k < i ≤ k'`. -/
def Aind (k k' : ℕ) (m0 : Fin M) (t0 : ℕ) (i : ℕ) (m : Fin M) (j : Fin (J + 1)) : ℕ :=
  if k < i ∧ i ≤ k' ∧ m.val = m0.val ∧ j.val + k = t0 + i then 1 else 0

lemma sum_Aind (k k' : ℕ) (m0 : Fin M) (t0 : ℕ) (ht : t0 + (k' - k) ≤ J) (i : ℕ) :
    ∑ m, ∑ j, (Aind (J := J) k k' m0 t0 i m j) = if k < i ∧ i ≤ k' then 1 else 0 := by
  by_cases hw : k < i ∧ i ≤ k'
  · rw [if_pos hw]
    rw [Finset.sum_eq_single m0]
    · rw [Finset.sum_eq_single (⟨t0 + i - k, by omega⟩ : Fin (J + 1))]
      · unfold Aind; rw [if_pos]; refine ⟨hw.1, hw.2, rfl, ?_⟩; show t0 + i - k + k = t0 + i; omega
      · intro b _ hb; simp only [Aind]; rw [if_neg]; intro hc; apply hb; ext; simp; omega
      · simp
    · intro b _ hb
      apply Finset.sum_eq_zero; intro j _
      simp only [Aind]; rw [if_neg]; intro hc; exact hb (Fin.ext hc.2.2.1)
    · simp
  · rw [if_neg hw]
    apply Finset.sum_eq_zero; intro m _
    apply Finset.sum_eq_zero; intro j _
    simp only [Aind]; rw [if_neg]; intro hc; exact hw ⟨hc.1, hc.2.1⟩

section Inter

variable (P : Model M J) (x0 : State M J) (arr : ℕ → Fin M → ℕ) (H : ℕ) (D : ℕ → Action M J)
    (hD : FeasibleSchedule P x0 arr H D)
    (m1 m2 : Fin M) (t1 t2 : Fin (J + 1)) (k k' : ℕ) (hkk' : k < k') (hk'H : k' ≤ H)
    (h1 : (t1 : ℕ) + (k' - k) ≤ J) (h2 : (t2 : ℕ) + (k' - k) ≤ J)
    (hD2 : 1 ≤ D k m2 t2) (hD1 : D k m1 t1 < traj x0 arr D k m1 t1)
    (hlate : k' < H → 1 ≤ D k' m1 (losShift t1 (k' - k) h1))
    (hterm : k' = H → 1 ≤ traj x0 arr D H m1 (losShift t1 (k' - k) h1))

include hD hkk' hk'H hlate hterm in
lemma cohort_end : 1 ≤ traj x0 arr D k' m1 (losShift t1 (k' - k) h1) := by
  rcases lt_or_eq_of_le hk'H with h | h
  · exact le_trans (hlate h) ((hD k' h).1 _ _)
  · have := hterm h; subst h; exact this

include hD hkk' hk'H hlate hterm in
lemma cohort : ∀ i, k ≤ i → i < k' → ∀ (m : Fin M) (j : Fin (J + 1)), m.val = m1.val →
    j.val + k = t1.val + i → D i m j + 1 ≤ traj x0 arr D i m j := by
  have hX := cohort_end P x0 arr H D hD m1 t1 k k' hkk' hk'H h1 hlate hterm
  suffices hs : ∀ n i, i + n + 1 = k' → k ≤ i → ∀ (m : Fin M) (j : Fin (J + 1)),
      m.val = m1.val → j.val + k = t1.val + i → D i m j + 1 ≤ traj x0 arr D i m j by
    intro i hki hik m j hm hj
    exact hs (k' - i - 1) i (by omega) hki m j hm hj
  intro n
  induction n with
  | zero =>
    intro i hi hki m j hm hj
    have hm' : m = m1 := Fin.ext hm
    subst hm'
    have hjJ : j.val + 1 < J + 1 := by omega
    have e := traj_succ_pos x0 arr D i j.val m hjJ j.isLt
    have hfe := (hD i (by omega)).1 m j
    have hX' : 1 ≤ traj x0 arr D (i + 1) m ⟨j.val + 1, hjJ⟩ := by
      have e2 : k' = i + 1 := by omega
      subst e2
      convert hX using 2
      ext; simp [losShift]; omega
    rw [e] at hX'
    simp only [Fin.eta] at hX'
    omega
  | succ n ih =>
    intro i hi hki m j hm hj
    have hjJ : j.val + 1 < J + 1 := by omega
    have := ih (i + 1) (by omega) (by omega) m ⟨j.val + 1, hjJ⟩ hm (by simp; omega)
    rw [traj_succ_pos x0 arr D i j.val m hjJ j.isLt] at this
    simp only [Fin.eta] at this
    have hfe := (hD i (by omega)).1 m j
    omega

include hD hkk' hk'H hD2 hlate hterm in
lemma relation : ∀ i ≤ H, ∀ (m : Fin M) (j : Fin (J + 1)),
    traj x0 arr (interchange D k k' m1 t1 (losShift t1 (k' - k) h1) m2 t2
        (losShift t2 (k' - k) h2)) i m j + Aind k k' m1 t1.val i m j
      = traj x0 arr D i m j + Aind k k' m2 t2.val i m j := by
  have hco := cohort P x0 arr H D hD m1 t1 k k' hkk' hk'H h1 hlate hterm
  have hp1 : (losShift t1 (k' - k) h1).val = t1.val + (k' - k) := rfl
  have hp2 : (losShift t2 (k' - k) h2).val = t2.val + (k' - k) := rfl
  intro i
  induction i with
  | zero =>
    intro _ m j
    simp [traj, Aind]
  | succ i ih =>
    intro hi m j
    rcases j with ⟨_ | j0, hj⟩
    · rw [traj_succ_zero, traj_succ_zero]
      simp only [Aind]
      split_ifs <;> omega
    · have hj0 : j0 < J + 1 := by omega
      rw [traj_succ_pos _ _ _ _ _ _ _ hj0, traj_succ_pos _ _ _ _ _ _ _ hj0]
      have IH := ih (by omega) m ⟨j0, hj0⟩
      rw [inter_apply D k k' hkk']
      have hle := (hD i (by omega)).1 m ⟨j0, hj0⟩
      have hc : k ≤ i ∧ i < k' ∧ m.val = m1.val ∧ j0 + k = t1.val + i →
          D i m ⟨j0, hj0⟩ + 1 ≤ traj x0 arr D i m ⟨j0, hj0⟩ :=
        fun h => hco i h.1 h.2.1 m _ h.2.2.1 h.2.2.2
      have hd2 : i = k ∧ m.val = m2.val ∧ j0 = t2.val → 1 ≤ D i m ⟨j0, hj0⟩ := by
        rintro ⟨a, b, c⟩
        subst a
        have : m = m2 := Fin.ext b
        subst this
        have : (⟨j0, hj0⟩ : Fin (J + 1)) = t2 := Fin.ext c
        rw [this]; exact hD2
      have hdl : i = k' ∧ i < H ∧ m.val = m1.val ∧ j0 = t1.val + (k' - k) →
          1 ≤ D i m ⟨j0, hj0⟩ := by
        rintro ⟨a, b, c, d⟩
        rw [a]
        have : m = m1 := Fin.ext c
        subst this
        have : (⟨j0, hj0⟩ : Fin (J + 1)) = losShift t1 (k' - k) h1 := Fin.ext d
        rw [this]; exact hlate (by omega)
      simp only [Aind] at IH ⊢
      rw [hp1, hp2]
      clear ih hco
      generalize traj x0 arr (interchange D k k' m1 t1 (losShift t1 (k' - k) h1) m2 t2
        (losShift t2 (k' - k) h2)) i m ⟨j0, hj0⟩ = X' at IH ⊢
      generalize traj x0 arr D i m ⟨j0, hj0⟩ = X at *
      generalize D i m ⟨j0, hj0⟩ = d at *
      exact step_arith i k k' H j0 t1.val t2.val m.val m1.val m2.val X' X d hkk' hi IH hd2 hdl hle hc

include hD hkk' hk'H hD2 hlate hterm in
lemma census_eq : ∀ i ≤ H,
    census (traj x0 arr (interchange D k k' m1 t1 (losShift t1 (k' - k) h1) m2 t2
        (losShift t2 (k' - k) h2)) i) = census (traj x0 arr D i) := by
  intro i hi
  have hr := relation P x0 arr H D hD m1 m2 t1 t2 k k' hkk' hk'H h1 h2 hD2 hlate hterm i hi
  have hs : ∑ m, ∑ j, (traj x0 arr (interchange D k k' m1 t1 (losShift t1 (k' - k) h1) m2 t2
        (losShift t2 (k' - k) h2)) i m j + Aind k k' m1 t1.val i m j)
      = ∑ m, ∑ j, (traj x0 arr D i m j + Aind k k' m2 t2.val i m j) := by
    apply Finset.sum_congr rfl; intro m _
    apply Finset.sum_congr rfl; intro j _
    exact hr m j
  simp only [Finset.sum_add_distrib] at hs
  rw [sum_Aind k k' m1 t1.val h1, sum_Aind k k' m2 t2.val h2] at hs
  unfold census
  omega

end Inter

end DTcore
end DischargeTiming.Ranking

open DischargeTiming.Ranking

theorem solution {M J : ℕ} (P : Model M J) (x0 : State M J)
    (arr : ℕ → Fin M → ℕ) (H : ℕ) (D : ℕ → Action M J)
    (hD : FeasibleSchedule P x0 arr H D)
    (m1 m2 : Fin M) (t1 t2 : Fin (J + 1)) (k k' : ℕ) (hkk' : k < k') (hk'H : k' ≤ H)
    (h1 : (t1 : ℕ) + (k' - k) ≤ J) (h2 : (t2 : ℕ) + (k' - k) ≤ J)
    (hD2 : 1 ≤ D k m2 t2) (hD1 : D k m1 t1 < traj x0 arr D k m1 t1)
    (hlate : k' < H → 1 ≤ D k' m1 (losShift t1 (k' - k) h1))
    (hterm : k' = H → 1 ≤ traj x0 arr D H m1 (losShift t1 (k' - k) h1)) :
    ∀ i ≤ H,
      census (traj x0 arr
          (interchange D k k' m1 t1 (losShift t1 (k' - k) h1) m2 t2 (losShift t2 (k' - k) h2)) i)
        = census (traj x0 arr D i) :=
  DTcore.census_eq P x0 arr H D hD m1 m2 t1 t2 k k' hkk' hk'H h1 h2 hD2 hlate hterm
