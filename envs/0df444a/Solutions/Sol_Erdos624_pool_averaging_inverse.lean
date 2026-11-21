-- Prove2me | solution 1 for Erdos624.pool_averaging_inverse
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-20T13:54:07.911778+00:00
-- url     : https://prove2.me/submissions/496846e4-a33b-450c-bada-dd9d39307909

import Mathlib
open Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace E624R21PA
open Finset

variable {α : Type*} [DecidableEq α]

/-- Crude inverse constant: `C 0 v = 1`, `C (r+1) v = 1 + 2 v C r (v-1)`. -/
def C : ℕ → ℕ → ℕ
  | 0, _ => 1
  | r + 1, v => 1 + 2 * v * C r (v - 1)

lemma descFactorial_succ_left (v j : ℕ) :
    v.descFactorial (j + 1) = v * (v - 1).descFactorial j := by
  cases v with
  | zero => simp [Nat.zero_descFactorial_succ]
  | succ v => exact Nat.succ_descFactorial_succ v j

lemma C_eq_sum (r v : ℕ) :
    (C r v : ℝ) = ∑ j ∈ range (r + 1), (2 ^ j * v.descFactorial j : ℝ) := by
  induction r generalizing v with
  | zero =>
    simp [C, Nat.descFactorial_zero]
  | succ r ih =>
    have hrec : (C (r + 1) v : ℝ) = 1 + (2 * v : ℝ) * (C r (v - 1) : ℝ) := by
      simp [C]
    have hterm : ∀ j ∈ range (r + 1),
        (2 ^ (j + 1) * v.descFactorial (j + 1) : ℝ) =
          (2 * v : ℝ) * (2 ^ j * (v - 1).descFactorial j) := by
      intro j _hj
      rw [descFactorial_succ_left, pow_succ]
      push_cast
      ring
    have hshift :
        ∑ j ∈ range (r + 1), (2 ^ (j + 1) * v.descFactorial (j + 1) : ℝ) =
          (2 * v : ℝ) * ∑ j ∈ range (r + 1), (2 ^ j * (v - 1).descFactorial j : ℝ) := by
      rw [sum_congr rfl hterm, ← mul_sum]
    have hsplit :
        ∑ j ∈ range (r + 2), (2 ^ j * v.descFactorial j : ℝ) =
          1 + ∑ j ∈ range (r + 1), (2 ^ (j + 1) * v.descFactorial (j + 1) : ℝ) := by
      rw [sum_range_succ' (fun j => (2 ^ j * (v.descFactorial j : ℝ))) (r + 1)]
      simp [pow_zero, Nat.descFactorial_zero]
      abel
    calc
      (C (r + 1) v : ℝ)
          = 1 + (2 * v : ℝ) * (C r (v - 1) : ℝ) := hrec
      _ = 1 + (2 * v : ℝ) *
            ∑ j ∈ range (r + 1), (2 ^ j * (v - 1).descFactorial j : ℝ) := by
            rw [ih]
      _ = 1 + ∑ j ∈ range (r + 1), (2 ^ (j + 1) * v.descFactorial (j + 1) : ℝ) := by
            rw [← hshift]
      _ = ∑ j ∈ range (r + 2), (2 ^ j * v.descFactorial j : ℝ) := hsplit.symm

noncomputable def poolAvg (r : ℕ) (f : Finset α → ℝ) (P : Finset α) : ℝ :=
  (∑ Y ∈ P.powersetCard r, f Y) / (#P).choose r

lemma choose_mul_pred (v r : ℕ) (hv : 1 ≤ v) (hr : 1 ≤ r) :
    (v : ℝ) * ((v - 1).choose (r - 1) : ℝ) = (r : ℝ) * (v.choose r : ℝ) := by
  obtain ⟨v0, rfl⟩ := Nat.exists_eq_add_of_le' hv
  obtain ⟨r0, rfl⟩ := Nat.exists_eq_add_of_le' hr
  simp
  have h : ((v0 + 1) * v0.choose r0 : ℝ) =
      ((v0 + 1).choose (r0 + 1) * (r0 + 1) : ℝ) :=
    by exact_mod_cast Nat.add_one_mul_choose_eq v0 r0
  linarith

lemma insert_inj_off {x : α} {T T' : Finset α} (hxT : x ∉ T) (hxT' : x ∉ T')
    (h : insert x T = insert x T') : T = T' := by
  ext z
  by_cases hz : z = x
  · subst hz
    simp [hxT, hxT']
  · have : z ∈ insert x T ↔ z ∈ insert x T' := by rw [h]
    simpa [mem_insert, hz] using this

lemma sum_powersetCard_cons (r : ℕ) (f : Finset α → ℝ) (Q : Finset α) (x : α)
    (hx : x ∉ Q) (hr : 1 ≤ r) :
    ∑ Y ∈ (insert x Q).powersetCard r, f Y =
      ∑ T ∈ Q.powersetCard (r - 1), f (insert x T) + ∑ Y ∈ Q.powersetCard r, f Y := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' hr
  subst hn
  have hunion := powersetCard_succ_insert (s := Q) (x := x) hx n
  have hdisj :
      Disjoint (Q.powersetCard (n + 1)) ((Q.powersetCard n).image (insert x)) := by
    refine disjoint_left.2 ?_
    intro Y hY hYim
    obtain ⟨T, hT, rfl⟩ := mem_image.1 hYim
    have hxY : x ∈ insert x T := mem_insert_self x T
    have hYQ : insert x T ⊆ Q := (mem_powersetCard.1 hY).1
    exact hx (hYQ hxY)
  have himg :
      ∑ Y ∈ (Q.powersetCard n).image (insert x), f Y =
        ∑ T ∈ Q.powersetCard n, f (insert x T) := by
    refine sum_image ?_
    intro T hT T' hT' hEq
    have hxT : x ∉ T := fun h => hx ((mem_powersetCard.1 hT).1 h)
    have hxT' : x ∉ T' := fun h => hx ((mem_powersetCard.1 hT').1 h)
    exact insert_inj_off hxT hxT' hEq
  simpa [Nat.add_one_sub_one, add_comm] using (by
    rw [hunion, sum_union hdisj, himg])

lemma card_insert_pred (Q : Finset α) (x : α) (hx : x ∉ Q) {m : ℕ}
    (hQ : #Q = m - 1) (hm : 1 ≤ m) : #(insert x Q) = m := by
  rw [card_insert_of_notMem hx, hQ, Nat.sub_add_cancel hm]

lemma avg_diff (r v : ℕ) (f : Finset α → ℝ) (Q : Finset α) (x y : α)
    (hx : x ∉ Q) (hy : y ∉ Q) (hxy : x ≠ y) (hQ : #Q = v - 1)
    (hr : 1 ≤ r) (hrv : r ≤ v) (hv : 1 ≤ v) :
    poolAvg (r - 1) (fun T => f (insert x T) - f (insert y T)) Q =
      (v / r : ℝ) * (poolAvg r f (insert x Q) - poolAvg r f (insert y Q)) := by
  classical
  have hxQ : #(insert x Q) = v := card_insert_pred Q x hx hQ hv
  have hyQ : #(insert y Q) = v := card_insert_pred Q y hy hQ hv
  have hsumx := sum_powersetCard_cons r f Q x hx hr
  have hsumy := sum_powersetCard_cons r f Q y hy hr
  have hnum :
      ∑ Y ∈ (insert x Q).powersetCard r, f Y - ∑ Y ∈ (insert y Q).powersetCard r, f Y =
        ∑ T ∈ Q.powersetCard (r - 1), (f (insert x T) - f (insert y T)) := by
    rw [hsumx, hsumy, sum_sub_distrib]
    ring
  have hden : ((v - 1).choose (r - 1) : ℝ) ≠ 0 := by
    have hle : r - 1 ≤ v - 1 := Nat.sub_le_sub_right hrv 1
    exact_mod_cast (Nat.choose_pos hle).ne'
  have hdenv : (v.choose r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hrv).ne'
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.1 hr)
  have hch := choose_mul_pred v r hv hr
  unfold poolAvg
  rw [hxQ, hyQ, hQ]
  have hfun :
      ∑ T ∈ Q.powersetCard (r - 1), (fun T => f (insert x T) - f (insert y T)) T =
        ∑ T ∈ Q.powersetCard (r - 1), (f (insert x T) - f (insert y T)) := rfl
  rw [hfun, ← hnum]
  set Sx := ∑ Y ∈ (insert x Q).powersetCard r, f Y
  set Sy := ∑ Y ∈ (insert y Q).powersetCard r, f Y
  set Cv := (v.choose r : ℝ)
  set Cp := ((v - 1).choose (r - 1) : ℝ)
  have : (Sx - Sy) / Cp = (v / r : ℝ) * (Sx / Cv - Sy / Cv) := by
    field_simp [hden, hdenv, hr0]
    -- (Sx - Sy) * r * Cv = (Sx - Sy) * Cp * v
    have h3 : (r : ℝ) * Cv = (v : ℝ) * Cp := by linarith [hch]
    rw [mul_assoc, h3, mul_comm (v : ℝ) Cp, ← mul_assoc]
  simpa [Sx, Sy, Cv, Cp] using this

lemma card_sdiff_eq_of_card_eq {s t : Finset α} (h : #s = #t) : #(s \ t) = #(t \ s) := by
  have hs := card_sdiff (s := s) (t := t)
  have ht := card_sdiff (s := t) (t := s)
  have hinter : #(s ∩ t) = #(t ∩ s) := by rw [inter_comm]
  omega

lemma swap_step_bound (X : Finset α) (r : ℕ) (f : Finset α → ℝ) (δ : ℝ)
    (hδ : ∀ x y : α, x ≠ y → x ∈ X → y ∈ X →
      ∀ T ⊆ X, x ∉ T → y ∉ T → #T = r - 1 →
        |f (insert x T) - f (insert y T)| ≤ δ)
    (hδ0 : 0 ≤ δ)
    (Y Z : Finset α) (hY : Y ⊆ X) (hZ : Z ⊆ X) (hYc : #Y = r) (hZc : #Z = r)
    (hr : 1 ≤ r) :
    |f Y - f Z| ≤ (#(Y \ Z) : ℝ) * δ := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ Y Z : Finset α, Y ⊆ X → Z ⊆ X → #Y = r → #Z = r → #(Y \ Z) = n →
      |f Y - f Z| ≤ (n : ℝ) * δ
  have hP : ∀ n, P n := by
    intro n
    induction n with
    | zero =>
      intro Y Z hY hZ hYc hZc hn
      have hss : Y ⊆ Z := by
        intro y hy
        by_contra hyZ
        have : y ∈ Y \ Z := mem_sdiff.2 ⟨hy, hyZ⟩
        have : 0 < #(Y \ Z) := card_pos.2 ⟨y, this⟩
        omega
      have hEq : Y = Z := eq_of_subset_of_card_le hss (by omega)
      simp [hEq]
    | succ n ih =>
      intro Y Z hY hZ hYc hZc hn
      have hpos : 0 < #(Y \ Z) := by rw [hn]; exact Nat.succ_pos _
      obtain ⟨x, hx⟩ := card_pos.mp hpos
      have hxY : x ∈ Y := (mem_sdiff.1 hx).1
      have hxZ : x ∉ Z := (mem_sdiff.1 hx).2
      have hposZ : 0 < #(Z \ Y) := by
        rw [← card_sdiff_eq_of_card_eq (hYc.trans hZc.symm), hn]
        exact Nat.succ_pos _
      obtain ⟨y, hy⟩ := card_pos.mp hposZ
      have hyZ : y ∈ Z := (mem_sdiff.1 hy).1
      have hyY : y ∉ Y := (mem_sdiff.1 hy).2
      have hxy : x ≠ y := fun h => hyY (h ▸ hxY)
      let Y' : Finset α := insert y (Y.erase x)
      have hyYer : y ∉ Y.erase x := fun h => hyY (mem_of_mem_erase h)
      have hY'c : #Y' = r := by
        rw [card_insert_of_notMem hyYer, card_erase_of_mem hxY, hYc, Nat.sub_add_cancel hr]
      have hY'X : Y' ⊆ X := insert_subset (hZ hyZ) ((erase_subset x Y).trans hY)
      have hT : Y.erase x ⊆ X := (erase_subset x Y).trans hY
      have hTc : #(Y.erase x) = r - 1 := by rw [card_erase_of_mem hxY, hYc]
      have hxT : x ∉ Y.erase x := notMem_erase x Y
      have hstep : |f Y - f Y'| ≤ δ := by
        have hYins : insert x (Y.erase x) = Y := insert_erase hxY
        simpa [Y', hYins] using hδ x y hxy (hY hxY) (hZ hyZ) (Y.erase x) hT hxT hyYer hTc
      have hdiff' : Y' \ Z = (Y \ Z).erase x := by
        ext z
        constructor
        · intro hz
          have hzY' : z ∈ Y' := (mem_sdiff.1 hz).1
          have hzZ : z ∉ Z := (mem_sdiff.1 hz).2
          have : z = y ∨ z ∈ Y.erase x := mem_insert.1 hzY'
          rcases this with rfl | hzYer
          · exact (hzZ hyZ).elim
          · exact mem_erase.2 ⟨(mem_erase.1 hzYer).1, mem_sdiff.2 ⟨(mem_erase.1 hzYer).2, hzZ⟩⟩
        · intro hz
          have hzx : z ≠ x := (mem_erase.1 hz).1
          have hzYZ : z ∈ Y \ Z := (mem_erase.1 hz).2
          have hzY : z ∈ Y := (mem_sdiff.1 hzYZ).1
          have hzZ : z ∉ Z := (mem_sdiff.1 hzYZ).2
          have hzY' : z ∈ Y' := mem_insert.2 (Or.inr (mem_erase.2 ⟨hzx, hzY⟩))
          exact mem_sdiff.2 ⟨hzY', hzZ⟩
      have hn' : #(Y' \ Z) = n := by
        rw [hdiff', card_erase_of_mem hx, hn, Nat.add_one_sub_one]
      have ih' : |f Y' - f Z| ≤ (n : ℝ) * δ := ih Y' Z hY'X hZ hY'c hZc hn'
      have htri : |f Y - f Z| ≤ δ + (n : ℝ) * δ :=
        le_trans (abs_sub_le (f Y) (f Y') (f Z)) (add_le_add hstep ih')
      have : |f Y - f Z| ≤ ((n : ℝ) + 1) * δ := by linarith
      simpa [hn, Nat.cast_succ] using this
  exact hP _ Y Z hY hZ hYc hZc rfl


lemma abs_poolAvg_sub (r : ℕ) (f : Finset α → ℝ) (P : Finset α) (Y : Finset α) (δ : ℝ)
    (hδ : ∀ Z ∈ P.powersetCard r, |f Y - f Z| ≤ δ)
    (hδ0 : 0 ≤ δ) (hYc : #Y = r) (hPc : r ≤ #P) :
    |f Y - poolAvg r f P| ≤ δ := by
  have hpos : (0 : ℝ) < (#P).choose r := by exact_mod_cast Nat.choose_pos hPc
  have hne : ((#P).choose r : ℝ) ≠ 0 := hpos.ne'
  have hid : f Y - (∑ Z ∈ P.powersetCard r, f Z) / ((#P).choose r : ℝ) =
      (∑ Z ∈ P.powersetCard r, (f Y - f Z)) / ((#P).choose r : ℝ) := by
    have : ∑ Z ∈ P.powersetCard r, (f Y - f Z) =
        (#(P.powersetCard r) : ℝ) * f Y - ∑ Z ∈ P.powersetCard r, f Z := by
      simp [sum_sub_distrib, sum_const, nsmul_eq_mul]
    rw [this, card_powersetCard]
    field_simp [hne]
  unfold poolAvg
  rw [hid, abs_div, abs_of_pos hpos]
  have hsum' : |∑ Z ∈ P.powersetCard r, (f Y - f Z)| ≤ ((#P).choose r : ℝ) * δ := by
    have hs : |∑ Z ∈ P.powersetCard r, (f Y - f Z)| ≤
        ∑ Z ∈ P.powersetCard r, |f Y - f Z| :=
      abs_sum_le_sum_abs (fun Z => f Y - f Z) (P.powersetCard r)
    have hs' : ∑ Z ∈ P.powersetCard r, |f Y - f Z| ≤ ∑ Z ∈ P.powersetCard r, δ :=
      sum_le_sum fun Z hZ => hδ Z hZ
    have hs'' : ∑ Z ∈ P.powersetCard r, (δ : ℝ) = ((#P).choose r : ℝ) * δ := by
      simp [sum_const, card_powersetCard, nsmul_eq_mul]
    linarith
  exact (div_le_iff₀ hpos).2 (by linarith)


lemma pool_averaging_inverse_C (X : Finset α) (r v : ℕ) (f : Finset α → ℝ) (ε : ℝ)
    (hrv : r ≤ v) (hN : r + v ≤ #X) (hε : 0 ≤ ε)
    (hAvg : ∀ P ⊆ X, #P = v → |poolAvg r f P| ≤ ε) :
    ∀ Y ⊆ X, #Y = r → |f Y| ≤ (C r v : ℝ) * ε := by
  classical
  induction r generalizing X v f ε with
  | zero =>
    intro Y hY hYc
    have hY0 : Y = ∅ := card_eq_zero.1 hYc
    have hvX : v ≤ #X := by linarith
    obtain ⟨P, hPX, hPc⟩ := exists_subset_card_eq (s := X) hvX
    have havg0 : poolAvg 0 f P = f ∅ := by
      simp [poolAvg, powersetCard_zero, hPc, Nat.choose_zero_right]
    have hP := hAvg P hPX hPc
    simpa [hY0, havg0, C] using hP
  | succ r ih =>
    intro Y hY hYc
    have hr : 1 ≤ r + 1 := Nat.succ_pos _
    have hv : 1 ≤ v := le_trans hr hrv
    have hrv' : r ≤ v - 1 := by omega
    have hden0 : (0 : ℝ) ≤ (r : ℝ) + 1 :=
      add_nonneg (Nat.cast_nonneg r) (by norm_num : (0 : ℝ) ≤ 1)
    have hε'0 : 0 ≤ ((2 * v : ℝ) / (r + 1)) * ε :=
      mul_nonneg (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg _))
        hden0) hε
    have hdiff : ∀ x y : α, x ∈ X → y ∈ X → x ≠ y →
        ∀ Q ⊆ X \ {x, y}, #Q = v - 1 →
          |poolAvg r (fun T => f (insert x T) - f (insert y T)) Q| ≤
            ((2 * v : ℝ) / (r + 1)) * ε := by
      intro x y hxX hyX hxy Q hQsub hQc
      have hxQ : x ∉ Q := by
        intro h
        have := (mem_sdiff.1 (hQsub h)).2
        simp [hxy] at this
      have hyQ : y ∉ Q := by
        intro h
        have := (mem_sdiff.1 (hQsub h)).2
        simp at this
      have hQxX : insert x Q ⊆ X := by
        intro z hz
        rcases mem_insert.1 hz with rfl | hzQ
        · exact hxX
        · exact (mem_sdiff.1 (hQsub hzQ)).1
      have hQyX : insert y Q ⊆ X := by
        intro z hz
        rcases mem_insert.1 hz with rfl | hzQ
        · exact hyX
        · exact (mem_sdiff.1 (hQsub hzQ)).1
      have hQxv : #(insert x Q) = v := card_insert_pred Q x hxQ hQc hv
      have hQyv : #(insert y Q) = v := card_insert_pred Q y hyQ hQc hv
      have hident := avg_diff (r + 1) v f Q x y hxQ hyQ hxy hQc hr hrv hv
      have habs :
          |poolAvg r (fun T => f (insert x T) - f (insert y T)) Q| =
            |(v / (r + 1) : ℝ) *
              (poolAvg (r + 1) f (insert x Q) - poolAvg (r + 1) f (insert y Q))| := by
        simpa [Nat.add_one_sub_one] using congrArg abs hident
      have hAx : |poolAvg (r + 1) f (insert x Q)| ≤ ε := hAvg _ hQxX hQxv
      have hAy : |poolAvg (r + 1) f (insert y Q)| ≤ ε := hAvg _ hQyX hQyv
      have hsub : |poolAvg (r + 1) f (insert x Q) - poolAvg (r + 1) f (insert y Q)| ≤
          2 * ε := by
        set a := poolAvg (r + 1) f (insert x Q)
        set b := poolAvg (r + 1) f (insert y Q)
        calc
          |a - b| = |a + -b| := by rw [sub_eq_add_neg]
          _ ≤ |a| + |-b| := abs_add_le a (-b)
          _ = |a| + |b| := by rw [abs_neg]
          _ ≤ ε + ε := add_le_add hAx hAy
          _ = 2 * ε := by ring
      have hcoef : 0 ≤ (v / (r + 1) : ℝ) :=
        div_nonneg (Nat.cast_nonneg _) hden0
      have hmul : |poolAvg r (fun T => f (insert x T) - f (insert y T)) Q| ≤
          (v / (r + 1) : ℝ) * (2 * ε) := by
        rw [habs, abs_mul, abs_of_nonneg hcoef]
        exact mul_le_mul_of_nonneg_left hsub hcoef
      have heq : (v / (r + 1) : ℝ) * (2 * ε) = ((2 * v : ℝ) / (r + 1)) * ε := by ring
      rw [← heq]
      exact hmul
    have hδval : ℝ := ((2 * v : ℝ) / (r + 1)) * (C r (v - 1) : ℝ) * ε
    have hδ0 : 0 ≤ ((2 * v : ℝ) / (r + 1)) * (C r (v - 1) : ℝ) * ε :=
      mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (Nat.cast_nonneg _)) hden0) (Nat.cast_nonneg _)) hε
    have hδ : ∀ x y : α, x ≠ y → x ∈ X → y ∈ X →
        ∀ T ⊆ X, x ∉ T → y ∉ T → #T = r →
          |f (insert x T) - f (insert y T)| ≤
            ((2 * v : ℝ) / (r + 1)) * (C r (v - 1) : ℝ) * ε := by
      intro x y hxy hxX hyX T hT hxT hyT hTc
      have hpair : ({x, y} : Finset α) ⊆ X := insert_subset hxX (by simpa using hyX)
      have hTX' : T ⊆ X \ {x, y} := by
        intro z hz
        refine mem_sdiff.2 ⟨hT hz, ?_⟩
        intro hzpair
        have hzxy : z = x ∨ z = y := by
          simpa [mem_insert, mem_singleton] using hzpair
        rcases hzxy with rfl | rfl
        · exact hxT hz
        · exact hyT hz
      have hxy2 : #({x, y} : Finset α) = 2 := by
        rw [card_insert_of_notMem (by simpa using hxy)]
        simp
      have hN' : r + (v - 1) ≤ #(X \ {x, y}) := by
        rw [card_sdiff_of_subset hpair, hxy2]
        omega
      have hAvg' : ∀ Q ⊆ X \ {x, y}, #Q = v - 1 →
          |poolAvg r (fun S => f (insert x S) - f (insert y S)) Q| ≤
            ((2 * v : ℝ) / (r + 1)) * ε :=
        fun Q hQsub hQc => hdiff x y hxX hyX hxy Q hQsub hQc
      have ihg :=
        ih (X \ {x, y}) (v - 1) (fun S => f (insert x S) - f (insert y S))
          (((2 * v : ℝ) / (r + 1)) * ε) hrv' hN' hε'0 hAvg' T hTX' hTc
      have : ((2 * v : ℝ) / (r + 1)) * ε * (C r (v - 1) : ℝ) =
          ((2 * v : ℝ) / (r + 1)) * (C r (v - 1) : ℝ) * ε := by ring
      linarith
    have hswap :=
      swap_step_bound (X := X) (r := r + 1) (f := f)
        (((2 * v : ℝ) / (r + 1)) * (C r (v - 1) : ℝ) * ε) hδ hδ0
    have hvX : v ≤ #X := by omega
    obtain ⟨P, hYP, hPX, hPc⟩ :=
      exists_subsuperset_card_eq hY (by omega : #Y ≤ v) hvX
    have hPavg : |poolAvg (r + 1) f P| ≤ ε := hAvg P hPX hPc
    have hZbound : ∀ Z ∈ P.powersetCard (r + 1),
        |f Y - f Z| ≤ (r + 1 : ℝ) * (((2 * v : ℝ) / (r + 1)) * (C r (v - 1) : ℝ) * ε) := by
      intro Z hZ
      have hZX : Z ⊆ X := (mem_powersetCard.1 hZ).1.trans hPX
      have hZc : #Z = r + 1 := (mem_powersetCard.1 hZ).2
      have hsz : |f Y - f Z| ≤ (#(Y \ Z) : ℝ) *
          (((2 * v : ℝ) / (r + 1)) * (C r (v - 1) : ℝ) * ε) :=
        hswap Y Z hY hZX hYc hZc hr
      have hcardle : #(Y \ Z) ≤ r + 1 := by
        have : Y \ Z ⊆ Y := sdiff_subset
        simpa [hYc] using card_le_card this
      have hnn : 0 ≤ ((2 * v : ℝ) / (r + 1)) * (C r (v - 1) : ℝ) * ε := hδ0
      have : (#(Y \ Z) : ℝ) ≤ (r + 1 : ℝ) := by exact_mod_cast hcardle
      exact le_trans hsz (mul_le_mul_of_nonneg_right this hnn)
    have havgsub : |f Y - poolAvg (r + 1) f P| ≤
        (r + 1 : ℝ) * (((2 * v : ℝ) / (r + 1)) * (C r (v - 1) : ℝ) * ε) :=
      abs_poolAvg_sub (r + 1) f P Y
        ((r + 1 : ℝ) * (((2 * v : ℝ) / (r + 1)) * (C r (v - 1) : ℝ) * ε))
        hZbound (mul_nonneg hden0 hδ0) hYc (by omega)
    have hsimp : (r + 1 : ℝ) * (((2 * v : ℝ) / (r + 1)) * (C r (v - 1) : ℝ) * ε) =
        (2 * v : ℝ) * (C r (v - 1) : ℝ) * ε := by
      have hr0 : (r : ℝ) + 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (by linarith [hden0]))
      field_simp [hr0]
    have : |f Y| ≤ ε + (2 * v : ℝ) * (C r (v - 1) : ℝ) * ε := by
      have habsY := abs_add_le (f Y - poolAvg (r + 1) f P) (poolAvg (r + 1) f P)
      have : |f Y| ≤ |f Y - poolAvg (r + 1) f P| + |poolAvg (r + 1) f P| := by
        simpa using habsY
      linarith [hPavg, havgsub, hsimp]
    have hC : (C (r + 1) v : ℝ) = 1 + (2 * v : ℝ) * (C r (v - 1) : ℝ) := by
      simp [C]
    have : |f Y| ≤ (C (r + 1) v : ℝ) * ε := by
      rw [hC]
      linarith
    exact this

theorem pool_averaging_inverse (X : Finset α) (r v : ℕ) (f : Finset α → ℝ) (ε : ℝ)
    (hrv : r ≤ v) (hN : r + v ≤ #X) (hε : 0 ≤ ε)
    (hAvg : ∀ P ⊆ X, #P = v →
      |(∑ Y ∈ P.powersetCard r, f Y) / (v.choose r : ℝ)| ≤ ε) :
    ∀ Y ⊆ X, #Y = r →
      |f Y| ≤ (∑ j ∈ range (r + 1), (2 ^ j * v.descFactorial j : ℝ)) * ε := by
  intro Y hY hYc
  have hAvg' : ∀ P ⊆ X, #P = v → |poolAvg r f P| ≤ ε := by
    intro P hPX hPc
    simpa [poolAvg, hPc] using hAvg P hPX hPc
  have := pool_averaging_inverse_C X r v f ε hrv hN hε hAvg' Y hY hYc
  rwa [C_eq_sum] at this

end E624R21PA

namespace Erdos624
open Finset

theorem pool_averaging_inverse {α : Type*} [DecidableEq α]
    (X : Finset α) (r v : ℕ) (f : Finset α → ℝ) (ε : ℝ)
    (hrv : r ≤ v) (hN : r + v ≤ #X) (hε : 0 ≤ ε)
    (hAvg : ∀ P ⊆ X, #P = v →
      |(∑ Y ∈ P.powersetCard r, f Y) / (v.choose r : ℝ)| ≤ ε) :
    ∀ Y ⊆ X, #Y = r →
      |f Y| ≤ (∑ j ∈ range (r + 1), (2 ^ j * v.descFactorial j : ℝ)) * ε :=
  E624R21PA.pool_averaging_inverse X r v f ε hrv hN hε hAvg

end Erdos624

open Finset

theorem solution {α : Type*} [DecidableEq α]
    (X : Finset α) (r v : ℕ) (f : Finset α → ℝ) (ε : ℝ)
    (hrv : r ≤ v) (hN : r + v ≤ #X) (hε : 0 ≤ ε)
    (hAvg : ∀ P ⊆ X, #P = v →
      |(∑ Y ∈ P.powersetCard r, f Y) / (v.choose r : ℝ)| ≤ ε) :
    ∀ Y ⊆ X, #Y = r →
      |f Y| ≤ (∑ j ∈ range (r + 1), (2 ^ j * v.descFactorial j : ℝ)) * ε :=
  Erdos624.pool_averaging_inverse X r v f ε hrv hN hε hAvg

