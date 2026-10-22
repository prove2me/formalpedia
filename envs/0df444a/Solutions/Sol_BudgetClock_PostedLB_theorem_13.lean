-- Prove2me | solution 1 for BudgetClock.PostedLB.theorem_13
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T18:24:48.700982+00:00
-- url     : https://prove2.me/submissions/5c2f183b-f25a-426e-a07e-2d1cc79deec7

import Mathlib
import Definitions.Def_BudgetClock_PostedLB_Setting

set_option autoImplicit false

namespace BudgetClock.PostedLB

/-- A history reachable by the run of `m` on the costs `c`, built one offer at a time. -/
inductive Valid {n : ℕ} (m : PostedPrice n) (c : Fin n → ℝ) : List (Offer n) → Prop
  | nil : Valid m c []
  | snoc (h : List (Offer n)) (i : Fin n) (p : ℝ) :
      Valid m c h → m.next h = some (i, p) → i ∉ h.map Prod.fst →
      Valid m c (h ++ [(i, p, decide (c i ≤ p))])

theorem valid_runAux {n : ℕ} (m : PostedPrice n) (c : Fin n → ℝ) :
    ∀ (k : ℕ) (h : List (Offer n)), Valid m c h → Valid m c (runAux m c k h) := by
  intro k
  induction k with
  | zero => intro h hv; simpa [runAux] using hv
  | succ k ih =>
    intro h hv
    cases hnext : m.next h with
    | none => simp [runAux, hnext, hv]
    | some ip =>
      obtain ⟨i, p⟩ := ip
      by_cases hi : i ∈ h.map Prod.fst
      · simp [runAux, hnext, hi, hv]
      · have := ih _ (Valid.snoc h i p hv hnext hi)
        simpa [runAux, hnext, hi] using this

theorem valid_run {n : ℕ} (m : PostedPrice n) (c : Fin n → ℝ) : Valid m c (run m c) :=
  valid_runAux m c n [] Valid.nil

theorem runAux_extends {n : ℕ} (m : PostedPrice n) (c : Fin n → ℝ) :
    ∀ (k : ℕ) (h : List (Offer n)), ∃ r, runAux m c k h = h ++ r := by
  intro k
  induction k with
  | zero => intro h; exact ⟨[], by simp [runAux]⟩
  | succ k ih =>
    intro h
    cases hnext : m.next h with
    | none => exact ⟨[], by simp [runAux, hnext]⟩
    | some ip =>
      obtain ⟨i, p⟩ := ip
      by_cases hi : i ∈ h.map Prod.fst
      · exact ⟨[], by simp [runAux, hnext, hi]⟩
      · obtain ⟨r, hr⟩ := ih (h ++ [(i, p, decide (c i ≤ p))])
        exact ⟨(i, p, decide (c i ≤ p)) :: r, by simp [runAux, hnext, hi, hr]⟩

theorem valid_reach {n : ℕ} (m : PostedPrice n) (c : Fin n → ℝ) (h : List (Offer n))
    (hv : Valid m c h) : ∀ k : ℕ, h.length ≤ k → runAux m c k [] = runAux m c (k - h.length) h := by
  induction hv with
  | nil => intro k _; simp
  | snoc h i p _ hnext hi ih =>
    intro k hk
    simp only [List.length_append, List.length_singleton] at hk
    rw [ih k (by omega)]
    have hk' : k - h.length = (k - (h.length + 1)) + 1 := by omega
    rw [hk']
    simp [runAux, hnext, hi, List.length_append]

theorem valid_run_eq {n : ℕ} (m : PostedPrice n) (c : Fin n → ℝ) (h : List (Offer n))
    (hv : Valid m c h) (hl : h.length ≤ n) : ∃ r, run m c = h ++ r := by
  unfold run
  rw [valid_reach m c h hv n hl]
  exact runAux_extends m c _ h

theorem valid_snoc_inv {n : ℕ} (m : PostedPrice n) (c : Fin n → ℝ) (h : List (Offer n))
    (x : Offer n) (hv : Valid m c (h ++ [x])) :
    Valid m c h ∧ m.next h = some (x.1, x.2.1) ∧ x.1 ∉ h.map Prod.fst ∧
      x.2.2 = decide (c x.1 ≤ x.2.1) := by
  generalize hl : h ++ [x] = l at hv
  cases hv with
  | nil => simp at hl
  | snoc h' i p hv' hnext hi =>
    obtain ⟨h1, h2⟩ := List.append_inj' hl rfl
    simp only [List.cons.injEq, and_true] at h2
    subst h1; subst h2
    exact ⟨hv', hnext, hi, rfl⟩

theorem valid_append_left {n : ℕ} (m : PostedPrice n) (c : Fin n → ℝ) (a : List (Offer n)) :
    ∀ b : List (Offer n), Valid m c (a ++ b) → Valid m c a := by
  intro b
  induction b using List.reverseRecOn with
  | nil => intro hv; simpa using hv
  | append_singleton b x ih =>
    intro hv
    rw [← List.append_assoc] at hv
    exact ih (valid_snoc_inv m c _ x hv).1

theorem valid_transfer {n : ℕ} (m : PostedPrice n) (c c' : Fin n → ℝ) (h : List (Offer n))
    (hv : Valid m c h) (hd : ∀ e ∈ h, decide (c' e.1 ≤ e.2.1) = e.2.2) : Valid m c' h := by
  induction hv with
  | nil => exact Valid.nil
  | snoc h i p hv hnext hi ih =>
    have hlast := hd (i, p, decide (c i ≤ p)) (by simp)
    have hrest : ∀ e ∈ h, decide (c' e.1 ≤ e.2.1) = e.2.2 := fun e he => hd e (by simp [he])
    have := Valid.snoc h i p (ih hrest) hnext hi
    simp only at hlast
    rw [hlast] at this
    exact this

theorem valid_nodup {n : ℕ} (m : PostedPrice n) (c : Fin n → ℝ) (h : List (Offer n))
    (hv : Valid m c h) : (h.map Prod.fst).Nodup := by
  induction hv with
  | nil => simp
  | snoc h i p _ _ hi ih =>
    rw [List.map_append, List.nodup_append]
    refine ⟨ih, by simp, ?_⟩
    intro a ha b hb
    simp at hb
    subst hb
    intro hab; subst hab; exact hi ha

theorem valid_dec {n : ℕ} (m : PostedPrice n) (c : Fin n → ℝ) (h : List (Offer n))
    (hv : Valid m c h) : ∀ e ∈ h, e.2.2 = decide (c e.1 ≤ e.2.1) := by
  induction hv with
  | nil => simp
  | snoc h i p _ _ _ ih =>
    intro e he
    rw [List.mem_append] at he
    rcases he with he | he
    · exact ih e he
    · simp at he; subst he; rfl

theorem valid_sum_le {n : ℕ} (m : PostedPrice n) (c : Fin n → ℝ) (h : List (Offer n))
    (hv : Valid m c h) : ∑ j ∈ accepted h, c j ≤ payment h := by
  unfold accepted payment
  have hnd : ((h.filter fun e => e.2.2).map Prod.fst).Nodup :=
    ((List.filter_sublist).map Prod.fst).nodup (valid_nodup m c h hv)
  rw [List.sum_toFinset c hnd, List.map_map]
  apply List.sum_le_sum
  intro e he
  rw [List.mem_filter] at he
  have hd := valid_dec m c h hv e he.1
  rw [he.2] at hd
  exact of_decide_eq_true hd.symm

theorem two_le_sum {n : ℕ} (S : Finset (Fin n)) (c : Fin n → ℝ) (hc : ∀ j, 0 ≤ c j)
    (x y : Fin n) (hx : x ∈ S) (hy : y ∈ S) (hxy : y ≠ x) : c x + c y ≤ ∑ j ∈ S, c j := by
  have hsub : ({x, y} : Finset (Fin n)) ⊆ S := by
    intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
  have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hc j)
  rwa [Finset.sum_pair (Ne.symm hxy)] at this

theorem mem_accepted {n : ℕ} (l : List (Offer n)) (j : Fin n) :
    j ∈ accepted l ↔ ∃ x ∈ l, x.2.2 = true ∧ x.1 = j := by
  unfold accepted
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [List.mem_filter] at hx
    exact ⟨x, hx.1, hx.2, rfl⟩
  · rintro ⟨x, hx, h2, rfl⟩
    exact ⟨x, List.mem_filter.2 ⟨hx, h2⟩, rfl⟩

end BudgetClock.PostedLB

open BudgetClock.PostedLB in
theorem solution (n : ℕ) (hn : 1 ≤ n) (B : ℝ) (hB : 0 < B)
    (M : (Finset (Fin n) → ℝ) → PostedPrice n) (hM : BudgetFeasible B M) :
    ∃ (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ), IsAdditive v ∧ (∀ i, 0 ≤ c i) ∧
      ∃ O : Finset (Fin n), ∑ i ∈ O, c i ≤ B ∧ 0 < v O ∧
        Real.sqrt (n : ℝ) / 2 * v (accepted (run (M v) c)) ≤ v O := by
  have hsq1 : 1 ≤ Real.sqrt (n : ℝ) := by
    rw [Real.one_le_sqrt]; exact_mod_cast hn
  set w : Fin n → ℝ := fun j => if j.val = 0 then Real.sqrt (n : ℝ) else 1 with hw
  have hw0 : ∀ j, 0 < w j := by
    intro j; simp only [hw]; split_ifs <;> linarith
  set v : Finset (Fin n) → ℝ := fun S => ∑ j ∈ S, w j with hvdef
  have hadd : IsAdditive v := ⟨w, fun j => (hw0 j).le, fun S => rfl⟩
  have hmono : ∀ S T : Finset (Fin n), S ⊆ T → v S ≤ v T := fun S T hST =>
    Finset.sum_le_sum_of_subset_of_nonneg hST (fun j _ _ => (hw0 j).le)
  have key : ∀ c : Fin n → ℝ, (∀ j, 0 ≤ c j) → ∑ j ∈ accepted (run (M v) c), c j ≤ B :=
    fun c hc => (valid_sum_le _ c _ (valid_run _ c)).trans (hM v hadd c hc)
  refine ⟨v, ?_⟩
  by_cases h2 : 2 ≤ n
  swap
  · -- n = 1: everything at cost zero, `O` is everybody
    have hn1 : n = 1 := by omega
    refine ⟨fun _ => 0, hadd, fun _ => le_refl _, Finset.univ, by simpa using hB.le, ?_, ?_⟩
    · apply Finset.sum_pos (fun j _ => hw0 j)
      exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    · have hle := hmono _ _ (Finset.subset_univ (accepted (run (M v) fun _ => 0)))
      have hpos : 0 ≤ v (accepted (run (M v) fun _ => 0)) :=
        Finset.sum_nonneg (fun j _ => (hw0 j).le)
      subst hn1
      simp only [Nat.cast_one, Real.sqrt_one]
      linarith
  -- n ≥ 2: the hard instance
  have hb0 : 0 < n := by omega
  set b : Fin n := ⟨0, hb0⟩ with hbdef
  have hwb : w b = Real.sqrt (n : ℝ) := by simp [hw, hbdef]
  have hwj : ∀ j : Fin n, j ≠ b → w j = 1 := by
    intro j hj; simp only [hw]; rw [if_neg]; intro h0; apply hj; exact Fin.ext h0
  have hvb : v {b} = Real.sqrt (n : ℝ) := by simp [hvdef, hwb]
  have hsqpos : 0 < Real.sqrt (n : ℝ) := by linarith
  set m := M v with hm
  set cB : Fin n → ℝ := fun _ => B with hcB
  have hcB0 : ∀ j, 0 ≤ cB j := fun _ => hB.le
  set h := run m cB with hh
  have hvh : Valid m cB h := valid_run m cB
  have hlen : h.length ≤ n := by
    have := (valid_nodup m cB h hvh).length_le_card
    simpa using this
  set P : Offer n → Bool := fun e => decide (e.1 ≠ b ∧ e.2.1 ≤ 0) with hP
  have hsplit : h.takeWhile P ++ h.dropWhile P = h := List.takeWhile_append_dropWhile
  have hpreP : ∀ e ∈ h.takeWhile P, e.1 ≠ b ∧ e.2.1 ≤ 0 := by
    intro e he
    have := List.mem_takeWhile_imp he
    simpa [hP] using this
  rcases hrest : h.dropWhile P with _ | ⟨e, post⟩
  · -- no positive offer, and `b` is never approached: nobody accepts at cost `B`
    rw [hrest, List.append_nil] at hsplit
    have hacc : accepted h = ∅ := by
      ext j
      simp only [Finset.notMem_empty, iff_false]
      rw [mem_accepted]
      rintro ⟨x, hx, hx2, -⟩
      have hd := valid_dec m cB h hvh x hx
      rw [← hsplit] at hx
      have h1 := (hpreP x hx).2
      rw [hx2] at hd
      have := of_decide_eq_true hd.symm
      simp only [hcB] at this
      linarith
    refine ⟨cB, hadd, hcB0, {b}, by simp [hcB], by rw [hvb]; exact hsqpos, ?_⟩
    rw [hacc, hvb]
    simp only [hvdef, Finset.sum_empty, mul_zero]
    exact hsqpos.le
  · rw [hrest] at hsplit
    set pre := h.takeWhile P with hpre
    have hnotPb : P e = false := by
      have aux : ∀ l : List (Offer n), l.dropWhile P = e :: post → P e = false := by
        intro l
        induction l with
        | nil => intro hl; simp at hl
        | cons x xs ih =>
          intro hl
          rw [List.dropWhile_cons] at hl
          split at hl
          · exact ih hl
          · obtain ⟨rfl, rfl⟩ := List.cons.inj hl
            simpa using (by assumption : ¬ P x = true)
      exact aux h hrest
    have hnotP : ¬ (e.1 ≠ b ∧ e.2.1 ≤ 0) := by
      have := hnotPb
      simp only [hP, decide_eq_false_iff_not] at this
      exact this
    have hv' : Valid m cB (pre ++ [e]) := by
      apply valid_append_left m cB (pre ++ [e]) post
      rw [List.append_assoc, List.singleton_append, hsplit]
      exact hvh
    obtain ⟨hvpre, hnext, hnotin, hdec⟩ := valid_snoc_inv m cB pre e hv'
    have hlenpre : pre.length + 1 ≤ n := by
      have := congrArg List.length hsplit
      simp only [List.length_append, List.length_cons] at this
      omega
    have hpredec : ∀ x ∈ pre, x.2.2 = false := by
      intro x hx
      have hd := valid_dec m cB pre hvpre x hx
      rw [hd, decide_eq_false_iff_not]
      have := (hpreP x hx).2
      simp only [hcB]
      linarith
    have newrun : ∀ c' : Fin n → ℝ, (∀ x ∈ pre, 0 < c' x.1) →
        ∃ r, run m c' = pre ++ (e.1, e.2.1, decide (c' e.1 ≤ e.2.1)) :: r := by
      intro c' hc'
      have hvpre' : Valid m c' pre := by
        apply valid_transfer m cB c' pre hvpre
        intro x hx
        rw [hpredec x hx, decide_eq_false_iff_not]
        have := (hpreP x hx).2
        have := hc' x hx
        linarith
      have hvs := Valid.snoc pre e.1 e.2.1 hvpre' hnext hnotin
      obtain ⟨r, hr⟩ := valid_run_eq m c' _ hvs (by simp; omega)
      exact ⟨r, by rw [hr]; simp⟩
    have he_mem : e ∈ h := by rw [← hsplit]; simp
    by_cases heb : e.1 = b
    · by_cases hpB : B ≤ e.2.1
      · -- Case 2: `b` gets the whole budget; the small bidders are cheap
        have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h2
        have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
        set c2 : Fin n → ℝ := fun j => if j = b then B else B / ((n : ℝ) - 1) with hc2
        have hsmall : 0 < B / ((n : ℝ) - 1) := div_pos hB hn1
        have hc2nn : ∀ j, 0 ≤ c2 j := by
          intro j; simp only [hc2]; split_ifs <;> linarith
        obtain ⟨r, hr⟩ := newrun c2 (by
          intro x hx
          have := (hpreP x hx).1
          simp only [hc2, if_neg this]
          exact hsmall)
        have hbacc : b ∈ accepted (run m c2) := by
          rw [mem_accepted, hr]
          refine ⟨(e.1, e.2.1, decide (c2 e.1 ≤ e.2.1)), by simp, ?_, heb⟩
          simp only [hc2, heb, if_true, decide_eq_true_eq]
          exact hpB
        have hsub : accepted (run m c2) ⊆ {b} := by
          intro j hj
          rw [Finset.mem_singleton]
          by_contra hjb
          have h1 := two_le_sum _ c2 hc2nn b j hbacc hj hjb
          have h3 := key c2 hc2nn
          simp only [hc2, if_true, if_neg hjb] at h1
          linarith
        refine ⟨c2, hadd, hc2nn, Finset.univ.erase b, ?_, ?_, ?_⟩
        · have : ∑ i ∈ Finset.univ.erase b, c2 i = ∑ i ∈ Finset.univ.erase b, B / ((n : ℝ) - 1) :=
            Finset.sum_congr rfl (fun j hj => by
              simp only [hc2, if_neg (Finset.ne_of_mem_erase hj)])
          rw [this, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega)]
          rw [Nat.cast_one, mul_div_cancel₀ _ hn1.ne']
        · have : v (Finset.univ.erase b) = ((n : ℝ) - 1) := by
            simp only [hvdef]
            rw [Finset.sum_congr rfl (fun j hj => hwj j (Finset.ne_of_mem_erase hj)),
              Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega)]
            simp
          rw [this]; exact hn1
        · have hvle : v (accepted (run m c2)) ≤ Real.sqrt (n : ℝ) := hvb ▸ hmono _ _ hsub
          have : v (Finset.univ.erase b) = ((n : ℝ) - 1) := by
            simp only [hvdef]
            rw [Finset.sum_congr rfl (fun j hj => hwj j (Finset.ne_of_mem_erase hj)),
              Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega)]
            simp
          rw [this]
          have hss : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = n := Real.mul_self_sqrt (by positivity)
          have := mul_le_mul_of_nonneg_left hvle (by positivity : (0 : ℝ) ≤ Real.sqrt (n : ℝ) / 2)
          nlinarith
      · -- Case 3: `b` is underbid and rejects; at cost `B` at most one small bidder is bought
        rw [not_le] at hpB
        have hbnot : b ∉ accepted h := by
          rw [mem_accepted]
          rintro ⟨x, hx, hx2, hx1⟩
          have hxe : x = e :=
            List.inj_on_of_nodup_map (valid_nodup m cB h hvh) hx he_mem (hx1.trans heb.symm)
          subst hxe
          rw [hdec] at hx2
          have := of_decide_eq_true hx2
          simp only [hcB] at this
          linarith
        have hcard : ((accepted h).card : ℝ) ≤ 1 := by
          have h3 := key cB hcB0
          simp only [hcB, Finset.sum_const, nsmul_eq_mul] at h3
          by_contra hc
          rw [not_le] at hc
          nlinarith
        have hvacc : v (accepted h) = (accepted h).card := by
          simp only [hvdef]
          rw [Finset.sum_congr rfl (fun j hj => hwj j (fun hjb => hbnot (hjb ▸ hj)))]
          simp
        refine ⟨cB, hadd, hcB0, {b}, by simp [hcB], by rw [hvb]; exact hsqpos, ?_⟩
        rw [hvacc, hvb]
        have := mul_le_mul_of_nonneg_left hcard (by positivity : (0 : ℝ) ≤ Real.sqrt (n : ℝ) / 2)
        linarith
    · -- Case 1: the first positive offer goes to a small bidder; make it accept
      have hp : 0 < e.2.1 := by
        by_contra hc
        rw [not_lt] at hc
        exact hnotP ⟨heb, hc⟩
      set c1 : Fin n → ℝ := fun j => if j = e.1 then e.2.1 else B with hc1
      have hc1nn : ∀ j, 0 ≤ c1 j := by
        intro j; simp only [hc1]; split_ifs <;> linarith
      obtain ⟨r, hr⟩ := newrun c1 (by
        intro x hx
        have hx1 : x.1 ≠ e.1 := fun hh => hnotin (hh ▸ List.mem_map_of_mem hx)
        simp only [hc1, if_neg hx1]
        exact hB)
      have hiacc : e.1 ∈ accepted (run m c1) := by
        rw [mem_accepted, hr]
        refine ⟨(e.1, e.2.1, decide (c1 e.1 ≤ e.2.1)), by simp, ?_, rfl⟩
        simp [hc1]
      have hsub : accepted (run m c1) ⊆ {e.1} := by
        intro j hj
        rw [Finset.mem_singleton]
        by_contra hjb
        have h1 := two_le_sum _ c1 hc1nn e.1 j hiacc hj hjb
        have h3 := key c1 hc1nn
        simp only [hc1, if_true, if_neg hjb] at h1
        linarith
      have hvle : v (accepted (run m c1)) ≤ 1 := by
        have := hmono _ _ hsub
        simp only [hvdef, Finset.sum_singleton, hwj _ heb] at this
        exact this
      refine ⟨c1, hadd, hc1nn, {b}, ?_, by rw [hvb]; exact hsqpos, ?_⟩
      · have hbe : b ≠ e.1 := fun hh => heb hh.symm
        simp [hc1, hbe]
      · rw [hvb]
        have := mul_le_mul_of_nonneg_left hvle (by positivity : (0 : ℝ) ≤ Real.sqrt (n : ℝ) / 2)
        linarith
