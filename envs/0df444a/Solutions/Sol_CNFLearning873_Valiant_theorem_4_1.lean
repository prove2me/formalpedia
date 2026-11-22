-- Prove2me | solution 1 for CNFLearning873.Valiant.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-22T21:01:50.407794+00:00
-- url     : https://prove2.me/submissions/4d869e98-4a25-492b-9b3a-58e641aff31a

import Definitions.Def_CNFLearning873_Valiant_Execution
import Theorems.Thm_CNFLearning873_Valiant_lemma_4_3

namespace CNFLearning873.Valiant.Aux
open CNFLearning873.Valiant

variable {n : ℕ}

theorem enum_zero (l : List (Fin n)) : enumerate l 0 = ([[]], 2) := by
  cases l <;> rfl

theorem enum_nil_succ (j : ℕ) : enumerate ([] : List (Fin n)) (j+1) = ([], 1) := rfl

theorem enum_cons_succ (v : Fin n) (vs : List (Fin n)) (j : ℕ) :
    enumerate (v :: vs) (j+1) =
      ((enumerate vs j).1.flatMap (fun c => [(v, true) :: c, (v, false) :: c]) ++ (enumerate vs (j+1)).1,
       (enumerate vs j).2 + (enumerate vs (j+1)).2 + 10 * (enumerate vs j).1.length + 3) := rfl

theorem enum_length (l : List (Fin n)) (j : ℕ) :
    (enumerate l j).1.length = 2 ^ j * l.length.choose j := by
  induction l generalizing j with
  | nil => cases j <;> simp [enum_zero, enum_nil_succ]
  | cons v vs ih =>
    cases j with
    | zero => simp [enum_zero]
    | succ j =>
      rw [enum_cons_succ]
      simp only [List.length_append, List.length_flatMap, List.length_cons, List.length_nil]
      rw [List.map_const', List.sum_replicate, ih, ih, Nat.choose_succ_succ]
      simp only [smul_eq_mul]; ring

/-- invariant of enumerated clauses -/
def Inv (l : List (Fin n)) (j : ℕ) (c : LiteralList n) : Prop :=
  (c.map Prod.fst).Nodup ∧ (∀ p ∈ c, p.1 ∈ l) ∧ c.length = j

theorem enum_inv (l : List (Fin n)) (hl : l.Nodup) (j : ℕ) :
    ∀ c ∈ (enumerate l j).1, Inv l j c := by
  induction l generalizing j with
  | nil =>
    cases j with
    | zero => simp [enum_zero, Inv]
    | succ j => simp [enum_nil_succ]
  | cons v vs ih =>
    have hv : v ∉ vs := (List.nodup_cons.mp hl).1
    have hvs : vs.Nodup := (List.nodup_cons.mp hl).2
    cases j with
    | zero => simp [enum_zero, Inv]
    | succ j =>
      rw [enum_cons_succ]
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · rcases List.mem_flatMap.mp hc with ⟨c', hc', hcc⟩
        obtain ⟨h1, h2, h3⟩ := ih hvs j c' hc'
        have key : ∀ b : Bool, Inv (v :: vs) (j+1) ((v, b) :: c') := by
          intro b
          refine ⟨?_, ?_, by simp [h3]⟩
          · simp only [List.map_cons, List.nodup_cons]
            refine ⟨?_, h1⟩
            intro hm
            rcases List.mem_map.mp hm with ⟨p, hp, hpv⟩
            exact hv (hpv ▸ h2 p hp)
          · intro p hp
            rcases List.mem_cons.mp hp with rfl | hp
            · simp
            · exact List.mem_cons_of_mem _ (h2 p hp)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hcc
        rcases hcc with rfl | rfl <;> exact key _
      · obtain ⟨h1, h2, h3⟩ := ih hvs (j+1) c hc
        exact ⟨h1, fun p hp => List.mem_cons_of_mem _ (h2 p hp), h3⟩


theorem decode_nil : decodeClause ([] : LiteralList n) = fun _ => none := rfl

theorem decode_cons (v : Fin n) (b : Bool) (c : LiteralList n) (w : Fin n) :
    decodeClause ((v, b) :: c) w = if w = v then some b else decodeClause c w := by
  unfold decodeClause
  rw [List.lookup_cons]
  by_cases h : w = v
  · subst h; simp
  · have : (w == v) = false := by simpa using h
    simp [this, h]

theorem decode_none_of_not_mem (c : LiteralList n) (w : Fin n) (hw : w ∉ c.map Prod.fst) :
    decodeClause c w = none := by
  induction c with
  | nil => rfl
  | cons p c ih =>
    obtain ⟨v, b⟩ := p
    rw [decode_cons]
    simp only [List.map_cons, List.mem_cons, not_or] at hw
    rw [if_neg hw.1]; exact ih hw.2

theorem decode_eq_some_iff (c : LiteralList n) (hc : (c.map Prod.fst).Nodup) (w : Fin n) (b : Bool) :
    decodeClause c w = some b ↔ (w, b) ∈ c := by
  induction c with
  | nil => simp [decode_nil]
  | cons p c ih =>
    obtain ⟨v, b'⟩ := p
    simp only [List.map_cons, List.nodup_cons] at hc
    rw [decode_cons]
    by_cases h : w = v
    · subst h
      simp only [if_true, Option.some.injEq, List.mem_cons, Prod.mk.injEq, true_and]
      constructor
      · intro h; exact Or.inl h.symm
      · rintro (h | h)
        · exact h.symm
        · exact absurd (List.mem_map_of_mem (f := Prod.fst) h) hc.1
    · rw [if_neg h, ih hc.2]
      simp [h]

theorem support_decode (c : LiteralList n) :
    support (decodeClause c) = (c.map Prod.fst).toFinset := by
  ext w
  simp only [support, RandomCNFDeficiency.LowerBound.clauseSupport, Finset.mem_filter,
    Finset.mem_univ, true_and, List.mem_toFinset]
  induction c with
  | nil => simp [decode_nil]
  | cons p c ih =>
    obtain ⟨v, b⟩ := p
    rw [decode_cons]
    by_cases h : w = v
    · subst h; simp
    · simp [h, ih]

theorem width_decode (c : LiteralList n) (hc : (c.map Prod.fst).Nodup) :
    width (decodeClause c) = c.length := by
  simp only [width, RandomCNFDeficiency.LowerBound.clauseWidth]
  rw [← support, support_decode, List.toFinset_card_of_nodup hc, List.length_map]

theorem enum_complete (l : List (Fin n)) (hl : l.Nodup) (j : ℕ) (C : Clause n)
    (hs : ∀ w, (C w).isSome → w ∈ l) (hw : width C = j) :
    ∃ c ∈ (enumerate l j).1, decodeClause c = C := by
  induction l generalizing j C with
  | nil =>
    cases j with
    | zero =>
      refine ⟨[], by simp [enum_zero], ?_⟩
      funext w
      cases h : C w with
      | none => rfl
      | some b => exact absurd (hs w (by simp [h])) (by simp)
    | succ j =>
      exfalso
      have : support C = ∅ := by
        ext w; simp only [support, RandomCNFDeficiency.LowerBound.clauseSupport,
          Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro h; exact absurd (hs w h) (by simp)
      simp only [width, RandomCNFDeficiency.LowerBound.clauseWidth] at hw
      rw [← support, this] at hw; simp at hw
  | cons v vs ih =>
    have hv : v ∉ vs := (List.nodup_cons.mp hl).1
    have hvs : vs.Nodup := (List.nodup_cons.mp hl).2
    cases j with
    | zero =>
      refine ⟨[], by simp [enum_zero], ?_⟩
      have : support C = ∅ := by
        simp only [width, RandomCNFDeficiency.LowerBound.clauseWidth] at hw
        exact Finset.card_eq_zero.mp hw
      funext w
      cases h : C w with
      | none => rfl
      | some b =>
        exfalso
        have hm : w ∈ support C := by
          simp [support, RandomCNFDeficiency.LowerBound.clauseSupport, h]
        rw [this] at hm; simp at hm
    | succ j =>
      rw [enum_cons_succ]
      cases hCv : C v with
      | none =>
        obtain ⟨c, hc, hdc⟩ := ih hvs (j+1) C (fun w hw' => by
          rcases List.mem_cons.mp (hs w hw') with rfl | h
          · simp [hCv] at hw'
          · exact h) hw
        exact ⟨c, List.mem_append_right _ hc, hdc⟩
      | some b =>
        set C' : Clause n := Function.update C v none with hC'
        have hsupp : support C = insert v (support C') := by
          ext w
          simp only [support, RandomCNFDeficiency.LowerBound.clauseSupport, Finset.mem_filter,
            Finset.mem_univ, true_and, Finset.mem_insert, hC']
          by_cases h : w = v
          · subst h; simp [hCv]
          · simp [h]
        have hvn : v ∉ support C' := by
          simp [support, RandomCNFDeficiency.LowerBound.clauseSupport, hC']
        have hw' : width C' = j := by
          simp only [width, RandomCNFDeficiency.LowerBound.clauseWidth] at hw ⊢
          rw [← support] at hw ⊢
          rw [hsupp, Finset.card_insert_of_notMem hvn] at hw
          omega
        obtain ⟨c, hc, hdc⟩ := ih hvs j C' (fun w hw2 => by
          have hne : w ≠ v := by rintro rfl; simp [hC'] at hw2
          have : (C w).isSome := by rwa [hC', Function.update_of_ne hne] at hw2
          rcases List.mem_cons.mp (hs w this) with h | h
          · exact absurd h hne
          · exact h) hw'
        refine ⟨(v, b) :: c, List.mem_append_left _ (List.mem_flatMap.mpr ⟨c, hc, by
          cases b <;> simp⟩), ?_⟩
        funext w
        rw [decode_cons, hdc]
        by_cases h : w = v
        · subst h; simp [hCv]
        · simp [h, hC']

theorem enum_nodup (l : List (Fin n)) (hl : l.Nodup) (j : ℕ) :
    ((enumerate l j).1.map decodeClause).Nodup := by
  induction l generalizing j with
  | nil => cases j <;> simp [enum_zero, enum_nil_succ]
  | cons v vs ih =>
    have hv : v ∉ vs := (List.nodup_cons.mp hl).1
    have hvs : vs.Nodup := (List.nodup_cons.mp hl).2
    cases j with
    | zero => simp [enum_zero]
    | succ j =>
      rw [enum_cons_succ, List.map_append, List.nodup_append]
      have hnone : ∀ c ∈ (enumerate vs j).1, decodeClause c v = none := fun c hc =>
        decode_none_of_not_mem c v (fun hm => by
          rcases List.mem_map.mp hm with ⟨p, hp, rfl⟩
          exact hv ((enum_inv vs hvs j c hc).2.1 p hp))
      have hnone' : ∀ c ∈ (enumerate vs (j+1)).1, decodeClause c v = none := fun c hc =>
        decode_none_of_not_mem c v (fun hm => by
          rcases List.mem_map.mp hm with ⟨p, hp, rfl⟩
          exact hv ((enum_inv vs hvs (j+1) c hc).2.1 p hp))
      refine ⟨?_, ih hvs (j+1), ?_⟩
      · rw [List.map_flatMap]
        rw [List.nodup_flatMap]
        refine ⟨?_, ?_⟩
        · intro c hc
          simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
            List.not_mem_nil, or_false, List.nodup_nil, and_true, not_false_eq_true]
          intro h
          have := congrFun h v
          simp [decode_cons] at this
        · have hinj := List.inj_on_of_nodup_map (ih hvs j)
          have hnd : (enumerate vs j).1.Nodup := (ih hvs j).of_map _
          refine hnd.pairwise_of_forall_ne ?_
          intro a ha b hb hab
          simp only [List.map_cons, List.map_nil, Function.onFun]
          rw [List.disjoint_cons_left, List.disjoint_cons_left]
          simp only [List.disjoint_cons_right, List.mem_cons, List.not_mem_nil, or_false,
            List.disjoint_nil_right, and_true, not_or]
          have key : ∀ b1 b2 : Bool, decodeClause ((v, b1) :: a) ≠ decodeClause ((v, b2) :: b) := by
            intro b1 b2 h
            apply hab; apply hinj ha hb
            funext w
            have := congrFun h w
            by_cases hw : w = v
            · subst hw; rw [hnone a ha, hnone b hb]
            · simpa [decode_cons, hw] using this
          and_intros <;> first | exact key _ _ | exact not_false
      · intro x hx y hy hxy
        subst hxy
        rcases List.mem_map.mp hx with ⟨c, hc, rfl⟩
        rcases List.mem_flatMap.mp hc with ⟨c', hc', hcc⟩
        rcases List.mem_map.mp hy with ⟨e, he, hde⟩
        have h1 := congrFun hde v
        rw [hnone' e he] at h1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hcc
        rcases hcc with rfl | rfl <;> simp [decode_cons] at h1

end CNFLearning873.Valiant.Aux

namespace CNFLearning873.Valiant.Aux
open CNFLearning873.Valiant

variable {n : ℕ}

theorem enum_main_length (k : ℕ) :
    (enumerate (List.finRange n) k).1.length = 2 ^ k * n.choose k := by
  rw [enum_length, List.length_finRange]

theorem enum_main_nodup (k : ℕ) :
    ((enumerate (List.finRange n) k).1.map decodeClause).Nodup :=
  enum_nodup _ (List.nodup_finRange n) k

theorem enum_main_toFinset (k : ℕ) :
    ((enumerate (List.finRange n) k).1.map decodeClause).toFinset = candidates n k := by
  ext C
  simp only [List.mem_toFinset, List.mem_map, candidates, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨h1, -, h3⟩ := enum_inv _ (List.nodup_finRange n) k c hc
    rw [width_decode c h1, h3]
  · intro hw
    exact enum_complete _ (List.nodup_finRange n) k C (fun w _ => List.mem_finRange w) hw

/-! semantics of testing -/

theorem testClause_fst (x : Assignment n) (c : LiteralList n) :
    (testClause x c).1 = true ↔ ∃ p ∈ c, x p.1 = p.2 := by
  induction c with
  | nil => simp [testClause]
  | cons p c ih =>
    obtain ⟨v, b⟩ := p
    simp [testClause, ih]

theorem testClause_snd (x : Assignment n) (c : LiteralList n) :
    (testClause x c).2 = 5 * c.length + 1 := by
  induction c with
  | nil => simp [testClause]
  | cons p c ih =>
    obtain ⟨v, b⟩ := p
    simp [testClause, ih]; ring

theorem testSamples_fst {N : ℕ} (xs : Fin N → Assignment n) (c : LiteralList n) (l : List (Fin N)) :
    (testSamples xs c l).1 = true ↔ ∀ i ∈ l, (testClause (xs i) c).1 = true := by
  induction l with
  | nil => simp [testSamples]
  | cons i l ih => simp [testSamples, ih]

theorem testSamples_snd {N : ℕ} (xs : Fin N → Assignment n) (c : LiteralList n) (l : List (Fin N)) :
    (testSamples xs c l).2 = l.length * (5 * c.length + 4) + 1 := by
  induction l with
  | nil => simp [testSamples]
  | cons i l ih => simp [testSamples, ih, testClause_snd]; ring

theorem filter_fst {N : ℕ} (xs : Fin N → Assignment n) (L : List (LiteralList n)) :
    (filterCandidates xs L).1 = L.filter (fun c => (testSamples xs c (List.finRange N)).1) := by
  induction L with
  | nil => simp [filterCandidates]
  | cons c L ih =>
    simp only [filterCandidates, ih, List.filter_cons]

theorem filter_snd_le {N : ℕ} (xs : Fin N → Assignment n) (L : List (LiteralList n)) (k : ℕ)
    (hL : ∀ c ∈ L, c.length = k) :
    (filterCandidates xs L).2 ≤ L.length * (N * (5 * k + 5) + k + 6) + 1 := by
  induction L with
  | nil => simp [filterCandidates]
  | cons c L ih =>
    have hc := hL c (by simp)
    have ih' := ih (fun c' hc' => hL c' (List.mem_cons_of_mem _ hc'))
    simp only [filterCandidates, testSamples_snd, List.length_finRange, hc, List.length_cons]
    have : (if (testSamples xs c (List.finRange N)).1 = true then k + 1 else 0) ≤ k + 1 := by
      split_ifs <;> omega
    nlinarith

theorem sat_decode_iff (x : Assignment n) (c : LiteralList n) (hc : (c.map Prod.fst).Nodup) :
    Sat x (decodeClause c) ↔ ∃ p ∈ c, x p.1 = p.2 := by
  simp only [Sat, RandomCNFDeficiency.LowerBound.SatisfiesClause]
  constructor
  · rintro ⟨i, hi⟩
    rw [decode_eq_some_iff c hc] at hi
    exact ⟨_, hi, rfl⟩
  · rintro ⟨⟨v, b⟩, hp, hx⟩
    refine ⟨v, ?_⟩
    rw [decode_eq_some_iff c hc]
    simp only at hx; rw [hx]; exact hp

theorem decodedOutput_eq {N : ℕ} (k : ℕ) (xs : Fin N → Assignment n) :
    decodedOutput k xs = output k xs := by
  ext C
  simp only [decodedOutput, run, filter_fst, output, Finset.mem_filter, List.mem_toFinset,
    List.mem_map, List.mem_filter]
  rw [← enum_main_toFinset k]
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨c, ⟨hc, ht⟩, rfl⟩
    refine ⟨⟨c, hc, rfl⟩, fun i => ?_⟩
    have h1 := (enum_inv _ (List.nodup_finRange n) k c hc).1
    rw [sat_decode_iff _ _ h1, ← testClause_fst]
    exact (testSamples_fst xs c _).mp ht i (List.mem_finRange i)
  · rintro ⟨⟨c, hc, rfl⟩, hs⟩
    refine ⟨c, ⟨hc, ?_⟩, rfl⟩
    have h1 := (enum_inv _ (List.nodup_finRange n) k c hc).1
    rw [testSamples_fst]
    intro i _
    rw [testClause_fst, ← sat_decode_iff _ _ h1]
    exact hs i

/-! cost of enumeration -/

theorem enum_cost_le (l : List (Fin n)) (j : ℕ) :
    (enumerate l j).2 ≤ 15 * 2 ^ j * (l.length + 1) ^ j := by
  induction l generalizing j with
  | nil =>
    cases j with
    | zero => simp [enum_zero]
    | succ j => simp only [enum_nil_succ]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  | cons v vs ih =>
    cases j with
    | zero => simp [enum_zero]
    | succ j =>
      rw [enum_cons_succ]
      simp only [List.length_cons]
      have h1 := ih j
      have h2 := ih (j+1)
      have h3 := enum_length vs j
      have hch : vs.length.choose j ≤ (vs.length + 1) ^ j :=
        (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) _)
      set m := vs.length
      have hp : (m + 1) ^ j ≤ (m + 1 + 1) ^ j := Nat.pow_le_pow_left (by omega) _
      have hpos : 1 ≤ (m+1)^j := Nat.one_le_pow _ _ (by omega)
      have h2j : 1 ≤ 2^j := Nat.one_le_two_pow
      have key : (m + 1 + 1) ^ (j + 1) ≥ (m + 1) ^ (j + 1) + (m + 1) ^ j := by
        rw [pow_succ, pow_succ]
        nlinarith
      rw [h3]
      calc (enumerate vs j).2 + (enumerate vs (j + 1)).2 + 10 * (2 ^ j * m.choose j) + 3
          ≤ 15 * 2 ^ j * (m + 1) ^ j + 15 * 2 ^ (j+1) * (m + 1) ^ (j+1)
              + 10 * (2 ^ j * (m + 1) ^ j) + 3 * (2 ^ j * (m+1)^j) := by
            have := Nat.mul_le_mul_left (2^j) hch
            have : 1 ≤ 2 ^ j * (m+1)^j := Nat.one_le_iff_ne_zero.mpr (by positivity)
            omega
        _ ≤ 15 * 2 ^ (j + 1) * (m + 1 + 1) ^ (j + 1) := by
            rw [pow_succ 2 j]
            nlinarith

theorem enum_members_length (k : ℕ) :
    ∀ c ∈ (enumerate (List.finRange n) k).1, c.length = k := fun c hc =>
  (enum_inv _ (List.nodup_finRange n) k c hc).2.2

theorem run_cost_le {N : ℕ} (k : ℕ) (hk : 1 ≤ k) (xs : Fin N → Assignment n) (hn : 1 ≤ n) (hN : 1 ≤ N) :
    ((run k xs).2 : ℝ) ≤ (3 + 15 * 4 ^ k + 2 ^ k * (6 * k + 11) : ℝ) * (n : ℝ) ^ k * (N : ℝ) := by
  have hc := enum_cost_le (List.finRange n) k
  rw [List.length_finRange] at hc
  have hf := filter_snd_le xs (enumerate (List.finRange n) k).1 k (enum_members_length k)
  rw [enum_main_length] at hf
  have hch : n.choose k ≤ n ^ k := Nat.choose_le_pow _ _
  have hnk : n ≤ n ^ k := by
    calc n = n ^ 1 := (pow_one n).symm
      _ ≤ n ^ k := Nat.pow_le_pow_right hn hk
  have hn1 : (n + 1) ^ k ≤ (2 * n) ^ k := Nat.pow_le_pow_left (by omega) _
  have hpow : 15 * 2 ^ k * (2 * n) ^ k = 15 * 4 ^ k * n ^ k := by
    rw [mul_pow, show (4:ℕ) = 2 * 2 from rfl, mul_pow]; ring
  have hnkpos : 1 ≤ n ^ k := Nat.one_le_pow _ _ hn
  have hrun : (run k xs).2 ≤ (3 + 15 * 4 ^ k + 2 ^ k * (6 * k + 11)) * n ^ k * N := by
    simp only [run]
    have e1 : (enumerate (List.finRange n) k).2 ≤ 15 * 4 ^ k * n ^ k := by
      calc _ ≤ 15 * 2 ^ k * (n + 1) ^ k := hc
        _ ≤ 15 * 2 ^ k * (2 * n) ^ k := Nat.mul_le_mul_left _ hn1
        _ = _ := hpow
    have e2 : (filterCandidates xs (enumerate (List.finRange n) k).1).2 ≤
        2 ^ k * n ^ k * (N * (6 * k + 11)) + 1 := by
      refine hf.trans ?_
      have : N * (5 * k + 5) + k + 6 ≤ N * (6 * k + 11) := by nlinarith
      have := Nat.mul_le_mul (Nat.mul_le_mul_left (2^k) hch) this
      omega
    have e3 : 15 * 4 ^ k * n ^ k ≤ 15 * 4 ^ k * n ^ k * N := Nat.le_mul_of_pos_right _ hN
    have e4 : n ^ k ≤ n ^ k * N := Nat.le_mul_of_pos_right _ hN
    have e5 : (3 + 15 * 4 ^ k + 2 ^ k * (6 * k + 11)) * n ^ k * N =
        3 * (n ^ k * N) + 15 * 4 ^ k * n ^ k * N + 2 ^ k * n ^ k * (N * (6 * k + 11)) := by ring
    have e6 : 1 ≤ n ^ k * N := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  exact_mod_cast hrun

end CNFLearning873.Valiant.Aux

namespace CNFLearning873.Valiant.Aux
open CNFLearning873.Valiant
open WildeQIT

theorem eventProb_mono {α : Type} [Fintype α] (p : FinDist α) (E E' : α → Prop)
    (h : ∀ x, p.prob x ≠ 0 → E x → E' x) : eventProb p E ≤ eventProb p E' := by
  classical
  unfold eventProb
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : p.prob x = 0
  · simp [hx]
  · by_cases hE : E x
    · simp [hE, h x hx hE]
    · simp only [hE, if_false]; split_ifs <;> [exact p.nonneg x; exact le_rfl]

theorem eventProb_compl {α : Type} [Fintype α] (p : FinDist α) (E : α → Prop) :
    eventProb p E + eventProb p (fun x => ¬ E x) = 1 := by
  classical
  unfold eventProb
  rw [← Finset.sum_add_distrib, ← p.sum_eq_one]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hE : E x <;> simp [hE]

theorem eventProb_nonneg {α : Type} [Fintype α] (p : FinDist α) (E : α → Prop) :
    0 ≤ eventProb p E := by
  classical
  unfold eventProb
  apply Finset.sum_nonneg; intro x _; split_ifs <;> [exact p.nonneg x; exact le_rfl]

theorem eventProb_exists_le {α β : Type} [Fintype α] (p : FinDist α) (S : Finset β)
    (P : β → α → Prop) :
    eventProb p (fun x => ∃ c ∈ S, P c x) ≤ ∑ c ∈ S, eventProb p (P c) := by
  classical
  unfold eventProb
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  by_cases hE : ∃ c ∈ S, P c x
  · obtain ⟨c, hc, hP⟩ := hE
    rw [if_pos ⟨c, hc, hP⟩]
    have : (if P c x then p.prob x else 0) ≤ ∑ c' ∈ S, if P c' x then p.prob x else 0 :=
      Finset.single_le_sum (f := fun c' => if P c' x then p.prob x else 0)
        (fun c' _ => by split_ifs <;> [exact p.nonneg x; exact le_rfl]) hc
    simpa [hP] using this
  · rw [if_neg hE]
    apply Finset.sum_nonneg; intro c _; split_ifs <;> [exact p.nonneg x; exact le_rfl]

theorem eventProb_pi_forall {α : Type} [Fintype α] (p : FinDist α) (N : ℕ) (P : α → Prop) :
    eventProb (RandomQueryXOR.piDist (fun _ : Fin N => p)) (fun xs => ∀ i, P (xs i)) =
      (eventProb p P) ^ N := by
  classical
  unfold eventProb RandomQueryXOR.piDist
  simp only
  rw [← Fin.prod_const, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro xs _
  by_cases h : ∀ i, P (xs i)
  · rw [if_pos h]; apply Finset.prod_congr rfl; intro i _; rw [if_pos (h i)]
  · rw [if_neg h]
    push Not at h
    obtain ⟨i, hi⟩ := h
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem eventProb_uniformOn {α : Type} [Fintype α] [DecidableEq α] (s : Finset α)
    (hs : s.Nonempty) (E : α → Prop) [DecidablePred E] :
    eventProb (RandomQueryXOR.uniformOn s hs) E = ((s.filter E).card : ℝ) / s.card := by
  classical
  unfold eventProb RandomQueryXOR.uniformOn
  simp only
  rw [div_eq_mul_inv, ← Finset.sum_filter]
  have : ∀ x ∈ Finset.univ.filter E, (if x ∈ s then (s.card : ℝ)⁻¹ else 0) =
      if x ∈ s.filter E then (s.card : ℝ)⁻¹ else 0 := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp [hx]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_mem]
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 3
  ext x; simp (config := {contextual := true})

theorem tv_uniformOn_subset {α : Type} [Fintype α] [DecidableEq α] (A B : Finset α)
    (hA : A.Nonempty) (hB : B.Nonempty) (hBA : B ⊆ A) :
    HybridXorLift.tvDist (RandomQueryXOR.uniformOn A hA).prob (RandomQueryXOR.uniformOn B hB).prob
      = ((A \ B).card : ℝ) / A.card := by
  classical
  unfold HybridXorLift.tvDist RandomQueryXOR.uniformOn
  simp only
  have hAc : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hBc : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hle : (B.card : ℝ) ≤ A.card := by exact_mod_cast Finset.card_le_card hBA
  have hdiff : ((A \ B).card : ℝ) = A.card - B.card := by
    rw [Finset.card_sdiff_of_subset hBA]; push_cast [Finset.card_le_card hBA]; ring
  -- split the sum
  have hterm : ∀ x : α, |(if x ∈ A then (A.card : ℝ)⁻¹ else 0) - (if x ∈ B then (B.card : ℝ)⁻¹ else 0)|
      = (if x ∈ B then ((B.card : ℝ)⁻¹ - (A.card : ℝ)⁻¹) else 0) +
        (if x ∈ A \ B then (A.card : ℝ)⁻¹ else 0) := by
    intro x
    have hinv : (A.card : ℝ)⁻¹ ≤ (B.card : ℝ)⁻¹ := inv_anti₀ hBc hle
    by_cases hxB : x ∈ B
    · have hxA : x ∈ A := hBA hxB
      simp [hxA, hxB, abs_of_nonpos (sub_nonpos.mpr hinv)]
    · by_cases hxA : x ∈ A
      · simp [hxA, hxB]
      · simp [hxA, hxB]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem]
  simp only [Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  rw [hdiff]
  field_simp
  ring

end CNFLearning873.Valiant.Aux

namespace CNFLearning873.Valiant.Aux
open CNFLearning873.Valiant
open WildeQIT

theorem candidates_card_le (n k : ℕ) : ((candidates n k).card : ℝ) ≤ (2 * (n : ℝ)) ^ k := by
  rw [← enum_main_toFinset k]
  have h1 := List.toFinset_card_le ((enumerate (List.finRange n) k).1.map decodeClause)
  rw [List.length_map, enum_main_length] at h1
  have h2 : n.choose k ≤ n ^ k := Nat.choose_le_pow _ _
  have : 2 ^ k * n.choose k ≤ (2 * n) ^ k := by rw [mul_pow]; exact Nat.mul_le_mul_left _ h2
  exact_mod_cast h1.trans this

theorem candidates_empty_of_lt {n k : ℕ} (h : n < k) : candidates n k = ∅ := by
  have : (enumerate (List.finRange n) k).1.length = 0 := by
    rw [enum_main_length, Nat.choose_eq_zero_of_lt h]; simp
  rw [List.length_eq_zero_iff] at this
  rw [← enum_main_toFinset k, this]; rfl

theorem sampleLaw_support {n N : ℕ} (F : CNF n) (h : (solutions F).Nonempty)
    (xs : Fin N → Assignment n) (hx : (sampleLaw F h N).prob xs ≠ 0) :
    ∀ i, xs i ∈ solutions F := by
  intro i
  by_contra hi
  apply hx
  unfold sampleLaw RandomQueryXOR.piDist
  simp only
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [solutionLaw, RandomQueryXOR.uniformOn, hi]

theorem sat_of_mem_solutions {n : ℕ} {F : CNF n} {x : Assignment n} (hx : x ∈ solutions F) :
    ∀ c ∈ F, Sat x c := by
  simpa [solutions] using hx

theorem q_add_sat {n : ℕ} (F : CNF n) (h : (solutions F).Nonempty) (c : Clause n) :
    eventProb (solutionLaw F h) (fun x => Sat x c) = 1 - q F h c := by
  have := eventProb_compl (solutionLaw F h) (Violates c)
  unfold q
  have e : (fun x => ¬ Violates c x) = (fun x => Sat x c) := by
    funext x; simp [Violates]
  rw [e] at this; linarith

/-- The core success bound, assuming the conclusion of Lemma 4.3. -/
theorem success_bound {n k N : ℕ} (d : ℕ) (t ε δ : ℝ) (F : CNF n) (hF : KD F k d)
    (h : (solutions F).Nonempty) (hk1 : 1 ≤ k) (hkn : k ≤ n) (hε1 : ε < 1) (hδ : 0 < δ)
    (hτ : 0 < parameterTau n k d t ε)
    (hrare : eventProb (solutionLaw F h) (fun x => ∃ c ∈ rare F h k d t ε, Violates c x) ≤ ε)
    (hN : sampleThreshold n k d t ε δ ≤ (N : ℝ)) :
    1 - δ ≤ eventProb (sampleLaw F h N) (Success F h k ε) := by
  classical
  set τ := parameterTau n k d t ε with hτdef
  let G : (Fin N → Assignment n) → Prop := fun xs =>
    ∀ c ∈ (candidates n k).filter (fun c => τ ≤ q F h c), ∃ i, Violates c (xs i)
  -- Claim A
  have hA : ∀ xs, (sampleLaw F h N).prob xs ≠ 0 → G xs → Success F h k ε xs := by
    intro xs hxs hG
    have hsupp := sampleLaw_support F h xs hxs
    have hFout : F ⊆ output k xs := by
      intro c hc
      simp only [output, Finset.mem_filter, candidates, Finset.mem_univ, true_and]
      exact ⟨hF.1 c hc, fun i => sat_of_mem_solutions (hsupp i) c hc⟩
    have hBA : solutions (output k xs) ⊆ solutions F := by
      intro x hx
      simp only [solutions, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact fun c hc => hx c (hFout hc)
    have hdiff : solutions F \ solutions (output k xs) ⊆
        (solutions F).filter (fun x => ∃ c ∈ rare F h k d t ε, Violates c x) := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      rw [Finset.mem_filter]
      refine ⟨hx.1, ?_⟩
      have : ¬ ∀ c ∈ output k xs, Sat x c := by
        intro hall; apply hx.2
        simp only [solutions, Finset.mem_filter, Finset.mem_univ, true_and]; exact hall
      push Not at this
      obtain ⟨c, hc, hnsat⟩ := this
      simp only [output, Finset.mem_filter] at hc
      refine ⟨c, ?_, hnsat⟩
      simp only [rare, if_neg (not_lt.mpr hkn), Finset.mem_filter]
      refine ⟨hc.1, ?_⟩
      by_contra hge
      push Not at hge
      obtain ⟨i, hi⟩ := hG c (Finset.mem_filter.mpr ⟨hc.1, hge⟩)
      exact hi (hc.2 i)
    have hprob := hrare
    unfold solutionLaw at hprob
    rw [eventProb_uniformOn] at hprob
    have hAc : (0 : ℝ) < (solutions F).card := by exact_mod_cast h.card_pos
    have hratio : (((solutions F \ solutions (output k xs)).card : ℝ)) / (solutions F).card ≤ ε := by
      refine le_trans ?_ hprob
      apply div_le_div_of_nonneg_right _ hAc.le
      exact_mod_cast Finset.card_le_card hdiff
    have hBne : (solutions (output k xs)).Nonempty := by
      by_contra hB
      rw [Finset.not_nonempty_iff_eq_empty] at hB
      rw [hB, Finset.sdiff_empty, div_self hAc.ne'] at hratio
      linarith
    refine ⟨hBne, ?_⟩
    unfold solutionLaw
    rw [tv_uniformOn_subset _ _ h hBne hBA]
    exact hratio
  -- Claim B
  have hB : eventProb (sampleLaw F h N) (fun xs => ¬ G xs) ≤ δ := by
    have e1 : eventProb (sampleLaw F h N) (fun xs => ¬ G xs) ≤
        eventProb (sampleLaw F h N) (fun xs => ∃ c ∈ (candidates n k).filter (fun c => τ ≤ q F h c),
          ∀ i, Sat (xs i) c) := by
      apply eventProb_mono
      intro xs _ hG
      simp only [G, not_forall, not_exists] at hG
      obtain ⟨c, hc, hall⟩ := hG
      exact ⟨c, hc, fun i => by have := hall i; simpa [Violates] using this⟩
    refine e1.trans ((eventProb_exists_le _ _ _).trans ?_)
    have e2 : ∀ c ∈ (candidates n k).filter (fun c => τ ≤ q F h c),
        eventProb (sampleLaw F h N) (fun xs => ∀ i, Sat (xs i) c) ≤ Real.exp (-(τ * N)) := by
      intro c hc
      rw [Finset.mem_filter] at hc
      unfold sampleLaw
      rw [eventProb_pi_forall (solutionLaw F h) N (fun x => Sat x c), q_add_sat]
      have hq1 : 0 ≤ 1 - q F h c := by
        rw [← q_add_sat]; exact eventProb_nonneg _ _
      calc (1 - q F h c) ^ N ≤ (Real.exp (-τ)) ^ N := by
            apply pow_le_pow_left₀ hq1
            have := Real.add_one_le_exp (-q F h c)
            have := Real.exp_le_exp.mpr (neg_le_neg hc.2)
            linarith
        _ = Real.exp (-(τ * N)) := by rw [← Real.exp_nat_mul]; ring_nf
    refine (Finset.sum_le_sum e2).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (((candidates n k).filter (fun c => τ ≤ q F h c)).card : ℝ) ≤ (2 * (n : ℝ)) ^ k :=
      le_trans (by exact_mod_cast Finset.card_filter_le _ _) (candidates_card_le n k)
    have hn : (0 : ℝ) < 2 * n := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      linarith
    have hexp : Real.exp (-(τ * N)) ≤ δ / (2 * (n : ℝ)) ^ k := by
      have hτN : (k : ℝ) * Real.log (2 * n) + Real.log (1 / δ) ≤ τ * N := by
        unfold sampleThreshold at hN
        rw [← hτdef] at hN
        have := mul_le_mul_of_nonneg_left hN hτ.le
        rwa [← mul_assoc, mul_inv_cancel₀ hτ.ne', one_mul] at this
      calc Real.exp (-(τ * N)) ≤ Real.exp (-((k : ℝ) * Real.log (2 * n) + Real.log (1 / δ))) :=
            Real.exp_le_exp.mpr (by linarith)
        _ = δ / (2 * (n : ℝ)) ^ k := by
            rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, ← Real.log_pow,
              Real.exp_log (by positivity), Real.exp_log (by positivity)]
            field_simp
    have hpos : (0 : ℝ) < (2 * (n : ℝ)) ^ k := by positivity
    calc _ ≤ (2 * (n : ℝ)) ^ k * Real.exp (-(τ * N)) :=
          mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
      _ ≤ (2 * (n : ℝ)) ^ k * (δ / (2 * (n : ℝ)) ^ k) := mul_le_mul_of_nonneg_left hexp hpos.le
      _ = δ := by field_simp
  have hG := eventProb_compl (sampleLaw F h N) G
  have hmono : eventProb (sampleLaw F h N) G ≤ eventProb (sampleLaw F h N) (Success F h k ε) :=
    eventProb_mono _ _ _ hA
  linarith

end CNFLearning873.Valiant.Aux

namespace CNFLearning873.Valiant.Aux
open CNFLearning873.Valiant

theorem r_pos (t : ℝ) (ht : 1 ≤ t) : 1 ≤ r t := by
  unfold r; exact Nat.one_le_iff_ne_zero.mpr (by positivity)

/-- the k,d,t-dependent constant `d^r (2k)^{k(1+r)}` -/
noncomputable def K2 (k d : ℕ) (t : ℝ) : ℝ := (d : ℝ) ^ r t * (2 * (k : ℝ)) ^ (k * (1 + r t))

theorem K2_ge_one (k d : ℕ) (t : ℝ) (hk : 1 ≤ k) (hd : 1 ≤ d) : 1 ≤ K2 k d t := by
  unfold K2
  have h1 : (1 : ℝ) ≤ (d : ℝ) ^ r t := one_le_pow₀ (by exact_mod_cast hd)
  have h2 : (1 : ℝ) ≤ (2 * (k : ℝ)) ^ (k * (1 + r t)) :=
    one_le_pow₀ (by have : (1:ℝ) ≤ k := by exact_mod_cast hk
                    linarith)
  nlinarith

theorem A_eq (n k d : ℕ) (t ε : ℝ) : parameterA n k d t ε = K2 k d t * (n : ℝ) ^ r t / ε := rfl

theorem A_gt_one (n k d : ℕ) (t ε : ℝ) (hk : 1 ≤ k) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (hε : 0 < ε) (hε1 : ε < 1) : 1 < parameterA n k d t ε := by
  rw [A_eq, lt_div_iff₀ hε]
  have := K2_ge_one k d t hk hd
  have h3 : (1 : ℝ) ≤ (n : ℝ) ^ r t := one_le_pow₀ (by exact_mod_cast hn)
  nlinarith

theorem M_pos (n k d : ℕ) (t ε : ℝ) (hk : 1 ≤ k) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (hε : 0 < ε) (hε1 : ε < 1) : 0 < parameterM n k d t ε := by
  unfold parameterM
  apply Nat.ceil_pos.mpr
  have := Real.log_pos (A_gt_one n k d t ε hk hd hn hε hε1)
  positivity

theorem lambda_eq (n k d : ℕ) (t ε : ℝ) : parameterLambda n k d t ε =
    ε / (2 * t * K2 k d t * (n : ℝ) ^ r t * (parameterM n k d t ε : ℝ) ^ k) := by
  unfold parameterLambda K2; ring_nf

theorem lambda_pos (n k d : ℕ) (t ε : ℝ) (hk : 1 ≤ k) (hd : 1 ≤ d) (hn : 1 ≤ n) (ht : 1 ≤ t)
    (hε : 0 < ε) (hε1 : ε < 1) : 0 < parameterLambda n k d t ε := by
  rw [lambda_eq]
  have := K2_ge_one k d t hk hd
  have hM : (0 : ℝ) < parameterM n k d t ε := by exact_mod_cast M_pos n k d t ε hk hd hn hε hε1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have : 0 < t := by linarith
  positivity

theorem tau_pos (n k d : ℕ) (t ε : ℝ) (hk : 1 ≤ k) (hd : 1 ≤ d) (hn : 1 ≤ n) (ht : 1 ≤ t)
    (hε : 0 < ε) (hε1 : ε < 1) : 0 < parameterTau n k d t ε := by
  unfold parameterTau
  have := lambda_pos n k d t ε hk hd hn ht hε hε1
  have hM : (0 : ℝ) < parameterM n k d t ε := by exact_mod_cast M_pos n k d t ε hk hd hn hε hε1
  positivity

theorem tau_inv_eq (n k d : ℕ) (t ε : ℝ) (hk : 1 ≤ k) (hd : 1 ≤ d) (hn : 1 ≤ n) (ht : 1 ≤ t)
    (hε : 0 < ε) (hε1 : ε < 1) : (parameterTau n k d t ε)⁻¹ =
    8 * t * K2 k d t * (n : ℝ) ^ r t * (parameterM n k d t ε : ℝ) ^ (k + 1) / ε := by
  unfold parameterTau
  rw [lambda_eq]
  have := K2_ge_one k d t hk hd
  have hM : (0 : ℝ) < parameterM n k d t ε := by exact_mod_cast M_pos n k d t ε hk hd hn hε hε1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have : 0 < t := by linarith
  field_simp
  ring

theorem threshold_pos (n k d : ℕ) (t ε δ : ℝ) (hk : 1 ≤ k) (hd : 1 ≤ d) (hn : 1 ≤ n) (ht : 1 ≤ t)
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1) : 0 < sampleThreshold n k d t ε δ := by
  unfold sampleThreshold
  have := tau_pos n k d t ε hk hd hn ht hε hε1
  have h1 : 0 < Real.log (2 * (n : ℝ)) := Real.log_pos (by
    have : (1:ℝ) ≤ n := by exact_mod_cast hn
    linarith)
  have h2 : 0 < Real.log (1 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  positivity

theorem chosen_spec (n k d : ℕ) (t ε δ : ℝ) (hkn : k ≤ n) :
    1 ≤ chosenSamples n k d t ε δ ∧
      sampleThreshold n k d t ε δ ≤ (chosenSamples n k d t ε δ : ℝ) := by
  unfold chosenSamples
  rw [if_neg (not_lt.mpr hkn)]
  refine ⟨le_max_left _ _, ?_⟩
  calc sampleThreshold n k d t ε δ ≤ (Nat.ceil (sampleThreshold n k d t ε δ) : ℝ) := Nat.le_ceil _
    _ ≤ _ := by exact_mod_cast le_max_right _ _

theorem chosen_le (n k d : ℕ) (t ε δ : ℝ) (hkn : k ≤ n) (hthr : 0 ≤ sampleThreshold n k d t ε δ) :
    (chosenSamples n k d t ε δ : ℝ) ≤ sampleThreshold n k d t ε δ + 1 := by
  unfold chosenSamples
  rw [if_neg (not_lt.mpr hkn)]
  push_cast
  rw [max_le_iff]
  refine ⟨by linarith, (Nat.ceil_lt_add_one hthr).le⟩

theorem one_lt_log_three_le (n : ℕ) (hn : 3 ≤ n) : 1 ≤ Real.log n := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have := Real.exp_one_lt_d9
  have : (3 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- The asymptotic sample bound. -/
theorem chosen_le_scale (n k d : ℕ) (t ε δ : ℝ) (hk : 1 ≤ k) (hd : 1 ≤ d) (ht : 1 ≤ t)
    (hkn : k ≤ n) (hn3 : 3 ≤ n)
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (chosenSamples n k d t ε δ : ℝ) ≤
      (16 * t * k * K2 k d t * (8 ^ k * (Real.log (K2 k d t) + r t) + 1) ^ (k + 1) + 1) *
        sampleScale n k t ε δ := by
  have hn : 1 ≤ n := by omega
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hK2 := K2_ge_one k d t hk hd
  have hlogK2 : 0 ≤ Real.log (K2 k d t) := Real.log_nonneg hK2
  have hr : (1 : ℝ) ≤ r t := by exact_mod_cast r_pos t ht
  have hlogn : 1 ≤ Real.log n := one_lt_log_three_le n hn3
  have hlogε : 0 ≤ Real.log (1 / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
  have hlogδ : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  set L1 := Real.log ((n : ℝ) / ε) with hL1d
  set L2 := Real.log ((n : ℝ) / δ) with hL2d
  have hL1e : L1 = Real.log n + Real.log (1 / ε) := by
    rw [hL1d, div_eq_mul_one_div (n : ℝ), Real.log_mul hnpos.ne' (by positivity)]
  have hL2e : L2 = Real.log n + Real.log (1 / δ) := by
    rw [hL2d, div_eq_mul_one_div (n : ℝ), Real.log_mul hnpos.ne' (by positivity)]
  have hL1 : 1 ≤ L1 := by rw [hL1e]; linarith
  have hL2 : 1 ≤ L2 := by rw [hL2e]; linarith
  set K3 := 8 ^ k * (Real.log (K2 k d t) + r t) + 1 with hK3
  -- bound on log A
  have hlogA : Real.log (parameterA n k d t ε) ≤ (Real.log (K2 k d t) + r t) * L1 := by
    rw [A_eq, div_eq_mul_one_div, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, hL1e]
    nlinarith
  -- bound on M
  have hM : (parameterM n k d t ε : ℝ) ≤ K3 * L1 := by
    unfold parameterM
    have hlogApos := Real.log_pos (A_gt_one n k d t ε hk hd hn hε hε1)
    have h8 : (0:ℝ) < 8 ^ k := by positivity
    calc (Nat.ceil ((8 : ℝ) ^ k * Real.log (parameterA n k d t ε)) : ℝ)
        ≤ (8 : ℝ) ^ k * Real.log (parameterA n k d t ε) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
      _ ≤ (8 : ℝ) ^ k * ((Real.log (K2 k d t) + r t) * L1) + L1 := by
          have := mul_le_mul_of_nonneg_left hlogA h8.le
          linarith
      _ = K3 * L1 := by rw [hK3]; ring
  have hMpos : (0 : ℝ) < parameterM n k d t ε := by exact_mod_cast M_pos n k d t ε hk hd hn hε hε1
  have hMpow : (parameterM n k d t ε : ℝ) ^ (k + 1) ≤ K3 ^ (k + 1) * L1 ^ (k + 1) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hMpos.le hM _
  -- bound on the log factor
  have hlog2n : (k : ℝ) * Real.log (2 * n) + Real.log (1 / δ) ≤ 2 * k * L2 := by
    have : Real.log (2 * (n : ℝ)) ≤ 2 * Real.log n := by
      rw [Real.log_mul (by norm_num) hnpos.ne']
      have : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by
        have : (3:ℝ) ≤ n := by exact_mod_cast hn3
        linarith)
      linarith
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [hL2e]
    nlinarith
  have hthr : sampleThreshold n k d t ε δ ≤
      16 * t * k * K2 k d t * K3 ^ (k + 1) * sampleScale n k t ε δ := by
    unfold sampleThreshold sampleScale
    rw [tau_inv_eq n k d t ε hk hd hn ht hε hε1]
    have hnr : (0 : ℝ) < (n : ℝ) ^ r t := by positivity
    have ht0 : (0 : ℝ) < t := by linarith
    have hlogsum : 0 ≤ (k : ℝ) * Real.log (2 * n) + Real.log (1 / δ) := by
      have : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
      positivity
    have hA : 0 ≤ 8 * t * K2 k d t * (n : ℝ) ^ r t / ε := by positivity
    calc 8 * t * K2 k d t * (n : ℝ) ^ r t * (parameterM n k d t ε : ℝ) ^ (k + 1) / ε *
          ((k : ℝ) * Real.log (2 * n) + Real.log (1 / δ))
        = (8 * t * K2 k d t * (n : ℝ) ^ r t / ε) * (parameterM n k d t ε : ℝ) ^ (k + 1) *
          ((k : ℝ) * Real.log (2 * n) + Real.log (1 / δ)) := by ring
      _ ≤ (8 * t * K2 k d t * (n : ℝ) ^ r t / ε) * (K3 ^ (k + 1) * L1 ^ (k + 1)) * (2 * k * L2) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hMpow hA) hlog2n hlogsum
          positivity
      _ = 16 * t * k * K2 k d t * K3 ^ (k + 1) * ((n : ℝ) ^ r t / ε * L1 ^ (k + 1) * L2) := by ring
  have hscale : 1 ≤ sampleScale n k t ε δ := by
    unfold sampleScale
    have h1 : 1 ≤ (n : ℝ) ^ r t / ε := by
      rw [le_div_iff₀ hε]
      have : (1:ℝ) ≤ (n : ℝ) ^ r t := one_le_pow₀ hn'
      linarith
    have h2 : 1 ≤ L1 ^ (k + 1) := one_le_pow₀ hL1
    have h12 : 1 ≤ (n : ℝ) ^ r t / ε * L1 ^ (k + 1) := one_le_mul_of_one_le_of_one_le h1 h2
    exact one_le_mul_of_one_le_of_one_le h12 hL2
  have hthr0 := (threshold_pos n k d t ε δ hk hd hn ht hε hε1 hδ hδ1).le
  have := chosen_le n k d t ε δ hkn hthr0
  have hpos : 0 ≤ 16 * t * k * K2 k d t * K3 ^ (k + 1) := by
    have : 0 ≤ K3 := by rw [hK3]; positivity
    have : (0:ℝ) ≤ t := by linarith
    positivity
  nlinarith

end CNFLearning873.Valiant.Aux

namespace CNFLearning873.Valiant.Aux
open CNFLearning873.Valiant

theorem width_le {n : ℕ} (c : Clause n) : width c ≤ n := by
  simp only [width, RandomCNFDeficiency.LowerBound.clauseWidth]
  exact (Finset.card_le_univ _).trans (by simp)

theorem eventProb_eq_one {α : Type} [Fintype α] (p : WildeQIT.FinDist α) (E : α → Prop)
    (h : ∀ x, E x) : eventProb p E = 1 := by
  classical
  unfold eventProb
  simp only [h, if_true]; exact p.sum_eq_one

theorem success_small {n k N : ℕ} (F : CNF n) (h : (solutions F).Nonempty) (hF : ∀ c ∈ F, width c = k)
    (hnk : n < k) (ε : ℝ) (hε : 0 < ε) (xs : Fin N → Assignment n) : Success F h k ε xs := by
  classical
  have hF0 : F = ∅ := by
    ext c; simp only [Finset.notMem_empty, iff_false]
    intro hc; have := hF c hc; have := width_le c; omega
  have hout : output k xs = ∅ := by
    unfold output; rw [candidates_empty_of_lt hnk]; rfl
  have hsolF : solutions F = Finset.univ := by
    rw [hF0]; ext x; simp [solutions]
  have hsolO : solutions (output k xs) = Finset.univ := by
    rw [hout]; ext x; simp [solutions]
  have hne : (solutions (output k xs)).Nonempty := by rw [hsolO]; exact ⟨fun _ => true, Finset.mem_univ _⟩
  refine ⟨hne, ?_⟩
  unfold solutionLaw
  have hsub : solutions (output k xs) ⊆ solutions F := by rw [hsolO, hsolF]
  rw [tv_uniformOn_subset (solutions F) (solutions (output k xs)) h hne hsub]
  rw [hsolF, hsolO, Finset.sdiff_self, Finset.card_empty]; simp; exact hε.le

end CNFLearning873.Valiant.Aux

open CNFLearning873.Valiant CNFLearning873.Valiant.Aux in
theorem solution (k d : ℕ) (t : ℝ) (hk : 100 ≤ k) (hd : 1 ≤ d)
    (ht : 1 ≤ t) (hLLL : LLLCondition k d t) :
    ∃ Csample Ctime : ℝ, 0 < Csample ∧ 0 < Ctime ∧
      ∃ n₀ : ℕ, k ≤ n₀ ∧
        (∀ n : ℕ, (enumerate (List.finRange n) k).1.length = 2 ^ k * n.choose k ∧
          ((enumerate (List.finRange n) k).1.map decodeClause).Nodup ∧
          ((enumerate (List.finRange n) k).1.map decodeClause).toFinset = candidates n k) ∧
        (∀ (n N : ℕ) (xs : Fin N → Assignment n), decodedOutput k xs = output k xs) ∧
        (∀ (n N : ℕ) (xs : Fin N → Assignment n), n₀ ≤ n → 1 ≤ N →
          ((run k xs).2 : ℝ) ≤ Ctime * (n : ℝ) ^ k * (N : ℝ)) ∧
        ∀ (n : ℕ) (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 →
          (n < k → chosenSamples n k d t ε δ = 0) ∧
          (k ≤ n → 0 < parameterM n k d t ε ∧
            0 < parameterLambda n k d t ε ∧ 0 < parameterTau n k d t ε ∧
            1 ≤ chosenSamples n k d t ε δ ∧
            sampleThreshold n k d t ε δ ≤ (chosenSamples n k d t ε δ : ℝ)) ∧
          (n₀ ≤ n → (chosenSamples n k d t ε δ : ℝ) ≤
            Csample * sampleScale n k t ε δ) ∧
          ∀ F : CNF n, KD F k d →
            ∃ h : (solutions F).Nonempty,
              (∀ N : ℕ, chosenSamples n k d t ε δ ≤ N →
                1 - δ ≤ eventProb (sampleLaw F h N) (Success F h k ε)) ∧
              (∀ N : ℕ, (n < k ∨ (1 ≤ N ∧ sampleThreshold n k d t ε δ ≤ (N : ℝ))) →
                1 - δ ≤ eventProb (sampleLaw F h N) (Success F h k ε)) := by
  have hk1 : 1 ≤ k := by omega
  have ht0 : (0 : ℝ) < t := by linarith
  have hK2 := K2_ge_one k d t hk1 hd
  have hK3 : (0 : ℝ) ≤ 8 ^ k * (Real.log (K2 k d t) + r t) + 1 := by
    have := Real.log_nonneg hK2
    positivity
  refine ⟨16 * t * k * K2 k d t * (8 ^ k * (Real.log (K2 k d t) + r t) + 1) ^ (k + 1) + 1,
    3 + 15 * 4 ^ k + 2 ^ k * (6 * k + 11), by positivity, by positivity, k, le_rfl,
    fun n => ⟨enum_main_length k, enum_main_nodup k, enum_main_toFinset k⟩,
    fun n N xs => decodedOutput_eq k xs,
    fun n N xs hn hN => run_cost_le k hk1 xs (by omega) hN, ?_⟩
  intro n ε δ hε hε1 hδ hδ1
  refine ⟨fun hnk => by unfold chosenSamples; rw [if_pos hnk], fun hkn => ?_,
    fun hkn => chosen_le_scale n k d t ε δ hk1 hd ht hkn (by omega) hε hε1 hδ hδ1, ?_⟩
  · have hn : 1 ≤ n := by omega
    exact ⟨M_pos n k d t ε hk1 hd hn hε hε1, lambda_pos n k d t ε hk1 hd hn ht hε hε1,
      tau_pos n k d t ε hk1 hd hn ht hε hε1, (chosen_spec n k d t ε δ hkn).1,
      (chosen_spec n k d t ε δ hkn).2⟩
  · intro F hF
    obtain ⟨h, hrare⟩ := lemma_4_3 n k d t ε F hk hd ht hε hε1 hF hLLL
    have key : ∀ N : ℕ, (n < k ∨ (k ≤ n ∧ sampleThreshold n k d t ε δ ≤ (N : ℝ))) →
        1 - δ ≤ eventProb (sampleLaw F h N) (Success F h k ε) := by
      intro N hN
      rcases hN with hnk | ⟨hkn, hthr⟩
      · rw [eventProb_eq_one _ _ (fun xs => success_small F h hF.1 hnk ε hε xs)]
        linarith
      · have hn : 1 ≤ n := by omega
        exact success_bound d t ε δ F hF h hk1 hkn hε1 hδ (tau_pos n k d t ε hk1 hd hn ht hε hε1)
          hrare hthr
    refine ⟨h, fun N hN => ?_, fun N hN => ?_⟩
    · by_cases hnk : n < k
      · exact key N (Or.inl hnk)
      · push Not at hnk
        refine key N (Or.inr ⟨hnk, ?_⟩)
        exact (chosen_spec n k d t ε δ hnk).2.trans (by exact_mod_cast hN)
    · rcases hN with hnk | ⟨_, hthr⟩
      · exact key N (Or.inl hnk)
      · by_cases hnk : n < k
        · exact key N (Or.inl hnk)
        · push Not at hnk
          exact key N (Or.inr ⟨hnk, hthr⟩)
