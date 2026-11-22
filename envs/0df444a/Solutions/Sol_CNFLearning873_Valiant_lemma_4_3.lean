-- Prove2me | solution 1 for CNFLearning873.Valiant.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-22T21:36:41.563853+00:00
-- url     : https://prove2.me/submissions/68d33c8f-2582-45b3-8835-1d4557a00ae1

import Definitions.Def_CNFLearning873_Valiant_Execution
import Theorems.Thm_CNFLearning873_Valiant_observation_4_2

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


namespace CNFLearning873.Valiant.L43
open CNFLearning873.Valiant

variable {n : ℕ}

/-- uniform product probability on assignments -/
noncomputable def pD (E : Assignment n → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter E).card : ℝ) / (2 : ℝ) ^ n

def SatF (L : CNF n) (x : Assignment n) : Prop := ∀ c ∈ L, Sat x c

def DependsOn (E : Assignment n → Prop) (W : Finset (Fin n)) : Prop :=
  ∀ x y : Assignment n, (∀ v ∈ W, x v = y v) → (E x ↔ E y)

theorem pD_eq (E : Assignment n → Prop) [DecidablePred E] :
    pD E = ((Finset.univ.filter E).card : ℝ) / (2 : ℝ) ^ n := by
  unfold pD; congr

theorem card_assign : Fintype.card (Assignment n) = 2 ^ n := by
  simp [Assignment, OAI.FixedClauseThreshold.Assignment]

theorem pD_nonneg (E : Assignment n → Prop) : 0 ≤ pD E := by
  unfold pD; positivity

theorem pD_mono {E E' : Assignment n → Prop} (h : ∀ x, E x → E' x) : pD E ≤ pD E' := by
  classical
  rw [pD_eq, pD_eq]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (fun x hx => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact h x hx)

theorem pD_congr {E E' : Assignment n → Prop} (h : ∀ x, E x ↔ E' x) : pD E = pD E' := by
  have : E = E' := funext fun x => propext (h x)
  rw [this]

theorem pD_true : pD (fun _ : Assignment n => True) = 1 := by
  classical
  rw [pD_eq, Finset.filter_true_of_mem (fun _ _ => trivial), Finset.card_univ, card_assign]
  push_cast; field_simp

theorem pD_le_one (E : Assignment n → Prop) : pD E ≤ 1 :=
  (pD_mono (E' := fun _ => True) (fun _ _ => trivial)).trans pD_true.le

theorem pD_split (E G : Assignment n → Prop) :
    pD E = pD (fun x => E x ∧ G x) + pD (fun x => E x ∧ ¬ G x) := by
  classical
  rw [pD_eq, pD_eq, pD_eq, ← add_div]
  have hset : Finset.univ.filter E = Finset.univ.filter (fun x => E x ∧ G x) ∪
      Finset.univ.filter (fun x => E x ∧ ¬ G x) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]; tauto
  rw [← Nat.cast_add, ← Finset.card_union_of_disjoint, ← hset]
  · rw [Finset.disjoint_filter]; intro x _ h1 h2; exact h2.2 h1.2

/-- mixing two assignments along `W` -/
def mix (W : Finset (Fin n)) (x y : Assignment n) : Assignment n :=
  fun v => if v ∈ W then x v else y v

theorem mix_mix (W : Finset (Fin n)) (x y : Assignment n) :
    mix W (mix W x y) (mix W y x) = x := by
  funext v; unfold mix; split_ifs <;> rfl

theorem pD_indep {E1 E2 : Assignment n → Prop} {W1 W2 : Finset (Fin n)}
    (h1 : DependsOn E1 W1) (h2 : DependsOn E2 W2) (hW : Disjoint W1 W2) :
    pD (fun x => E1 x ∧ E2 x) = pD E1 * pD E2 := by
  classical
  have key : ((Finset.univ.filter E1) ×ˢ (Finset.univ.filter E2)).card =
      ((Finset.univ.filter (fun x => E1 x ∧ E2 x)) ×ˢ (Finset.univ : Finset (Assignment n))).card := by
    apply Finset.card_bij' (fun p _ => (mix W1 p.1 p.2, mix W1 p.2 p.1))
      (fun p _ => (mix W1 p.1 p.2, mix W1 p.2 p.1))
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp ⊢
      exact ⟨(h1 (mix W1 p.1 p.2) p.1 (fun v hv => by simp [mix, hv])).mpr hp.1,
        (h2 (mix W1 p.1 p.2) p.2 (fun v hv => by
          simp [mix, Finset.disjoint_right.mp hW hv])).mpr hp.2⟩
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp ⊢
      exact ⟨(h1 (mix W1 p.1 p.2) p.1 (fun v hv => by simp [mix, hv])).mpr hp.1,
        (h2 (mix W1 p.2 p.1) p.1 (fun v hv => by
          simp [mix, Finset.disjoint_right.mp hW hv])).mpr hp.2⟩
    · intro p _; simp only [mix_mix]
    · intro p _; simp only [mix_mix]
  rw [pD_eq, pD_eq, pD_eq]
  rw [Finset.card_product, Finset.card_product, Finset.card_univ, card_assign] at key
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_mul_div_comm, eq_div_iff (by positivity)]
  have : ((Finset.univ.filter E1).card : ℝ) * (Finset.univ.filter E2).card =
      (Finset.univ.filter (fun x => E1 x ∧ E2 x)).card * 2 ^ n := by exact_mod_cast key
  rw [this]; field_simp

theorem dep_violates (c : Clause n) : DependsOn (Violates c) (support c) := by
  intro x y hxy
  simp only [Violates, Sat, RandomCNFDeficiency.LowerBound.SatisfiesClause]
  apply not_congr
  constructor
  · rintro ⟨i, hi⟩
    have : i ∈ support c := by
      simp [support, RandomCNFDeficiency.LowerBound.clauseSupport, hi]
    exact ⟨i, by rw [hi, hxy i this]⟩
  · rintro ⟨i, hi⟩
    have : i ∈ support c := by
      simp [support, RandomCNFDeficiency.LowerBound.clauseSupport, hi]
    exact ⟨i, by rw [hi, hxy i this]⟩

theorem dep_sat (c : Clause n) : DependsOn (fun x => Sat x c) (support c) := by
  intro x y hxy
  have := dep_violates c x y hxy
  simp only [Violates] at this; tauto

theorem dep_satF (S : CNF n) : DependsOn (SatF S) (S.biUnion support) := by
  intro x y hxy
  simp only [SatF]
  apply forall₂_congr
  intro c hc
  exact dep_sat c x y (fun v hv => hxy v (Finset.mem_biUnion.mpr ⟨c, hc, hv⟩))

theorem dep_mono {E : Assignment n → Prop} {W W' : Finset (Fin n)} (h : DependsOn E W)
    (hW : W ⊆ W') : DependsOn E W' := fun x y hxy => h x y (fun v hv => hxy v (hW hv))

/-! ### the local lemma -/

noncomputable def nbr (L : CNF n) (c : Clause n) : CNF n := by
  classical
  exact L.filter (fun c' => c' ≠ c ∧ ¬ Disjoint (support c) (support c'))

def LLLHyp (L : CNF n) (x : Clause n → ℝ) : Prop :=
  (∀ c ∈ L, 0 ≤ x c ∧ x c < 1) ∧
    ∀ c ∈ L, pD (Violates c) ≤ x c * ∏ c' ∈ nbr L c, (1 - x c')

theorem satF_insert (S : CNF n) (c : Clause n) (x : Assignment n) :
    SatF (insert c S) x ↔ Sat x c ∧ SatF S x := by
  classical
  simp [SatF, Finset.forall_mem_insert]

theorem satF_union (S T : CNF n) (x : Assignment n) :
    SatF (S ∪ T) x ↔ SatF S x ∧ SatF T x := by
  classical
  simp only [SatF, Finset.mem_union]
  constructor
  · intro h; exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩
  · rintro ⟨h1, h2⟩ c (hc | hc); exacts [h1 c hc, h2 c hc]

theorem satF_empty (x : Assignment n) : SatF (∅ : CNF n) x := by simp [SatF]

/-- removing one clause: `pD (Sat (insert c S)) = pD (Sat S) - pD (Viol c ∧ Sat S)` -/
theorem pD_insert (S : CNF n) (c : Clause n) :
    pD (SatF (insert c S)) = pD (SatF S) - pD (fun x => Violates c x ∧ SatF S x) := by
  have := pD_split (SatF S) (fun x => Sat x c)
  rw [pD_congr (E := SatF (insert c S)) (E' := fun x => SatF S x ∧ Sat x c)
    (fun x => by rw [satF_insert]; tauto)]
  rw [pD_congr (E := fun x => Violates c x ∧ SatF S x) (E' := fun x => SatF S x ∧ ¬ Sat x c)
    (fun x => by simp only [Violates]; tauto)]
  linarith

section LLL
variable (L : CNF n) (x : Clause n → ℝ)

/-- one-step statement at a given set -/
def Step (S : CNF n) : Prop :=
  ∀ c ∈ L, c ∉ S → pD (fun y => Violates c y ∧ SatF S y) ≤ x c * pD (SatF S)

theorem extend_bound (hx : LLLHyp L x) (N : ℕ)
    (ih : ∀ S ⊆ L, S.card < N → Step L x S) :
    ∀ (T S : CNF n), S ⊆ L → T ⊆ L → Disjoint S T → (S ∪ T).card ≤ N →
      pD (SatF S) * ∏ c ∈ T, (1 - x c) ≤ pD (SatF (S ∪ T)) := by
  classical
  intro T
  induction T using Finset.induction_on with
  | empty => intro S _ _ _ _; simp
  | insert c T hcT ihT =>
    intro S hS hT hST hcard
    have hcL : c ∈ L := hT (Finset.mem_insert_self c T)
    have hTL : T ⊆ L := fun y hy => hT (Finset.mem_insert_of_mem hy)
    have hST' : Disjoint S T := Finset.disjoint_of_subset_right (Finset.subset_insert _ _) hST
    have hcS : c ∉ S := fun h => Finset.disjoint_left.mp hST h (Finset.mem_insert_self c T)
    have hcard' : (S ∪ T).card < N := by
      have : (S ∪ T).card < (S ∪ insert c T).card := by
        apply Finset.card_lt_card
        rw [Finset.union_insert]
        exact Finset.ssubset_insert (by simp [hcS, hcT])
      omega
    have h1 := ihT S hS hTL hST' hcard'.le
    have hstep := ih (S ∪ T) (Finset.union_subset hS hTL) hcard' c hcL (by simp [hcS, hcT])
    rw [Finset.prod_insert hcT, Finset.union_insert, pD_insert]
    have hxc := hx.1 c hcL
    have hprod : 0 ≤ ∏ c ∈ T, (1 - x c) :=
      Finset.prod_nonneg (fun y hy => by have := hx.1 y (hTL hy); linarith)
    nlinarith [pD_nonneg (SatF S)]

theorem step_all (hx : LLLHyp L x) : ∀ N, ∀ S ⊆ L, S.card < N → Step L x S := by
  classical
  intro N
  induction N with
  | zero => intro S _ h; omega
  | succ N ih =>
    intro S hS hcard c hc hcS
    set S1 := S.filter (fun c' => ¬ Disjoint (support c) (support c'))
    set S2 := S.filter (fun c' => Disjoint (support c) (support c'))
    have hS12 : S2 ∪ S1 = S := by
      ext y; simp only [S1, S2, Finset.mem_union, Finset.mem_filter]; tauto
    have hdisj : Disjoint S2 S1 := by
      rw [Finset.disjoint_filter]; intro y _ h1 h2; exact h2 h1
    have hS2L : S2 ⊆ L := (Finset.filter_subset _ _).trans hS
    have hS1L : S1 ⊆ L := (Finset.filter_subset _ _).trans hS
    -- extension bound
    have hext := extend_bound L x hx N (fun S' hS' hc' => ih S' hS' hc') S1 S2 hS2L hS1L hdisj
      (by rw [hS12]; omega)
    rw [hS12] at hext
    -- independence
    have hind : pD (fun y => Violates c y ∧ SatF S2 y) = pD (Violates c) * pD (SatF S2) := by
      apply pD_indep (dep_violates c) (dep_satF S2)
      rw [Finset.disjoint_biUnion_right]
      intro c' hc'
      exact (Finset.mem_filter.mp hc').2
    have hmono : pD (fun y => Violates c y ∧ SatF S y) ≤ pD (fun y => Violates c y ∧ SatF S2 y) :=
      pD_mono (fun y hy => ⟨hy.1, fun c' hc' => hy.2 c' ((Finset.filter_subset _ _) hc')⟩)
    have hS1nbr : S1 ⊆ nbr L c := by
      intro c' hc'
      simp only [S1, Finset.mem_filter] at hc'
      simp only [nbr, Finset.mem_filter]
      exact ⟨hS hc'.1, fun h => hcS (h ▸ hc'.1), hc'.2⟩
    have hprod : ∏ c' ∈ nbr L c, (1 - x c') ≤ ∏ c' ∈ S1, (1 - x c') := by
      rw [← Finset.prod_sdiff hS1nbr]
      have h1 : ∏ c' ∈ nbr L c \ S1, (1 - x c') ≤ 1 := by
        apply Finset.prod_le_one
        · intro i hi
          have := hx.1 i ((Finset.filter_subset _ _) (Finset.sdiff_subset hi)); linarith
        · intro i hi
          have := hx.1 i ((Finset.filter_subset _ _) (Finset.sdiff_subset hi)); linarith
      have h2 : 0 ≤ ∏ c' ∈ S1, (1 - x c') :=
        Finset.prod_nonneg (fun i hi => by have := hx.1 i (hS1L hi); linarith)
      nlinarith
    have hprodnn : 0 ≤ ∏ c' ∈ nbr L c, (1 - x c') :=
      Finset.prod_nonneg (fun i hi => by
        have := hx.1 i ((Finset.filter_subset _ _) hi); linarith)
    have hll := hx.2 c hc
    have hxc := (hx.1 c hc).1
    calc pD (fun y => Violates c y ∧ SatF S y) ≤ pD (Violates c) * pD (SatF S2) := hind ▸ hmono
      _ ≤ (x c * ∏ c' ∈ nbr L c, (1 - x c')) * pD (SatF S2) :=
          mul_le_mul_of_nonneg_right hll (pD_nonneg _)
      _ ≤ (x c * ∏ c' ∈ S1, (1 - x c')) * pD (SatF S2) := by
          apply mul_le_mul_of_nonneg_right _ (pD_nonneg _)
          exact mul_le_mul_of_nonneg_left hprod hxc
      _ = x c * (pD (SatF S2) * ∏ c' ∈ S1, (1 - x c')) := by ring
      _ ≤ x c * pD (SatF S) := mul_le_mul_of_nonneg_left hext hxc

/-- (a) of the local lemma: the probability that all clauses are satisfied is at least
`∏ (1 - x c)`. -/
theorem lll_lower (hx : LLLHyp L x) : ∏ c ∈ L, (1 - x c) ≤ pD (SatF L) := by
  classical
  have := extend_bound L x hx (L.card + 1) (fun S hS hc => step_all L x hx (L.card + 1) S hS hc)
    L ∅ (Finset.empty_subset _) le_rfl (Finset.disjoint_empty_left _) (by simp)
  simp only [Finset.empty_union] at this
  rw [pD_congr (E := SatF ∅) (E' := fun _ => True) (fun y => by simp [satF_empty]), pD_true,
    one_mul] at this
  exact this

theorem lll_pos (hx : LLLHyp L x) : 0 < pD (SatF L) := by
  refine lt_of_lt_of_le ?_ (lll_lower L x hx)
  apply Finset.prod_pos
  intro c hc; have := hx.1 c hc; linarith

/-- (b) of the local lemma: conditional bound for an event depending on `W`. -/
theorem lll_cond (hx : LLLHyp L x) (E : Assignment n → Prop) (W : Finset (Fin n))
    (hE : DependsOn E W) :
    pD (fun y => E y ∧ SatF L y) ≤
      pD E * pD (SatF L) * (∏ c ∈ L.filter (fun c => ¬ Disjoint (support c) W), (1 - x c))⁻¹ := by
  classical
  set G := L.filter (fun c => ¬ Disjoint (support c) W)
  set L2 := L.filter (fun c => Disjoint (support c) W)
  have hL : L2 ∪ G = L := by
    ext y; simp only [G, L2, Finset.mem_union, Finset.mem_filter]; tauto
  have hdisj : Disjoint L2 G := by
    rw [Finset.disjoint_filter]; intro y _ h1 h2; exact h2 h1
  have hext := extend_bound L x hx (L.card + 1)
    (fun S hS hc => step_all L x hx (L.card + 1) S hS hc) G L2
    (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdisj (by rw [hL]; omega)
  rw [hL] at hext
  have hind : pD (fun y => E y ∧ SatF L2 y) = pD E * pD (SatF L2) := by
    apply pD_indep hE (dep_satF L2)
    rw [Finset.disjoint_biUnion_right]
    intro c hc
    exact (Finset.mem_filter.mp hc).2.symm
  have hmono : pD (fun y => E y ∧ SatF L y) ≤ pD (fun y => E y ∧ SatF L2 y) :=
    pD_mono (fun y hy => ⟨hy.1, fun c hc => hy.2 c ((Finset.filter_subset _ _) hc)⟩)
  have hGpos : 0 < ∏ c ∈ G, (1 - x c) :=
    Finset.prod_pos (fun c hc => by have := hx.1 c ((Finset.filter_subset _ _) hc); linarith)
  have : pD (SatF L2) ≤ pD (SatF L) * (∏ c ∈ G, (1 - x c))⁻¹ := by
    rw [le_mul_inv_iff₀ hGpos]; exact hext
  calc pD (fun y => E y ∧ SatF L y) ≤ pD E * pD (SatF L2) := hind ▸ hmono
    _ ≤ pD E * (pD (SatF L) * (∏ c ∈ G, (1 - x c))⁻¹) :=
        mul_le_mul_of_nonneg_left this (pD_nonneg _)
    _ = _ := by ring

end LLL

end CNFLearning873.Valiant.L43


namespace CNFLearning873.Valiant.L43
open CNFLearning873.Valiant

variable {n : ℕ}

theorem mem_support {c : Clause n} {v : Fin n} : v ∈ support c ↔ (c v).isSome := by
  simp [support, RandomCNFDeficiency.LowerBound.clauseSupport]

theorem not_mem_support {c : Clause n} {v : Fin n} : v ∉ support c ↔ c v = none := by
  rw [mem_support]; cases c v <;> simp

theorem width_eq (c : Clause n) : width c = (support c).card := rfl

open Classical in
theorem solutions_eq (F : CNF n) : solutions F = Finset.univ.filter (SatF F) := by
  ext x; simp only [solutions, SatF, Finset.mem_filter, Finset.mem_univ, true_and]

theorem card_solutions (F : CNF n) :
    ((solutions F).card : ℝ) = pD (SatF F) * 2 ^ n := by
  classical
  rw [pD_eq, solutions_eq]; field_simp

theorem nonempty_of_pD (F : CNF n) (h : 0 < pD (SatF F)) : (solutions F).Nonempty := by
  have := card_solutions F
  rw [← Finset.card_pos]
  have : (0 : ℝ) < (solutions F).card := by rw [this]; positivity
  exact_mod_cast this

theorem pD_pos_of_nonempty (F : CNF n) (h : (solutions F).Nonempty) : 0 < pD (SatF F) := by
  have h1 := card_solutions F
  have h2 : (0 : ℝ) < (solutions F).card := by exact_mod_cast h.card_pos
  rw [h1] at h2
  exact pos_of_mul_pos_left h2 (by positivity)

/-- the solution law expressed through the uniform product measure -/
theorem eventProb_eq (F : CNF n) (h : (solutions F).Nonempty) (E : Assignment n → Prop) :
    eventProb (solutionLaw F h) E = pD (fun x => E x ∧ SatF F x) / pD (SatF F) := by
  classical
  unfold solutionLaw
  rw [Aux.eventProb_uniformOn, pD_eq, pD_eq]
  have : (2 : ℝ) ^ n ≠ 0 := by positivity
  rw [div_div_div_cancel_right₀ this]
  have e1 : (solutions F).filter E = Finset.univ.filter (fun x => E x ∧ SatF F x) := by
    ext x; rw [Finset.mem_filter, Finset.mem_filter]; simp [solutions, SatF, and_comm]
  have e2 : solutions F = Finset.univ.filter (SatF F) := by
    ext x; simp only [solutions, SatF, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [e1, e2]

/-! violation probability of a clause -/

theorem violates_iff (c : Clause n) (x : Assignment n) :
    Violates c x ↔ ∀ v b, c v = some b → x v = !b := by
  show (¬ ∃ i, c i = some (x i)) ↔ _
  rw [not_exists]
  constructor
  · intro h v b hv
    have h1 : c v ≠ some (x v) := h v
    rw [hv] at h1
    have h2 : b ≠ x v := fun e => h1 (by rw [e])
    revert h2; cases x v <;> cases b <;> decide
  · intro h v hv
    have := h v (x v) hv
    revert this; cases x v <;> decide

theorem pD_violates (c : Clause n) : pD (Violates c) = ((2 : ℝ) ^ width c)⁻¹ := by
  classical
  rw [pD_eq]
  set s := support c
  have hcard : (Finset.univ.filter (Violates c)).card = 2 ^ (n - s.card) := by
    have e : {x : Assignment n // Violates c x} ≃ ({v : Fin n // v ∉ s} → Bool) :=
      { toFun := fun x v => x.1 v.1
        invFun := fun g => ⟨fun v => if h : v ∈ s then !((c v).get (mem_support.mp h)) else g ⟨v, h⟩,
          by
            rw [violates_iff]
            intro v b hv
            have hvs : v ∈ s := mem_support.mpr (by simp [hv])
            simp [hvs, hv]⟩
        left_inv := by
          intro x
          apply Subtype.ext
          funext v
          by_cases hv : v ∈ s
          · simp only [hv, dite_true]
            have hs := mem_support.mp hv
            obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hs
            have := (violates_iff c x.1).mp x.2 v b hb
            simp [hb, this]
          · simp [hv]
        right_inv := by
          intro g; funext v; simp [v.2] }
    rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
  rw [hcard, width_eq]
  have hle : s.card ≤ n := (Finset.card_le_univ _).trans (by simp)
  rw [Nat.cast_pow, Nat.cast_ofNat, div_eq_iff (by positivity),
    eq_inv_mul_iff_mul_eq₀ (by positivity), ← pow_add, Nat.add_sub_cancel' hle]

/-! counting clauses meeting a variable set -/

theorem card_meeting_le (L : CNF n) (d : ℕ) (hL : DegreeBound L d) (W : Finset (Fin n)) :
    (L.filter (fun c => ¬ Disjoint (support c) W)).card ≤ d * W.card := by
  classical
  have hsub : L.filter (fun c => ¬ Disjoint (support c) W) ⊆
      W.biUnion (fun v => L.filter (fun c => v ∈ support c)) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.not_disjoint_iff] at hc
    obtain ⟨hcL, v, hv1, hv2⟩ := hc
    exact Finset.mem_biUnion.mpr ⟨v, hv2, Finset.mem_filter.mpr ⟨hcL, hv1⟩⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ W, (L.filter (fun c => v ∈ support c)).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ W, d := Finset.sum_le_sum (fun v _ => hL v)
    _ = d * W.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- product of `1 - x` over a family on which `x` is a constant -/
theorem prod_const_ge (G : CNF n) (x : Clause n → ℝ) (x0 : ℝ) (m : ℕ)
    (hx : ∀ c ∈ G, x c = x0) (h0 : 0 ≤ x0) (h1 : x0 ≤ 1) (hG : G.card ≤ m) :
    (1 - x0) ^ m ≤ ∏ c ∈ G, (1 - x c) := by
  rw [Finset.prod_congr rfl (fun c hc => by rw [hx c hc]), Finset.prod_const]
  exact pow_le_pow_of_le_one (by linarith) (by linarith) hG

theorem bernoulli (x0 : ℝ) (m : ℕ) (h0 : 0 ≤ x0) (h1 : x0 ≤ 1) : 1 - m * x0 ≤ (1 - x0) ^ m := by
  have := one_add_mul_le_pow (a := -x0) (by linarith) m
  have e1 : (1 : ℝ) + m * -x0 = 1 - m * x0 := by ring
  have e2 : (1 : ℝ) + -x0 = 1 - x0 := by ring
  rw [e1, e2] at this; exact this

theorem lllHyp_mono (L L' : CNF n) (x : Clause n → ℝ) (hx : LLLHyp L x) (hL : L' ⊆ L) :
    LLLHyp L' x := by
  classical
  refine ⟨fun c hc => hx.1 c (hL hc), fun c hc => (hx.2 c (hL hc)).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (hx.1 c (hL hc)).1
  have hsub : nbr L' c ⊆ nbr L c := by
    intro c' hc'; simp only [nbr, Finset.mem_filter] at hc' ⊢; exact ⟨hL hc'.1, hc'.2⟩
  rw [← Finset.prod_sdiff hsub]
  have h1 : ∏ c' ∈ nbr L c \ nbr L' c, (1 - x c') ≤ 1 := by
    apply Finset.prod_le_one
    · intro i hi
      have := hx.1 i ((Finset.filter_subset _ _) (Finset.sdiff_subset hi)); linarith
    · intro i hi
      have := hx.1 i ((Finset.filter_subset _ _) (Finset.sdiff_subset hi)); linarith
  have h2 : 0 ≤ ∏ c' ∈ nbr L' c, (1 - x c') :=
    Finset.prod_nonneg (fun i hi => by
      have := hx.1 i (hL ((Finset.filter_subset _ _) hi)); linarith)
  nlinarith

/-- nbr of `c` is contained in the family meeting `support c` -/
theorem nbr_subset (L : CNF n) (c : Clause n) :
    nbr L c ⊆ L.filter (fun c' => ¬ Disjoint (support c') (support c)) := by
  intro c' hc'
  simp only [nbr, Finset.mem_filter] at hc' ⊢
  exact ⟨hc'.1, fun h => hc'.2.2 h.symm⟩

end CNFLearning873.Valiant.L43


namespace CNFLearning873.Valiant.L43
open CNFLearning873.Valiant

/-! ### consequences of Observation 4.2 -/

theorem est_i (k d : ℕ) (t : ℝ) (hk : 100 ≤ k) (hd : 1 ≤ d) (ht : 1 ≤ t)
    (hLLL : LLLCondition k d t) : 64 * (d : ℝ) * (k : ℝ) ^ 2 < (2 : ℝ) ^ k := by
  obtain ⟨h1, -, -⟩ := observation_4_2 k d t hk hd ht hLLL
  unfold log₂ at h1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hkpos : (0 : ℝ) < k := by
    have : (100:ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have h2 : Real.log ((d : ℝ) * k) + Real.log k + 6 * Real.log 2 < k * Real.log 2 := by
    have := mul_lt_mul_of_pos_right h1 hl2
    rw [sub_mul, sub_mul, div_mul_cancel₀ _ hl2.ne', div_mul_cancel₀ _ hl2.ne'] at this
    linarith
  have h3 : Real.log (64 * (d : ℝ) * (k : ℝ) ^ 2) < Real.log ((2 : ℝ) ^ k) := by
    rw [Real.log_pow, show (64 : ℝ) * d * k ^ 2 = ((d : ℝ) * k) * k * 2 ^ 6 by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow]
    push_cast; linarith
  exact (Real.log_lt_log_iff (by positivity) (by positivity)).mp h3

theorem est_iii (k d : ℕ) (t : ℝ) (hk : 100 ≤ k) (hd : 1 ≤ d) (ht : 1 ≤ t)
    (hLLL : LLLCondition k d t) :
    (d : ℝ) * k * (2 : ℝ) ^ (-((k : ℝ) * t / (1 + t))) ≤ 1 / 8 := by
  obtain ⟨-, -, h3⟩ := observation_4_2 k d t hk hd ht hLLL
  rw [Real.rpow_sub (by norm_num), Real.rpow_one] at h3
  rw [Real.rpow_neg (by norm_num)]
  have : (d : ℝ) * k * (2 / (2 : ℝ) ^ ((k : ℝ) * t / (1 + t))) =
      2 * ((d : ℝ) * k * ((2 : ℝ) ^ ((k : ℝ) * t / (1 + t)))⁻¹) := by ring
  rw [this] at h3; linarith

/-! ### parameter estimates -/

theorem K2_ge (k d : ℕ) (t : ℝ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    (2 * (k : ℝ)) ^ (k * (1 + r t)) ≤ (d : ℝ) ^ r t * (2 * (k : ℝ)) ^ (k * (1 + r t)) := by
  have : (1 : ℝ) ≤ (d : ℝ) ^ r t := one_le_pow₀ (by exact_mod_cast hd)
  have : (0 : ℝ) ≤ (2 * (k : ℝ)) ^ (k * (1 + r t)) := by positivity
  nlinarith

theorem A_ge (n k d : ℕ) (t ε : ℝ) (hk : 1 ≤ k) (hd : 1 ≤ d) (hn : 1 ≤ n) (hε : 0 < ε)
    (hε1 : ε < 1) : (2 * (k : ℝ)) ^ (k * (1 + r t)) ≤ parameterA n k d t ε := by
  unfold parameterA
  rw [le_div_iff₀ hε]
  have h1 := K2_ge k d t hk hd
  have h2 : (1 : ℝ) ≤ (n : ℝ) ^ r t := one_le_pow₀ (by exact_mod_cast hn)
  have h3 : (0 : ℝ) ≤ (2 * (k : ℝ)) ^ (k * (1 + r t)) := by positivity
  nlinarith

theorem logA_ge_one (n k d : ℕ) (t ε : ℝ) (hk : 100 ≤ k) (hd : 1 ≤ d) (hn : 1 ≤ n) (hε : 0 < ε)
    (hε1 : ε < 1) : 1 ≤ Real.log (parameterA n k d t ε) := by
  have hA := A_ge n k d t ε (by omega) hd hn hε hε1
  have hk' : (100 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : (2 * (k : ℝ)) ≤ (2 * (k : ℝ)) ^ (k * (1 + r t)) := by
    apply le_self_pow₀ (by linarith)
    have : 1 ≤ k * (1 + r t) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

theorem four_t_le_A (n k d : ℕ) (t ε : ℝ) (hk : 100 ≤ k) (hd : 1 ≤ d) (hn : 1 ≤ n) (ht : 1 ≤ t)
    (hε : 0 < ε) (hε1 : ε < 1) : 4 * t ≤ parameterA n k d t ε := by
  have hA := A_ge n k d t ε (by omega) hd hn hε hε1
  have hk' : (100 : ℝ) ≤ k := by exact_mod_cast hk
  have htr : t ≤ (r t : ℝ) := Nat.le_ceil t
  have h1 : (2 * (k : ℝ)) ^ (1 + r t) ≤ (2 * (k : ℝ)) ^ (k * (1 + r t)) := by
    apply pow_le_pow_right₀ (by linarith)
    have : 1 ≤ k := by omega
    nlinarith
  have h2 : 1 + (r t : ℝ) * 199 ≤ (1 + 199 : ℝ) ^ r t := one_add_mul_le_pow (by norm_num) _
  have h3 : (200 : ℝ) ^ r t ≤ (2 * (k : ℝ)) ^ r t := pow_le_pow_left₀ (by norm_num) (by linarith) _
  have h4 : (2 * (k : ℝ)) ^ (1 + r t) = 2 * k * (2 * (k : ℝ)) ^ r t := by ring
  have hr0 : (0 : ℝ) ≤ r t := by positivity
  norm_num at h2
  nlinarith

theorem M_ge (n k d : ℕ) (t ε : ℝ) :
    (8 : ℝ) ^ k * Real.log (parameterA n k d t ε) ≤ parameterM n k d t ε := by
  unfold parameterM; exact Nat.le_ceil _

theorem M_le (n k d : ℕ) (t ε : ℝ) (hL : 0 ≤ Real.log (parameterA n k d t ε)) :
    (parameterM n k d t ε : ℝ) ≤ (8 : ℝ) ^ k * (Real.log (parameterA n k d t ε) + 1) := by
  unfold parameterM
  have := (Nat.ceil_lt_add_one (show 0 ≤ (8 : ℝ) ^ k * Real.log (parameterA n k d t ε) by positivity)).le
  have h8 : (1 : ℝ) ≤ 8 ^ k := one_le_pow₀ (by norm_num)
  nlinarith

theorem two_div_lambda (n k d : ℕ) (t ε : ℝ) (hk : 1 ≤ k) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (ht : 1 ≤ t) (hε : 0 < ε) (hε1 : ε < 1) :
    2 / parameterLambda n k d t ε =
      4 * t * parameterA n k d t ε * (parameterM n k d t ε : ℝ) ^ k := by
  unfold parameterLambda parameterA
  have hM : (0 : ℝ) < parameterM n k d t ε := by exact_mod_cast Aux.M_pos n k d t ε hk hd hn hε hε1
  have : (0 : ℝ) < t := by linarith
  have : (0 : ℝ) < d := by exact_mod_cast hd
  have : (0 : ℝ) < k := by exact_mod_cast hk
  have : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp
  norm_num

theorem log_two_div_lambda (n k d : ℕ) (t ε : ℝ) (hk : 100 ≤ k) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (ht : 1 ≤ t) (hε : 0 < ε) (hε1 : ε < 1) :
    Real.log (2 / parameterLambda n k d t ε) ≤
      4 * (k : ℝ) ^ 2 * Real.log (parameterA n k d t ε) := by
  have hL := logA_ge_one n k d t ε hk hd hn hε hε1
  have hA := four_t_le_A n k d t ε hk hd hn ht hε hε1
  have hk1 : 1 ≤ k := by omega
  have hM : (0 : ℝ) < parameterM n k d t ε := by exact_mod_cast Aux.M_pos n k d t ε hk1 hd hn hε hε1
  have ht0 : (0 : ℝ) < t := by linarith
  have hApos : 0 < parameterA n k d t ε := by linarith
  rw [two_div_lambda n k d t ε hk1 hd hn ht hε hε1, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have h1 : Real.log (4 * t) ≤ Real.log (parameterA n k d t ε) := Real.log_le_log (by positivity) hA
  have h2 : Real.log (parameterM n k d t ε) ≤ 3 * k + Real.log (parameterA n k d t ε) := by
    have hMle := M_le n k d t ε (by linarith)
    calc Real.log (parameterM n k d t ε) ≤ Real.log ((8 : ℝ) ^ k * (Real.log (parameterA n k d t ε) + 1)) :=
          Real.log_le_log hM hMle
      _ = k * Real.log 8 + Real.log (Real.log (parameterA n k d t ε) + 1) := by
          rw [Real.log_mul (by positivity) (by linarith), Real.log_pow]
      _ ≤ k * 3 + Real.log (parameterA n k d t ε) := by
          have h8 : Real.log 8 < 3 := by
            rw [Real.log_lt_iff_lt_exp (by norm_num)]
            have := Real.exp_one_gt_d9
            have e3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
            have h27 : (2.7:ℝ)^3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
            norm_num at h27; linarith
          have hl := Real.log_le_sub_one_of_pos
            (show 0 < Real.log (parameterA n k d t ε) + 1 by linarith)
          have : (0 : ℝ) ≤ k := by positivity
          nlinarith
      _ = 3 * k + Real.log (parameterA n k d t ε) := by ring
  have hk' : (100 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have h3 := mul_le_mul_of_nonneg_left h2 hk0
  have h4 : 3 * (k : ℝ) ^ 2 ≤ 3 * (k : ℝ) ^ 2 * Real.log (parameterA n k d t ε) := by nlinarith
  have h5 : ((k : ℝ) + 2) * Real.log (parameterA n k d t ε) ≤
      (k : ℝ) ^ 2 * Real.log (parameterA n k d t ε) :=
    mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
  nlinarith

end CNFLearning873.Valiant.L43


namespace CNFLearning873.Valiant.L43

theorem two_pow_ge (k : ℕ) (hk : 100 ≤ k) : 64 * (k : ℝ) ^ 3 + 2 ≤ (2 : ℝ) ^ k := by
  have h1 : ∀ j : ℕ, 64 * ((j + 100 : ℕ) : ℝ) ^ 3 + 2 ≤ (2 : ℝ) ^ (j + 100) := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
      push_cast at ih ⊢
      rw [show j + 1 + 100 = (j + 100) + 1 by ring, pow_succ (2 : ℝ) (j + 100)]
      have hj : (0 : ℝ) ≤ j := by positivity
      have ha : (100 : ℝ) ≤ (j : ℝ) + 100 := by linarith
      have h3 : 3 * ((j : ℝ) + 100) ^ 2 + 3 * ((j : ℝ) + 100) + 1 ≤ ((j : ℝ) + 100) ^ 3 := by
        nlinarith [sq_nonneg ((j : ℝ) + 100)]
      have e : ((j : ℝ) + 1 + 100) ^ 2 * ((j : ℝ) + 1 + 100) = ((j : ℝ) + 100) ^ 3 +
        3 * ((j : ℝ) + 100) ^ 2 + 3 * ((j : ℝ) + 100) + 1 := by ring
      have e' : ((j : ℝ) + 1 + 100) ^ 3 = ((j : ℝ) + 100) ^ 3 +
        3 * ((j : ℝ) + 100) ^ 2 + 3 * ((j : ℝ) + 100) + 1 := by ring
      first | (rw [e]; nlinarith) | (rw [e']; nlinarith)
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 100 := ⟨k - 100, by omega⟩
  exact h1 j

theorem eight_pow_ge (k : ℕ) (hk : 100 ≤ k) : 64 * (k : ℝ) ^ 3 + 2 * 4 ^ k ≤ (8 : ℝ) ^ k := by
  have := two_pow_ge k hk
  have h4 : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
  have e : (8 : ℝ) ^ k = 2 ^ k * 4 ^ k := by rw [← mul_pow]; norm_num
  rw [e]
  have h64 : 0 ≤ 64 * (k : ℝ) ^ 3 := by positivity
  nlinarith

theorem inv_one_sub_le_exp (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1 / 2) : (1 - y)⁻¹ ≤ Real.exp (2 * y) := by
  have hpos : 0 < 1 - y := by linarith
  calc (1 - y)⁻¹ ≤ 1 + 2 * y := by
        rw [inv_le_iff_one_le_mul₀ hpos]; nlinarith
    _ ≤ Real.exp (2 * y) := by have := Real.add_one_le_exp (2 * y); linarith

theorem one_sub_le_exp (z : ℝ) : 1 - z ≤ Real.exp (-z) := by
  have := Real.add_one_le_exp (-z); linarith

theorem numI (k d ℓ m : ℕ) (hk : 100 ≤ k) (hd : 1 ≤ d) (hℓ1 : 1 ≤ ℓ) (hℓk : ℓ < k)
    (hcase : (2 : ℝ) ^ (k - ℓ) < 8 * k) (hi : 64 * (d : ℝ) * (k : ℝ) ^ 2 < (2 : ℝ) ^ k) :
    ((2 : ℝ) ^ ℓ)⁻¹ * (1 - ((2 : ℝ) ^ (k - ℓ))⁻¹) ^ m *
      ((1 - 2 / (2 : ℝ) ^ k) ^ (d * (ℓ + m * (k - ℓ))))⁻¹ ≤
      2 / 3 * Real.exp (-(m / (16 * k))) := by
  set y : ℝ := 2 / (2 : ℝ) ^ k with hy
  set z : ℝ := ((2 : ℝ) ^ (k - ℓ))⁻¹ with hz
  have hk' : (100 : ℝ) ≤ k := by exact_mod_cast hk
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hy0 : 0 ≤ y := by positivity
  -- d k y ≤ 1/4
  have hdky : (d : ℝ) * k * y ≤ 1 / 4 := by
    rw [hy, mul_div_assoc', div_le_iff₀ h2k]
    nlinarith
  have hy1 : y ≤ 1 / 2 := by
    have : (1 : ℝ) ≤ d * k := by nlinarith
    nlinarith
  have hpos : 0 < 1 - y := by linarith
  -- (1-y)^{dk} ≥ 3/4
  have hdk : 3 / 4 ≤ (1 - y) ^ (d * k) := by
    have := bernoulli y (d * k) hy0 (by linarith)
    push_cast at this; linarith
  -- first factor
  have hfirst : ((2 : ℝ) ^ ℓ)⁻¹ * ((1 - y) ^ (d * ℓ))⁻¹ ≤ 2 / 3 := by
    have h1 : (1 - y) ^ (d * k) ≤ (1 - y) ^ (d * ℓ) :=
      pow_le_pow_of_le_one hpos.le (by linarith) (Nat.mul_le_mul_left _ hℓk.le)
    have h2 : ((2 : ℝ) ^ ℓ)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      have : (2 : ℝ) ^ 1 ≤ 2 ^ ℓ := pow_le_pow_right₀ (by norm_num) hℓ1
      norm_num at this ⊢; linarith
    have h3 : ((1 - y) ^ (d * ℓ))⁻¹ ≤ 4 / 3 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
    calc _ ≤ (1 / 2) * (4 / 3) := mul_le_mul h2 h3 (by positivity) (by norm_num)
      _ = 2 / 3 := by norm_num
  -- 8 d (k - ℓ) ≤ 2^ℓ
  have h8 : 8 * (d : ℝ) * (k - ℓ : ℕ) ≤ 2 ^ ℓ := by
    have e : (2 : ℝ) ^ k = 2 ^ ℓ * 2 ^ (k - ℓ) := by rw [← pow_add]; congr 1; omega
    have hkl : ((k - ℓ : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k ℓ
    rw [e] at hi
    have h2l : (0 : ℝ) < 2 ^ ℓ := by positivity
    have : 64 * (d : ℝ) * k ^ 2 < 2 ^ ℓ * (8 * k) := by nlinarith
    have : 8 * (d : ℝ) * k < 2 ^ ℓ := by
      by_contra hc; push Not at hc; nlinarith
    have : 0 ≤ (d : ℝ) := by positivity
    nlinarith
  -- second factor
  have hsecond : (1 - z) * ((1 - y) ^ (d * (k - ℓ)))⁻¹ ≤ Real.exp (-(z / 2)) := by
    have hz0 : 0 ≤ z := by positivity
    have hz1 : z ≤ 1 := by rw [hz]; apply inv_le_one_of_one_le₀; exact one_le_pow₀ (by norm_num)
    have e1 : ((1 - y) ^ (d * (k - ℓ)))⁻¹ = ((1 - y)⁻¹) ^ (d * (k - ℓ)) := by rw [inv_pow]
    have e2 : ((1 - y)⁻¹) ^ (d * (k - ℓ)) ≤ Real.exp (2 * y) ^ (d * (k - ℓ)) :=
      pow_le_pow_left₀ (by positivity) (inv_one_sub_le_exp y hy0 hy1) _
    rw [← Real.exp_nat_mul] at e2
    have e3 : 1 - z ≤ Real.exp (-z) := one_sub_le_exp z
    have key : ((d * (k - ℓ) : ℕ) : ℝ) * (2 * y) ≤ z / 2 := by
      rw [hz, hy]
      have e : (2 : ℝ) ^ k = 2 ^ ℓ * 2 ^ (k - ℓ) := by rw [← pow_add]; congr 1; omega
      rw [e]
      have h2l : (0 : ℝ) < 2 ^ ℓ := by positivity
      have h2kl : (0 : ℝ) < 2 ^ (k - ℓ) := by positivity
      push_cast
      field_simp
      nlinarith
    calc (1 - z) * ((1 - y) ^ (d * (k - ℓ)))⁻¹ ≤ Real.exp (-z) * Real.exp (((d * (k - ℓ) : ℕ) : ℝ) * (2 * y)) := by
          rw [e1]
          apply mul_le_mul e3 e2 (by positivity) (by positivity)
      _ = Real.exp (-z + ((d * (k - ℓ) : ℕ) : ℝ) * (2 * y)) := by rw [Real.exp_add]
      _ ≤ Real.exp (-(z / 2)) := Real.exp_le_exp.mpr (by linarith)
  -- combine
  have hsplit : ((1 - y) ^ (d * (ℓ + m * (k - ℓ))))⁻¹ =
      ((1 - y) ^ (d * ℓ))⁻¹ * (((1 - y) ^ (d * (k - ℓ)))⁻¹) ^ m := by
    rw [show d * (ℓ + m * (k - ℓ)) = d * ℓ + d * (k - ℓ) * m by ring, pow_add,
      pow_mul (1 - y) (d * (k - ℓ)) m, mul_inv, inv_pow]
  rw [hsplit]
  have hz2 : 1 / (16 * (k : ℝ)) ≤ z / 2 := by
    have e : z / 2 = 1 / (2 * (2 : ℝ) ^ (k - ℓ)) := by rw [hz]; field_simp
    rw [e]
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hnn : 0 ≤ (1 - z) * ((1 - y) ^ (d * (k - ℓ)))⁻¹ := by
    have : z ≤ 1 := by rw [hz]; apply inv_le_one_of_one_le₀; exact one_le_pow₀ (by norm_num)
    have : 0 ≤ 1 - z := by linarith
    positivity
  have hsec_pow : ((1 - z) * ((1 - y) ^ (d * (k - ℓ)))⁻¹) ^ m ≤ Real.exp (-(m / (16 * k))) := by
    calc _ ≤ Real.exp (-(z / 2)) ^ m := pow_le_pow_left₀ hnn hsecond m
      _ = Real.exp (m * (-(z / 2))) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (-(m / (16 * k))) := by
          apply Real.exp_le_exp.mpr
          have hm : (0 : ℝ) ≤ m := by positivity
          have := mul_le_mul_of_nonneg_left hz2 hm
          rw [mul_one_div] at this
          linarith
  have hA : 0 ≤ ((2 : ℝ) ^ ℓ)⁻¹ * ((1 - y) ^ (d * ℓ))⁻¹ := by positivity
  calc ((2 : ℝ) ^ ℓ)⁻¹ * (1 - z) ^ m * (((1 - y) ^ (d * ℓ))⁻¹ * (((1 - y) ^ (d * (k - ℓ)))⁻¹) ^ m)
      = (((2 : ℝ) ^ ℓ)⁻¹ * ((1 - y) ^ (d * ℓ))⁻¹) *
          ((1 - z) * ((1 - y) ^ (d * (k - ℓ)))⁻¹) ^ m := by rw [mul_pow]; ring
    _ ≤ (2 / 3) * Real.exp (-(m / (16 * k))) :=
        mul_le_mul hfirst hsec_pow (pow_nonneg hnn m) (by norm_num)

theorem contraI (k : ℕ) (hk : 100 ≤ k) (lam P L : ℝ) (m : ℕ) (hlam : 0 < lam)
    (hlow : lam / 2 < P) (hup : P ≤ 2 / 3 * Real.exp (-(m / (16 * k))))
    (hm : (8 : ℝ) ^ k * L ≤ m) (hL : 1 ≤ L) (hΛ : Real.log (2 / lam) ≤ 4 * (k : ℝ) ^ 2 * L) :
    False := by
  have hk' : (100 : ℝ) ≤ k := by exact_mod_cast hk
  have h8 := eight_pow_ge k hk
  have h1 : 4 * (k : ℝ) ^ 2 * L ≤ m / (16 * k) := by
    rw [le_div_iff₀ (by positivity)]
    have : 64 * (k : ℝ) ^ 3 * L ≤ 8 ^ k * L := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      have : (0 : ℝ) ≤ 2 * 4 ^ k := by positivity
      linarith
    nlinarith
  have h2 : Real.exp (-(m / (16 * k))) ≤ lam / 2 := by
    have : Real.exp (-Real.log (2 / lam)) = lam / 2 := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
    rw [← this]; apply Real.exp_le_exp.mpr; linarith
  linarith

theorem contraII (k : ℕ) (hk : 100 ≤ k) (lam P L : ℝ) (m : ℕ) (hlam : 0 < lam)
    (hlow : lam / 2 < P) (hup : P ≤ 4 / 3 * Real.exp (-(m / (2 : ℝ) ^ (k + 1))))
    (hm : (8 : ℝ) ^ k * L ≤ m) (hL : 1 ≤ L) (hΛ : Real.log (2 / lam) ≤ 4 * (k : ℝ) ^ 2 * L) :
    False := by
  have hk' : (100 : ℝ) ≤ k := by exact_mod_cast hk
  have h8 := eight_pow_ge k hk
  have h4 : 4 * (k : ℝ) ^ 2 + 1 ≤ 4 ^ k / 2 := by
    have : (4 : ℝ) ^ k ≥ 64 * k ^ 3 + 2 := by
      have hh : (2 : ℝ) ^ k ≤ 4 ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
      linarith [two_pow_ge k hk]
    nlinarith
  have h1 : 4 * (k : ℝ) ^ 2 * L + 1 ≤ m / 2 ^ (k + 1) := by
    rw [le_div_iff₀ (by positivity)]
    have e : (8 : ℝ) ^ k = 2 ^ (k + 1) * (4 ^ k / 2) := by
      rw [pow_succ, show (8 : ℝ) = 2 * 4 by norm_num, mul_pow]; ring
    rw [e] at hm
    have h2 : (0 : ℝ) < 2 ^ (k + 1) := by positivity
    have : (4 * (k : ℝ) ^ 2 + 1) * L ≤ (4 ^ k / 2) * L := mul_le_mul_of_nonneg_right h4 (by linarith)
    have h22 : (2 : ℝ) ≤ 2 ^ (k + 1) := by
      have := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) (show 1 ≤ k + 1 by omega)
      simpa using this
    nlinarith
  have h2 : Real.exp (-(m / (2 : ℝ) ^ (k + 1))) ≤ Real.exp (-1) * (lam / 2) := by
    have : Real.exp (-1 - Real.log (2 / lam)) = Real.exp (-1) * (lam / 2) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log (by positivity)]
      field_simp
    rw [← this]; apply Real.exp_le_exp.mpr; linarith
  have he : Real.exp (-1) < 3 / 4 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    have := Real.exp_one_gt_d9; linarith
  have hl2 : 0 < lam / 2 := by positivity
  nlinarith

end CNFLearning873.Valiant.L43


namespace CNFLearning873.Valiant.L43
open CNFLearning873.Valiant

variable {n : ℕ}

theorem pD_or_le (E G : Assignment n → Prop) : pD (fun x => E x ∨ G x) ≤ pD E + pD G := by
  have h1 := pD_split (fun x => E x ∨ G x) E
  have h2 : pD (fun x => (E x ∨ G x) ∧ E x) ≤ pD E := pD_mono (fun x hx => hx.2)
  have h3 : pD (fun x => (E x ∨ G x) ∧ ¬ E x) ≤ pD G := pD_mono (fun x hx => hx.1.resolve_left hx.2)
  linarith

theorem pD_exists_le {β : Type} (S : Finset β) (P : β → Assignment n → Prop) :
    pD (fun x => ∃ c ∈ S, P c x) ≤ ∑ c ∈ S, pD (P c) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.notMem_empty, false_and, exists_false, Finset.sum_empty]
             exact (pD_mono (E' := fun _ => False) (fun x h => h)).trans (by
               rw [pD_eq]; simp)
  | insert c S hc ih =>
    rw [Finset.sum_insert hc]
    calc pD (fun x => ∃ c' ∈ insert c S, P c' x) ≤ pD (fun x => P c x ∨ ∃ c' ∈ S, P c' x) :=
          pD_mono (fun x ⟨c', hc', hp⟩ => by
            rcases Finset.mem_insert.mp hc' with rfl | h
            · exact Or.inl hp
            · exact Or.inr ⟨c', h, hp⟩)
      _ ≤ pD (P c) + pD (fun x => ∃ c' ∈ S, P c' x) := pD_or_le _ _
      _ ≤ _ := by linarith

theorem dep_and {E G : Assignment n → Prop} {W W' : Finset (Fin n)} (hE : DependsOn E W)
    (hG : DependsOn G W') : DependsOn (fun x => E x ∧ G x) (W ∪ W') := by
  classical
  intro x y hxy
  have h1 := hE x y (fun v hv => hxy v (Finset.mem_union_left _ hv))
  have h2 := hG x y (fun v hv => hxy v (Finset.mem_union_right _ hv))
  simp only [h1, h2]

theorem pD_sat (c : Clause n) : pD (fun x => Sat x c) = 1 - ((2 : ℝ) ^ width c)⁻¹ := by
  have := pD_split (fun _ => True) (fun x => Sat x c)
  rw [pD_true, pD_congr (E := fun x => True ∧ Sat x c) (E' := fun x => Sat x c) (by simp),
    pD_congr (E := fun x => True ∧ ¬ Sat x c) (E' := Violates c) (by simp [Violates]),
    pD_violates] at this
  linarith

/-- product formula for clauses with pairwise disjoint supports, disjoint from an event's
variables -/
theorem pD_prod_formula (E : Assignment n → Prop) (W0 : Finset (Fin n)) (hE : DependsOn E W0)
    (T : CNF n) (hT : ∀ b ∈ T, ∀ b' ∈ T, b ≠ b' → Disjoint (support b) (support b'))
    (hTW : ∀ b ∈ T, Disjoint (support b) W0) :
    pD (fun x => E x ∧ SatF T x) = pD E * ∏ b ∈ T, (1 - ((2 : ℝ) ^ width b)⁻¹) := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, mul_one]; exact pD_congr (fun x => by simp [satF_empty])
  | insert b T hb ih =>
    have hT' : ∀ c ∈ T, ∀ c' ∈ T, c ≠ c' → Disjoint (support c) (support c') :=
      fun c hc c' hc' h => hT c (Finset.mem_insert_of_mem hc) c' (Finset.mem_insert_of_mem hc') h
    have hTW' : ∀ c ∈ T, Disjoint (support c) W0 := fun c hc => hTW c (Finset.mem_insert_of_mem hc)
    rw [Finset.prod_insert hb, ← pD_sat]
    rw [pD_congr (E := fun x => E x ∧ SatF (insert b T) x)
      (E' := fun x => Sat x b ∧ (E x ∧ SatF T x)) (fun x => by rw [satF_insert]; tauto)]
    rw [pD_indep (dep_sat b) (dep_and hE (dep_satF T)), ih hT' hTW']
    · ring
    · rw [Finset.disjoint_union_right]
      refine ⟨hTW b (Finset.mem_insert_self b T), ?_⟩
      rw [Finset.disjoint_biUnion_right]
      intro c hc
      exact hT b (Finset.mem_insert_self b T) c (Finset.mem_insert_of_mem hc)
        (fun h => hb (h ▸ hc))

/-- a family of pairwise disjoint sets each meeting `W` has at most `|W|` members -/
theorem card_disjoint_meeting (T : CNF n) (W : Finset (Fin n))
    (hT : ∀ b ∈ T, ∀ b' ∈ T, b ≠ b' → Disjoint (support b) (support b'))
    (hW : ∀ b ∈ T, ¬ Disjoint (support b) W) : T.card ≤ W.card := by
  classical
  have hex : ∀ b ∈ T, ∃ v, v ∈ support b ∧ v ∈ W := fun b hb => by
    have := hW b hb; rw [Finset.not_disjoint_iff] at this; exact this
  choose f hf using hex
  rcases T.eq_empty_or_nonempty with h0 | ⟨b0, hb0⟩
  · rw [h0]; simp
  let g : Clause n → Fin n := fun b => if h : b ∈ T then f b h else f b0 hb0
  apply Finset.card_le_card_of_injOn g
  · intro b hb; simp only [g, dif_pos (Finset.mem_coe.mp hb)]; exact (hf b hb).2
  · intro b hb b' hb' hgg
    by_contra hne
    simp only [g, dif_pos (Finset.mem_coe.mp hb), dif_pos (Finset.mem_coe.mp hb')] at hgg
    have := hT b hb b' hb' hne
    exact Finset.disjoint_left.mp this (hf b hb).1 (hgg ▸ (hf b' hb').1)

theorem subclause_restrict (c : Clause n) (U : Finset (Fin n)) : Subclause (restrict c U) c := by
  intro v b h; simp only [restrict] at h; split_ifs at h; exact h

theorem support_restrict (c : Clause n) (U : Finset (Fin n)) :
    support (restrict c U) = support c ∩ U := by
  ext v; simp only [mem_support, restrict, Finset.mem_inter]
  split_ifs with h <;> simp [h]

theorem sat_of_subclause {s c : Clause n} (h : Subclause s c) {x : Assignment n} (hs : Sat x s) :
    Sat x c := by
  obtain ⟨i, hi⟩ := hs; exact ⟨i, h i _ hi⟩

theorem violates_of_subclause {s c : Clause n} (h : Subclause s c) {x : Assignment n}
    (hc : Violates c x) : Violates s x := fun hs => hc (sat_of_subclause h hs)

theorem support_subset_of_subclause {s c : Clause n} (h : Subclause s c) :
    support s ⊆ support c := by
  intro v hv
  rw [mem_support] at hv ⊢
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hv
  rw [h v b hb]; rfl

end CNFLearning873.Valiant.L43


namespace CNFLearning873.Valiant.L43
open CNFLearning873.Valiant

variable {n : ℕ}

structure KeyCtx (F : CNF n) (k d : ℕ) (t : ℝ) (s : Clause n) (Rb : CNF n) : Prop where
  hk : 100 ≤ k
  hd : 1 ≤ d
  ht : 1 ≤ t
  hLLL : LLLCondition k d t
  hF : KD F k d
  hℓ : width s < k
  hRw : ∀ b ∈ Rb, width b = k - width s
  hRs : ∀ b ∈ Rb, Disjoint (support b) (support s)
  hRd : ∀ b ∈ Rb, ∀ b' ∈ Rb, b ≠ b' → Disjoint (support b) (support b')
  hRo : ∀ b ∈ Rb, ∀ f ∈ F, ((support b ∩ support f).card : ℝ) ≤ k / (1 + t)

/-- basic numeric facts -/
theorem y_facts (k d : ℕ) (hk : 100 ≤ k) (hd : 1 ≤ d)
    (hi : 64 * (d : ℝ) * (k : ℝ) ^ 2 < (2 : ℝ) ^ k) :
    0 < 2 / (2 : ℝ) ^ k ∧ 2 / (2 : ℝ) ^ k < 1 ∧ (d : ℝ) * k * (2 / (2 : ℝ) ^ k) ≤ 1 / 4 ∧
      3 / 4 ≤ (1 - 2 / (2 : ℝ) ^ k) ^ (d * k) := by
  have hk' : (100 : ℝ) ≤ k := by exact_mod_cast hk
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hdky : (d : ℝ) * k * (2 / (2 : ℝ) ^ k) ≤ 1 / 4 := by
    rw [mul_div_assoc', div_le_iff₀ h2k]; nlinarith
  have hy1 : 2 / (2 : ℝ) ^ k ≤ 1 / 4 := by
    have : (1 : ℝ) ≤ d * k := by nlinarith
    have : 0 ≤ 2 / (2 : ℝ) ^ k := by positivity
    nlinarith
  refine ⟨by positivity, by linarith, hdky, ?_⟩
  have := bernoulli (2 / (2 : ℝ) ^ k) (d * k) (by positivity) (by linarith)
  push_cast at this; linarith

theorem lllHyp_global (F : CNF n) (k d : ℕ) (hk : 100 ≤ k) (hd : 1 ≤ d) (hF : KD F k d)
    (hi : 64 * (d : ℝ) * (k : ℝ) ^ 2 < (2 : ℝ) ^ k) :
    LLLHyp F (fun _ => 2 / (2 : ℝ) ^ k) := by
  obtain ⟨hy0, hy1, -, hdk⟩ := y_facts k d hk hd hi
  refine ⟨fun c _ => ⟨hy0.le, hy1⟩, fun c hc => ?_⟩
  rw [pD_violates, hF.1 c hc]
  have hcount : (nbr F c).card ≤ d * k := by
    have := card_meeting_le F d hF.2 (support c)
    rw [← width_eq, hF.1 c hc] at this
    exact (Finset.card_le_card (nbr_subset F c)).trans this
  have hp := prod_const_ge (nbr F c) (fun _ => 2 / (2 : ℝ) ^ k) (2 / (2 : ℝ) ^ k) (d * k)
    (fun _ _ => rfl) hy0.le hy1.le hcount
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have : ((2 : ℝ) ^ k)⁻¹ = 2 / (2 : ℝ) ^ k * (1 / 2) := by field_simp
  rw [this]
  apply mul_le_mul_of_nonneg_left _ hy0.le
  linarith

/-- Case I upper bound -/
theorem caseI_bound (F : CNF n) (k d : ℕ) (t : ℝ) (s : Clause n) (Rb : CNF n)
    (C : KeyCtx F k d t s Rb) (hcase : (2 : ℝ) ^ (k - width s) < 8 * k) :
    pD (fun x => (Violates s x ∧ SatF Rb x) ∧ SatF F x) ≤
      2 / 3 * Real.exp (-(Rb.card / (16 * k))) * pD (SatF F) := by
  classical
  have hi := est_i k d t C.hk C.hd C.ht C.hLLL
  set y : ℝ := 2 / (2 : ℝ) ^ k with hy
  obtain ⟨hy0, hy1, -, -⟩ := y_facts k d C.hk C.hd hi
  have hx := lllHyp_global F k d C.hk C.hd C.hF hi
  set ℓ := width s with hℓdef
  have hℓ1 : 1 ≤ ℓ := by
    by_contra h0
    have h0 : ℓ = 0 := by omega
    rw [h0, Nat.sub_zero] at hcase
    have := two_pow_ge k C.hk
    have hk' : (100 : ℝ) ≤ k := by exact_mod_cast C.hk
    nlinarith
  set W := support s ∪ Rb.biUnion support with hW
  have hWcard : W.card ≤ ℓ + Rb.card * (k - ℓ) := by
    calc W.card ≤ (support s).card + (Rb.biUnion support).card := Finset.card_union_le _ _
      _ ≤ ℓ + ∑ b ∈ Rb, (support b).card := by
          rw [← width_eq]; exact Nat.add_le_add_left Finset.card_biUnion_le _
      _ = ℓ + Rb.card * (k - ℓ) := by
          rw [Finset.sum_congr rfl (fun b hb => by rw [← width_eq, C.hRw b hb]), Finset.sum_const,
            smul_eq_mul]
  have hdepA : DependsOn (fun x => Violates s x ∧ SatF Rb x) W :=
    dep_and (dep_violates s) (dep_satF Rb)
  have hcond := lll_cond F (fun _ => y) hx _ W hdepA
  -- product lower bound
  have hprod : (1 - y) ^ (d * (ℓ + Rb.card * (k - ℓ))) ≤
      ∏ c ∈ F.filter (fun c => ¬ Disjoint (support c) W), (1 - y) := by
    apply prod_const_ge _ _ y _ (fun _ _ => rfl) hy0.le hy1.le
    exact (card_meeting_le F d C.hF.2 W).trans (Nat.mul_le_mul_left _ hWcard)
  have hprodpos : 0 < (1 - y) ^ (d * (ℓ + Rb.card * (k - ℓ))) := by
    apply pow_pos; linarith
  -- pD of the event
  have hpA : pD (fun x => Violates s x ∧ SatF Rb x) =
      ((2 : ℝ) ^ ℓ)⁻¹ * (1 - ((2 : ℝ) ^ (k - ℓ))⁻¹) ^ Rb.card := by
    rw [pD_prod_formula (Violates s) (support s) (dep_violates s) Rb C.hRd C.hRs, pD_violates,
      Finset.prod_congr rfl (fun b hb => by rw [C.hRw b hb]), Finset.prod_const]
  have hnum := numI k d ℓ Rb.card C.hk C.hd hℓ1 C.hℓ hcase hi
  have hS := pD_nonneg (SatF F)
  have hpAnn := pD_nonneg (fun x => Violates s x ∧ SatF Rb x)
  calc pD (fun x => (Violates s x ∧ SatF Rb x) ∧ SatF F x)
      ≤ pD (fun x => Violates s x ∧ SatF Rb x) * pD (SatF F) *
          (∏ c ∈ F.filter (fun c => ¬ Disjoint (support c) W), (1 - y))⁻¹ := hcond
    _ ≤ pD (fun x => Violates s x ∧ SatF Rb x) * pD (SatF F) *
          ((1 - y) ^ (d * (ℓ + Rb.card * (k - ℓ))))⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact inv_anti₀ hprodpos hprod
    _ = (((2 : ℝ) ^ ℓ)⁻¹ * (1 - ((2 : ℝ) ^ (k - ℓ))⁻¹) ^ Rb.card *
          ((1 - y) ^ (d * (ℓ + Rb.card * (k - ℓ))))⁻¹) * pD (SatF F) := by rw [hpA]; ring
    _ ≤ 2 / 3 * Real.exp (-(Rb.card / (16 * k))) * pD (SatF F) :=
        mul_le_mul_of_nonneg_right hnum hS

end CNFLearning873.Valiant.L43


namespace CNFLearning873.Valiant.L43
open CNFLearning873.Valiant

variable {n : ℕ}

section CaseII
variable (F : CNF n) (k d : ℕ) (t : ℝ) (s : Clause n) (Rb : CNF n)

noncomputable def C2 : CNF n := by
  classical
  exact F.filter (fun c => Disjoint (support c) (support s))

noncomputable def xw (c : Clause n) : ℝ := by
  classical
  exact if c ∈ Rb then 1 / (4 * (k : ℝ)) else 2 / (2 : ℝ) ^ k

theorem C2_sub : C2 F s ⊆ F := by
  classical
  unfold C2; exact Finset.filter_subset _ _

theorem C2_disj {c : Clause n} (hc : c ∈ C2 F s) : Disjoint (support c) (support s) := by
  classical
  unfold C2 at hc; exact (Finset.mem_filter.mp hc).2

theorem quarter_facts (hk : 100 ≤ k) :
    0 < 1 / (4 * (k : ℝ)) ∧ 1 / (4 * (k : ℝ)) < 1 ∧ 3 / 4 ≤ (1 - 1 / (4 * (k : ℝ))) ^ k := by
  have hk' : (100 : ℝ) ≤ k := by exact_mod_cast hk
  refine ⟨by positivity, by rw [div_lt_one (by positivity)]; linarith, ?_⟩
  have := bernoulli (1 / (4 * (k : ℝ))) k (by positivity)
    (by rw [div_le_one (by positivity)]; linarith)
  have e : (k : ℝ) * (1 / (4 * k)) = 1 / 4 := by field_simp
  rw [e] at this; linarith

/-- product lower bound over a subfamily of `C2 ∪ Rb` meeting a small set -/
theorem plb (C : KeyCtx F k d t s Rb) (G : CNF n) (hG : G ⊆ C2 F s ∪ Rb) (W : Finset (Fin n))
    (hW : W.card ≤ k) (hGW : ∀ c ∈ G, ¬ Disjoint (support c) W) :
    9 / 16 ≤ ∏ c ∈ G, (1 - xw k Rb c) := by
  classical
  have hi := est_i k d t C.hk C.hd C.ht C.hLLL
  obtain ⟨hy0, hy1, -, hdk⟩ := y_facts k d C.hk C.hd hi
  obtain ⟨hq0, hq1, hqk⟩ := quarter_facts k C.hk
  rw [← Finset.prod_filter_mul_prod_filter_not G (fun c => c ∈ Rb)]
  have h1 : (1 - 1 / (4 * (k : ℝ))) ^ k ≤ ∏ c ∈ G.filter (fun c => c ∈ Rb), (1 - xw k Rb c) := by
    apply prod_const_ge _ _ _ _ (fun c hc => by
      simp only [xw, (Finset.mem_filter.mp hc).2, if_true]) hq0.le hq1.le
    refine le_trans ?_ hW
    apply card_disjoint_meeting
    · intro b hb b' hb' hne
      exact C.hRd b (Finset.mem_filter.mp hb).2 b' (Finset.mem_filter.mp hb').2 hne
    · intro b hb; exact hGW b (Finset.mem_filter.mp hb).1
  have h2 : (1 - 2 / (2 : ℝ) ^ k) ^ (d * k) ≤
      ∏ c ∈ G.filter (fun c => c ∉ Rb), (1 - xw k Rb c) := by
    apply prod_const_ge _ _ _ _ (fun c hc => by
      simp only [xw, (Finset.mem_filter.mp hc).2, if_false]) hy0.le hy1.le
    have hsub : G.filter (fun c => c ∉ Rb) ⊆ F.filter (fun c => ¬ Disjoint (support c) W) := by
      intro c hc
      obtain ⟨hcG, hcR⟩ := Finset.mem_filter.mp hc
      have : c ∈ C2 F s := by
        rcases Finset.mem_union.mp (hG hcG) with h | h
        · exact h
        · exact absurd h hcR
      exact Finset.mem_filter.mpr ⟨C2_sub F s this, hGW c hcG⟩
    exact (Finset.card_le_card hsub).trans ((card_meeting_le F d C.hF.2 W).trans
      (Nat.mul_le_mul_left _ hW))
  have : (0 : ℝ) ≤ (1 - 1 / (4 * (k : ℝ))) ^ k := by positivity
  nlinarith

theorem lllHyp_L0 (C : KeyCtx F k d t s Rb) (hcase : 8 * (k : ℝ) ≤ (2 : ℝ) ^ (k - width s)) :
    LLLHyp (C2 F s ∪ Rb) (xw k Rb) := by
  classical
  have hi := est_i k d t C.hk C.hd C.ht C.hLLL
  obtain ⟨hy0, hy1, -, -⟩ := y_facts k d C.hk C.hd hi
  obtain ⟨hq0, hq1, -⟩ := quarter_facts k C.hk
  refine ⟨fun c _ => ?_, fun c hc => ?_⟩
  · unfold xw; split_ifs
    · exact ⟨hq0.le, hq1⟩
    · exact ⟨hy0.le, hy1⟩
  · have hwc : width c ≤ k := by
      rcases Finset.mem_union.mp hc with h | h
      · rw [C.hF.1 c (C2_sub F s h)]
      · rw [C.hRw c h]; omega
    have hprod : 9 / 16 ≤ ∏ c' ∈ nbr (C2 F s ∪ Rb) c, (1 - xw k Rb c') := by
      apply plb F k d t s Rb C _ ((nbr_subset _ c).trans (Finset.filter_subset _ _)) (support c)
        (by rw [← width_eq]; exact hwc)
      intro c' hc'
      exact (Finset.mem_filter.mp (nbr_subset _ c hc')).2
    rw [pD_violates]
    by_cases hcR : c ∈ Rb
    · simp only [xw, hcR, if_true]
      rw [C.hRw c hcR]
      have hk' : (100 : ℝ) ≤ k := by exact_mod_cast C.hk
      calc ((2 : ℝ) ^ (k - width s))⁻¹ ≤ (8 * (k : ℝ))⁻¹ := inv_anti₀ (by positivity) hcase
        _ = 1 / (4 * k) * (1 / 2) := by field_simp; ring
        _ ≤ 1 / (4 * k) * (9 / 16) := by
            apply mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by positivity)
    · simp only [xw, hcR, if_false]
      have hcC2 : c ∈ C2 F s := by
        rcases Finset.mem_union.mp hc with h | h
        · exact h
        · exact absurd h hcR
      rw [C.hF.1 c (C2_sub F s hcC2)]
      have h2k : (0 : ℝ) < 2 ^ k := by positivity
      calc ((2 : ℝ) ^ k)⁻¹ = 2 / (2 : ℝ) ^ k * (1 / 2) := by field_simp
        _ ≤ 2 / (2 : ℝ) ^ k * (9 / 16) := by
            apply mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by positivity)

/-- the lower bound on violating one added residual clause -/
theorem lb_violate (C : KeyCtx F k d t s Rb) (hcase : 8 * (k : ℝ) ≤ (2 : ℝ) ^ (k - width s))
    (T : CNF n) (hT : T ⊆ Rb) (b : Clause n) (hb : b ∈ Rb) (hbT : b ∉ T) :
    ((2 : ℝ) ^ (k + 1))⁻¹ * pD (SatF (C2 F s ∪ T)) ≤
      pD (fun x => Violates b x ∧ SatF (C2 F s ∪ T) x) := by
  classical
  have hx := lllHyp_L0 F k d t s Rb C hcase
  set L := C2 F s ∪ T with hLdef
  have hLsub : L ⊆ C2 F s ∪ Rb := Finset.union_subset_union le_rfl hT
  set N := L.filter (fun c => ¬ Disjoint (support c) (support b)) with hN
  set L' := L.filter (fun c => Disjoint (support c) (support b)) with hL'
  have hNC2 : N ⊆ C2 F s := by
    intro c hc
    obtain ⟨hcL, hcb⟩ := Finset.mem_filter.mp hc
    rcases Finset.mem_union.mp hcL with h | h
    · exact h
    · exfalso
      have hne : c ≠ b := fun e => hbT (e ▸ h)
      exact hcb (C.hRd c (hT h) b hb hne)
  let cut : Clause n → Clause n := fun c => restrict c (support c \ support b)
  set NC := N.image cut with hNC
  have hsupp_cut : ∀ c, support (cut c) = support c \ support b := by
    intro c; simp only [cut, support_restrict]
    ext v; simp only [Finset.mem_inter, Finset.mem_sdiff]; tauto
  -- the event G
  have hL'x : LLLHyp L' (xw k Rb) :=
    lllHyp_mono _ _ _ hx ((Finset.filter_subset _ _).trans hLsub)
  -- width of the cut clauses
  have ha : ∀ c ∈ N, (k : ℝ) * t / (1 + t) ≤ width (cut c) := by
    intro c hc
    have hcF : c ∈ F := C2_sub F s (hNC2 hc)
    have hov := C.hRo b hb c hcF
    rw [width_eq, hsupp_cut]
    have h1 := Finset.card_sdiff_add_card_inter (support c) (support b)
    have hck : (support c).card = k := by rw [← width_eq]; exact C.hF.1 c hcF
    have hint : (support c ∩ support b).card = (support b ∩ support c).card := by
      rw [Finset.inter_comm]
    have : ((support c \ support b).card : ℝ) = k - (support b ∩ support c).card := by
      rw [← hint]; push_cast [← hck, ← h1]; ring
    rw [this]
    have ht0 : 0 < 1 + t := by linarith [C.ht]
    have : (k : ℝ) * t / (1 + t) = k - k / (1 + t) := by field_simp; ring
    linarith
  have hviol_cut : ∀ c ∈ N, pD (Violates (cut c)) ≤ (2 : ℝ) ^ (-((k : ℝ) * t / (1 + t))) := by
    intro c hc
    rw [pD_violates, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [ha c hc])
  have hiii := est_iii k d t C.hk C.hd C.ht C.hLLL
  have hNcard : NC.card ≤ d * k := by
    refine Finset.card_image_le.trans ?_
    have : N ⊆ (C2 F s).filter (fun c => ¬ Disjoint (support c) (support b)) := by
      intro c hc; exact Finset.mem_filter.mpr ⟨hNC2 hc, (Finset.mem_filter.mp hc).2⟩
    refine (Finset.card_le_card this).trans ((card_meeting_le _ d ?_ _).trans ?_)
    · intro v
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (C2_sub F s))).trans (C.hF.2 v)
    · rw [← width_eq, C.hRw b hb]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  -- bound for each cut clause
  have hterm : ∀ c' ∈ NC, pD (fun x => Violates c' x ∧ SatF L' x) ≤
      (2 : ℝ) ^ (-((k : ℝ) * t / (1 + t))) * (16 / 9) * pD (SatF L') := by
    intro c' hc'
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hc'
    have hcF : c ∈ F := C2_sub F s (hNC2 hc)
    have h1 := lll_cond L' (xw k Rb) hL'x (Violates (cut c)) (support (cut c)) (dep_violates _)
    have hp := plb F k d t s Rb C (L'.filter (fun c' => ¬ Disjoint (support c') (support (cut c))))
      ((Finset.filter_subset _ _).trans ((Finset.filter_subset _ _).trans hLsub)) (support (cut c))
      (by rw [hsupp_cut]; refine (Finset.card_le_card Finset.sdiff_subset).trans ?_
          rw [← width_eq, C.hF.1 c hcF])
      (fun c'' hc'' => (Finset.mem_filter.mp hc'').2)
    have hpos : (0 : ℝ) < 9 / 16 := by norm_num
    have hinv : (∏ c'' ∈ L'.filter (fun c' => ¬ Disjoint (support c') (support (cut c))),
        (1 - xw k Rb c''))⁻¹ ≤ 16 / 9 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    calc _ ≤ _ := h1
      _ ≤ (2 : ℝ) ^ (-((k : ℝ) * t / (1 + t))) * pD (SatF L') * (16 / 9) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right (hviol_cut c hc) (pD_nonneg _)) hinv
            (inv_nonneg.mpr (by linarith)) (by have := pD_nonneg (SatF L'); positivity)
      _ = _ := by ring
  -- pD of G
  have hG : (7 / 9) * pD (SatF L') ≤ pD (SatF (L' ∪ NC)) := by
    have hsplit := pD_split (SatF L') (SatF NC)
    have h1 : pD (fun x => SatF L' x ∧ SatF NC x) = pD (SatF (L' ∪ NC)) :=
      pD_congr (fun x => by rw [satF_union])
    have h2 : pD (fun x => SatF L' x ∧ ¬ SatF NC x) ≤
        pD (fun x => ∃ c' ∈ NC, Violates c' x ∧ SatF L' x) := by
      apply pD_mono
      intro x ⟨hx1, hx2⟩
      simp only [SatF, not_forall] at hx2
      obtain ⟨c', hc', hnot⟩ := hx2
      exact ⟨c', hc', hnot, hx1⟩
    have h3 := pD_exists_le NC (fun c' x => Violates c' x ∧ SatF L' x)
    have h4 : ∑ c' ∈ NC, pD (fun x => Violates c' x ∧ SatF L' x) ≤
        (d * k : ℕ) * ((2 : ℝ) ^ (-((k : ℝ) * t / (1 + t))) * (16 / 9) * pD (SatF L')) := by
      calc _ ≤ ∑ _c' ∈ NC, (2 : ℝ) ^ (-((k : ℝ) * t / (1 + t))) * (16 / 9) * pD (SatF L') :=
            Finset.sum_le_sum hterm
        _ = NC.card * ((2 : ℝ) ^ (-((k : ℝ) * t / (1 + t))) * (16 / 9) * pD (SatF L')) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := by
            apply mul_le_mul_of_nonneg_right (by exact_mod_cast hNcard)
            have := pD_nonneg (SatF L'); positivity
    have hpL := pD_nonneg (SatF L')
    have e : ((d * k : ℕ) : ℝ) * ((2 : ℝ) ^ (-((k : ℝ) * t / (1 + t))) * (16 / 9) * pD (SatF L')) =
        ((d : ℝ) * k * (2 : ℝ) ^ (-((k : ℝ) * t / (1 + t)))) * (16 / 9) * pD (SatF L') := by
      push_cast; ring
    rw [e] at h4
    have h5 : ((d : ℝ) * k * (2 : ℝ) ^ (-((k : ℝ) * t / (1 + t)))) * (16 / 9) * pD (SatF L') ≤
        (1 / 8) * (16 / 9) * pD (SatF L') := by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hiii (by norm_num)) hpL
    linarith
  have hL'L : pD (SatF L) ≤ pD (SatF L') :=
    pD_mono (fun x hx c hc => hx c ((Finset.filter_subset _ _) hc))
  -- independence
  have hind : pD (fun x => Violates b x ∧ SatF (L' ∪ NC) x) =
      pD (Violates b) * pD (SatF (L' ∪ NC)) := by
    apply pD_indep (dep_violates b) (dep_satF _)
    rw [Finset.disjoint_biUnion_right]
    intro c hc
    rcases Finset.mem_union.mp hc with h | h
    · exact (Finset.mem_filter.mp h).2.symm
    · obtain ⟨c0, -, rfl⟩ := Finset.mem_image.mp h
      rw [hsupp_cut]; exact Finset.disjoint_sdiff
  have himp : pD (fun x => Violates b x ∧ SatF (L' ∪ NC) x) ≤
      pD (fun x => Violates b x ∧ SatF L x) := by
    apply pD_mono
    intro x ⟨hv, hs⟩
    refine ⟨hv, fun c hc => ?_⟩
    by_cases hcb : Disjoint (support c) (support b)
    · exact hs c (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hc, hcb⟩))
    · have hcN : c ∈ N := Finset.mem_filter.mpr ⟨hc, hcb⟩
      exact sat_of_subclause (subclause_restrict c _)
        (hs (cut c) (Finset.mem_union_right _ (Finset.mem_image_of_mem cut hcN)))
  have hvb : ((2 : ℝ) ^ k)⁻¹ ≤ pD (Violates b) := by
    rw [pD_violates, C.hRw b hb]
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have hpL := pD_nonneg (SatF L)
  have hGL : (1 / 2) * pD (SatF L) ≤ pD (SatF (L' ∪ NC)) := by linarith
  calc ((2 : ℝ) ^ (k + 1))⁻¹ * pD (SatF L) = ((2 : ℝ) ^ k)⁻¹ * ((1 / 2) * pD (SatF L)) := by
        rw [pow_succ]; field_simp
    _ ≤ pD (Violates b) * pD (SatF (L' ∪ NC)) :=
        mul_le_mul hvb hGL (by positivity) (pD_nonneg _)
    _ = _ := hind.symm
    _ ≤ _ := himp

end CaseII

end CNFLearning873.Valiant.L43


namespace CNFLearning873.Valiant.L43
open CNFLearning873.Valiant

variable {n : ℕ}

theorem telescope (F : CNF n) (k d : ℕ) (t : ℝ) (s : Clause n) (Rb : CNF n)
    (C : KeyCtx F k d t s Rb) (hcase : 8 * (k : ℝ) ≤ (2 : ℝ) ^ (k - width s)) :
    ∀ T : CNF n, T ⊆ Rb →
      pD (SatF (C2 F s ∪ T)) ≤ pD (SatF (C2 F s)) * (1 - ((2 : ℝ) ^ (k + 1))⁻¹) ^ T.card := by
  classical
  intro T
  induction T using Finset.induction_on with
  | empty => intro _; simp
  | insert b T hbT ih =>
    intro hT
    have hT' : T ⊆ Rb := fun x hx => hT (Finset.mem_insert_of_mem hx)
    have hb : b ∈ Rb := hT (Finset.mem_insert_self b T)
    have hlb := lb_violate F k d t s Rb C hcase T hT' b hb hbT
    have e : C2 F s ∪ insert b T = insert b (C2 F s ∪ T) := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    rw [e, pD_insert, Finset.card_insert_of_notMem hbT, pow_succ]
    have h1 := ih hT'
    have hz : 0 ≤ 1 - ((2 : ℝ) ^ (k + 1))⁻¹ := by
      have : ((2 : ℝ) ^ (k + 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
      linarith
    calc pD (SatF (C2 F s ∪ T)) - pD (fun x => Violates b x ∧ SatF (C2 F s ∪ T) x)
        ≤ (1 - ((2 : ℝ) ^ (k + 1))⁻¹) * pD (SatF (C2 F s ∪ T)) := by linarith
      _ ≤ (1 - ((2 : ℝ) ^ (k + 1))⁻¹) *
            (pD (SatF (C2 F s)) * (1 - ((2 : ℝ) ^ (k + 1))⁻¹) ^ T.card) :=
          mul_le_mul_of_nonneg_left h1 hz
      _ = _ := by ring

theorem satF_ge_C2 (F : CNF n) (k d : ℕ) (t : ℝ) (s : Clause n) (Rb : CNF n)
    (C : KeyCtx F k d t s Rb) : (3 / 4) * pD (SatF (C2 F s)) ≤ pD (SatF F) := by
  classical
  have hi := est_i k d t C.hk C.hd C.ht C.hLLL
  obtain ⟨hy0, hy1, hdky, hdk⟩ := y_facts k d C.hk C.hd hi
  have hx := lllHyp_mono _ _ _ (lllHyp_global F k d C.hk C.hd C.hF hi) (C2_sub F s)
  set C1 := F.filter (fun c => ¬ Disjoint (support c) (support s)) with hC1
  have h1 : pD (SatF (C2 F s)) ≤ pD (SatF F) +
      pD (fun x => ∃ c ∈ C1, Violates c x ∧ SatF (C2 F s) x) := by
    have := pD_split (SatF (C2 F s)) (SatF F)
    have h2 : pD (fun x => SatF (C2 F s) x ∧ SatF F x) ≤ pD (SatF F) := pD_mono (fun x h => h.2)
    have h3 : pD (fun x => SatF (C2 F s) x ∧ ¬ SatF F x) ≤
        pD (fun x => ∃ c ∈ C1, Violates c x ∧ SatF (C2 F s) x) := by
      apply pD_mono
      intro x ⟨hx1, hx2⟩
      simp only [SatF, not_forall] at hx2
      obtain ⟨c, hcF, hnot⟩ := hx2
      refine ⟨c, Finset.mem_filter.mpr ⟨hcF, fun hdis => ?_⟩, hnot, hx1⟩
      apply hnot
      exact hx1 c (by unfold C2; exact Finset.mem_filter.mpr ⟨hcF, hdis⟩)
    linarith
  have hterm : ∀ c ∈ C1, pD (fun x => Violates c x ∧ SatF (C2 F s) x) ≤
      ((2 : ℝ) ^ k)⁻¹ * (4 / 3) * pD (SatF (C2 F s)) := by
    intro c hc
    have hcF : c ∈ F := (Finset.mem_filter.mp hc).1
    have h := lll_cond (C2 F s) (fun _ => 2 / (2 : ℝ) ^ k) hx (Violates c) (support c)
      (dep_violates c)
    have hp : (1 - 2 / (2 : ℝ) ^ k) ^ (d * k) ≤
        ∏ c' ∈ (C2 F s).filter (fun c' => ¬ Disjoint (support c') (support c)),
          (1 - 2 / (2 : ℝ) ^ k) := by
      apply prod_const_ge _ _ _ _ (fun _ _ => rfl) hy0.le hy1.le
      refine (Finset.card_le_card (Finset.filter_subset_filter _ (C2_sub F s))).trans ?_
      have := card_meeting_le F d C.hF.2 (support c)
      rwa [← width_eq, C.hF.1 c hcF] at this
    have hinv : (∏ c' ∈ (C2 F s).filter (fun c' => ¬ Disjoint (support c') (support c)),
        (1 - 2 / (2 : ℝ) ^ k))⁻¹ ≤ 4 / 3 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    rw [pD_violates, C.hF.1 c hcF] at h
    calc _ ≤ _ := h
      _ ≤ ((2 : ℝ) ^ k)⁻¹ * pD (SatF (C2 F s)) * (4 / 3) :=
          mul_le_mul_of_nonneg_left hinv (by have := pD_nonneg (SatF (C2 F s)); positivity)
      _ = _ := by ring
  have hC1card : C1.card ≤ d * k := by
    refine (card_meeting_le F d C.hF.2 (support s)).trans ?_
    rw [← width_eq]; exact Nat.mul_le_mul_left _ C.hℓ.le
  have h2 := pD_exists_le C1 (fun c x => Violates c x ∧ SatF (C2 F s) x)
  have h3 : ∑ c ∈ C1, pD (fun x => Violates c x ∧ SatF (C2 F s) x) ≤
      (d * k : ℕ) * (((2 : ℝ) ^ k)⁻¹ * (4 / 3) * pD (SatF (C2 F s))) := by
    calc _ ≤ ∑ _c ∈ C1, ((2 : ℝ) ^ k)⁻¹ * (4 / 3) * pD (SatF (C2 F s)) := Finset.sum_le_sum hterm
      _ = C1.card * (((2 : ℝ) ^ k)⁻¹ * (4 / 3) * pD (SatF (C2 F s))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right (by exact_mod_cast hC1card)
          have := pD_nonneg (SatF (C2 F s)); positivity
  have hp := pD_nonneg (SatF (C2 F s))
  have e : ((d * k : ℕ) : ℝ) * (((2 : ℝ) ^ k)⁻¹ * (4 / 3) * pD (SatF (C2 F s))) =
      ((d : ℝ) * k * (2 / (2 : ℝ) ^ k)) * (2 / 3) * pD (SatF (C2 F s)) := by
    push_cast; field_simp; ring
  rw [e] at h3
  have h4 : ((d : ℝ) * k * (2 / (2 : ℝ) ^ k)) * (2 / 3) * pD (SatF (C2 F s)) ≤
      (1 / 4) * (2 / 3) * pD (SatF (C2 F s)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdky (by norm_num)) hp
  linarith

theorem caseII_bound (F : CNF n) (k d : ℕ) (t : ℝ) (s : Clause n) (Rb : CNF n)
    (C : KeyCtx F k d t s Rb) (hcase : 8 * (k : ℝ) ≤ (2 : ℝ) ^ (k - width s)) :
    pD (fun x => (Violates s x ∧ SatF Rb x) ∧ SatF F x) ≤
      4 / 3 * Real.exp (-(Rb.card / (2 : ℝ) ^ (k + 1))) * pD (SatF F) := by
  classical
  have h1 : pD (fun x => (Violates s x ∧ SatF Rb x) ∧ SatF F x) ≤ pD (SatF (C2 F s ∪ Rb)) := by
    apply pD_mono
    intro x ⟨⟨_, hR⟩, hF⟩
    rw [satF_union]
    exact ⟨fun c hc => hF c (C2_sub F s hc), hR⟩
  have h2 := telescope F k d t s Rb C hcase Rb le_rfl
  have h3 := satF_ge_C2 F k d t s Rb C
  have hz : (1 - ((2 : ℝ) ^ (k + 1))⁻¹) ^ Rb.card ≤ Real.exp (-(Rb.card / (2 : ℝ) ^ (k + 1))) := by
    have hz0 : 0 ≤ 1 - ((2 : ℝ) ^ (k + 1))⁻¹ := by
      have : ((2 : ℝ) ^ (k + 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
      linarith
    calc _ ≤ Real.exp (-((2 : ℝ) ^ (k + 1))⁻¹) ^ Rb.card :=
          pow_le_pow_left₀ hz0 (one_sub_le_exp _) _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; field_simp
  have hp := pD_nonneg (SatF (C2 F s))
  have hE : 0 ≤ Real.exp (-(Rb.card / (2 : ℝ) ^ (k + 1))) := (Real.exp_pos _).le
  calc _ ≤ pD (SatF (C2 F s ∪ Rb)) := h1
    _ ≤ pD (SatF (C2 F s)) * (1 - ((2 : ℝ) ^ (k + 1))⁻¹) ^ Rb.card := h2
    _ ≤ pD (SatF (C2 F s)) * Real.exp (-(Rb.card / (2 : ℝ) ^ (k + 1))) :=
        mul_le_mul_of_nonneg_left hz hp
    _ ≤ (4 / 3 * pD (SatF F)) * Real.exp (-(Rb.card / (2 : ℝ) ^ (k + 1))) :=
        mul_le_mul_of_nonneg_right (by linarith) hE
    _ = _ := by ring

end CNFLearning873.Valiant.L43


namespace CNFLearning873.Valiant.L43
open CNFLearning873.Valiant

variable {n : ℕ}

noncomputable def res (s c : Clause n) : Clause n := restrict c (support c \ support s)

theorem support_res (s c : Clause n) : support (res s c) = support c \ support s := by
  unfold res; rw [support_restrict]
  ext v; simp only [Finset.mem_inter, Finset.mem_sdiff]; tauto

theorem violates_of_split {s c : Clause n} (h : Subclause s c) {x : Assignment n}
    (hs : Violates s x) (hr : Violates (res s c) x) : Violates c x := by
  rw [violates_iff] at hs hr ⊢
  intro v b hv
  by_cases hvs : v ∈ support s
  · obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp (mem_support.mp hvs)
    have := h v b' hb'
    rw [hv] at this
    cases this
    exact hs v b hb'
  · apply hr v b
    unfold res restrict
    have : v ∈ support c \ support s := by
      rw [Finset.mem_sdiff]; exact ⟨mem_support.mpr (by simp [hv]), hvs⟩
    simp [this, hv]

theorem width_res {s c : Clause n} (h : Subclause s c) : width (res s c) = width c - width s := by
  rw [width_eq, width_eq, width_eq, support_res, Finset.card_sdiff_of_subset
    (support_subset_of_subclause h)]

/-- The key lemma (core of Lemma 4.5): there are no `M+1` rare clauses containing a frequent
subclause whose residuals are pairwise disjoint and have small overlaps. -/
theorem key_lemma (F : CNF n) (h : (solutions F).Nonempty) (k d : ℕ) (t ε : ℝ)
    (hk : 100 ≤ k) (hd : 1 ≤ d) (ht : 1 ≤ t) (hLLL : LLLCondition k d t) (hF : KD F k d)
    (hkn : k ≤ n) (hε : 0 < ε) (hε1 : ε < 1)
    (s : Clause n) (hs : width s < k) (hq : parameterLambda n k d t ε < q F h s)
    (R : CNF n) (hR : parameterM n k d t ε + 1 ≤ R.card)
    (hRw : ∀ c ∈ R, width c = k) (hRs : ∀ c ∈ R, Subclause s c)
    (hRq : ∀ c ∈ R, q F h c < parameterTau n k d t ε)
    (hRo : ∀ c ∈ R, ∀ f ∈ F, (((support c \ support s) ∩ support f).card : ℝ) ≤ k / (1 + t))
    (hRd : ∀ c ∈ R, ∀ c' ∈ R, c ≠ c' →
      Disjoint (support c \ support s) (support c' \ support s)) : False := by
  classical
  obtain ⟨R', hR'R, hR'card⟩ := Finset.exists_subset_card_eq hR
  set M := parameterM n k d t ε
  set lam := parameterLambda n k d t ε
  set τ := parameterTau n k d t ε
  have hn : 1 ≤ n := by omega
  have hk1 : 1 ≤ k := by omega
  have hMpos : 0 < M := Aux.M_pos n k d t ε hk1 hd hn hε hε1
  have hlam : 0 < lam := Aux.lambda_pos n k d t ε hk1 hd hn ht hε hε1
  -- residual family
  set Rb := R'.image (res s)
  have hresinj : ∀ c ∈ R', ∀ c' ∈ R', res s c = res s c' → c = c' := by
    intro c hc c' hc' he
    by_contra hne
    have hdis := hRd c (hR'R hc) c' (hR'R hc') hne
    have e1 : support (res s c) = support (res s c') := by rw [he]
    rw [support_res, support_res] at e1
    rw [e1, disjoint_self, Finset.bot_eq_empty] at hdis
    have hw := width_res (hRs c' (hR'R hc'))
    rw [width_eq, support_res, hdis, Finset.card_empty, hRw c' (hR'R hc')] at hw
    omega
  have hRbcard : Rb.card = M + 1 := by
    rw [Finset.card_image_of_injOn (fun c hc c' hc' he => hresinj c hc c' hc' he), hR'card]
  have C : KeyCtx F k d t s Rb := by
    refine ⟨hk, hd, ht, hLLL, hF, hs, ?_, ?_, ?_, ?_⟩
    · intro b hb
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
      rw [width_res (hRs c (hR'R hc)), hRw c (hR'R hc)]
    · intro b hb
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
      rw [support_res]; exact Finset.sdiff_disjoint
    · intro b hb b' hb' hne
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hb'
      rw [support_res, support_res]
      exact hRd c (hR'R hc) c' (hR'R hc') (fun e => hne (e ▸ rfl))
    · intro b hb f hf
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
      rw [support_res]; exact hRo c (hR'R hc) f hf
  -- the probabilities through pD
  have hS : 0 < pD (SatF F) := pD_pos_of_nonempty F h
  set S := pD (SatF F)
  have hqeq : ∀ c, q F h c = pD (fun x => Violates c x ∧ SatF F x) / S := fun c => by
    unfold q; rw [eventProb_eq]
  set P := pD (fun x => (Violates s x ∧ SatF Rb x) ∧ SatF F x) / S with hPdef
  -- lower bound
  have hlow : lam / 2 < P := by
    have h1 : pD (fun x => Violates s x ∧ SatF F x) ≤
        pD (fun x => (Violates s x ∧ SatF Rb x) ∧ SatF F x) +
          ∑ c ∈ R', pD (fun x => Violates c x ∧ SatF F x) := by
      calc _ ≤ pD (fun x => ((Violates s x ∧ SatF Rb x) ∧ SatF F x) ∨
            ∃ c ∈ R', Violates c x ∧ SatF F x) := by
            apply pD_mono
            intro x ⟨hv, hsat⟩
            by_cases hR : SatF Rb x
            · exact Or.inl ⟨⟨hv, hR⟩, hsat⟩
            · right
              simp only [SatF, not_forall] at hR
              obtain ⟨b, hb, hnb⟩ := hR
              obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
              exact ⟨c, hc, violates_of_split (hRs c (hR'R hc)) hv hnb, hsat⟩
        _ ≤ _ := (pD_or_le _ _).trans (by linarith [pD_exists_le R' (fun c x => Violates c x ∧ SatF F x)])
    have h2 : ∑ c ∈ R', pD (fun x => Violates c x ∧ SatF F x) < (M + 1 : ℕ) * (τ * S) := by
      have hne : R'.Nonempty := by rw [← Finset.card_pos, hR'card]; omega
      calc _ < ∑ _c ∈ R', τ * S := by
            apply Finset.sum_lt_sum_of_nonempty hne
            intro c hc
            have := hRq c (hR'R hc)
            rw [hqeq, div_lt_iff₀ hS] at this
            exact this
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hR'card]
    have h3 : lam * S < pD (fun x => Violates s x ∧ SatF F x) := by
      have := hq; rw [hqeq, lt_div_iff₀ hS] at this; exact this
    have hτ : ((M + 1 : ℕ) : ℝ) * τ ≤ lam / 2 := by
      simp only [τ, parameterTau]
      have hM : (1 : ℝ) ≤ M := by exact_mod_cast hMpos
      push_cast
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    rw [hPdef, lt_div_iff₀ hS]
    have : ((M + 1 : ℕ) : ℝ) * (τ * S) ≤ lam / 2 * S := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hτ hS.le
    linarith
  -- the parameters
  have hL := logA_ge_one n k d t ε hk hd hn hε hε1
  have hm : (8 : ℝ) ^ k * Real.log (parameterA n k d t ε) ≤ ((M + 1 : ℕ) : ℝ) := by
    have := M_ge n k d t ε; push_cast; linarith
  have hΛ := log_two_div_lambda n k d t ε hk hd hn ht hε hε1
  -- the two cases
  by_cases hcase : (2 : ℝ) ^ (k - width s) < 8 * k
  · have hup := caseI_bound F k d t s Rb C hcase
    rw [hRbcard] at hup
    have : P ≤ 2 / 3 * Real.exp (-(((M + 1 : ℕ) : ℝ) / (16 * k))) := by
      rw [hPdef, div_le_iff₀ hS]; push_cast at hup ⊢; exact hup
    exact contraI k hk lam P _ (M + 1) hlam hlow this hm hL hΛ
  · push Not at hcase
    have hup := caseII_bound F k d t s Rb C hcase
    rw [hRbcard] at hup
    have : P ≤ 4 / 3 * Real.exp (-(((M + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (k + 1))) := by
      rw [hPdef, div_le_iff₀ hS]; push_cast at hup ⊢; exact hup
    exact contraII k hk lam P _ (M + 1) hlam hlow this hm hL hΛ

end CNFLearning873.Valiant.L43


namespace CNFLearning873.Valiant.L43
open CNFLearning873.Valiant

variable {n : ℕ}

theorem mem_rare {F : CNF n} {h : (solutions F).Nonempty} {k d : ℕ} {t ε : ℝ} {c : Clause n}
    (hkn : k ≤ n) (hc : c ∈ rare F h k d t ε) : width c = k ∧ q F h c < parameterTau n k d t ε := by
  classical
  unfold rare at hc
  rw [if_neg (not_lt.mpr hkn)] at hc
  simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  exact hc

theorem eq_of_subclause_width {s c : Clause n} (h : Subclause s c) (hw : width s = width c) :
    s = c := by
  have hsub := support_subset_of_subclause h
  have heq : support s = support c := Finset.eq_of_subset_of_card_le hsub (by
    rw [← width_eq, ← width_eq, hw])
  funext v
  by_cases hv : v ∈ support s
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (mem_support.mp hv)
    rw [hb, h v b hb]
  · have hv' : v ∉ support c := heq ▸ hv
    rw [not_mem_support.mp hv, not_mem_support.mp hv']

theorem support_update (s : Clause n) (v : Fin n) (b : Bool) :
    support (Function.update s v (some b)) = insert v (support s) := by
  ext w
  simp only [mem_support, Finset.mem_insert]
  by_cases hw : w = v
  · subst hw; simp
  · simp [Function.update_of_ne hw, hw]

theorem group_bound (F : CNF n) (h : (solutions F).Nonempty) (k d : ℕ) (t ε : ℝ)
    (hk : 100 ≤ k) (hd : 1 ≤ d) (ht : 1 ≤ t) (hLLL : LLLCondition k d t) (hF : KD F k d)
    (hkn : k ≤ n) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ j : ℕ, ∀ (s : Clause n) (A : CNF n), k - width s ≤ j → width s ≤ k →
      A ⊆ rare F h k d t ε → (∀ c ∈ A, Subclause s c) →
      (∀ c ∈ A, ∀ f ∈ F, (((support c \ support s) ∩ support f).card : ℝ) ≤ k / (1 + t)) →
      pD (fun x => (∃ c ∈ A, Violates c x) ∧ SatF F x) ≤
        (2 * k * (parameterM n k d t ε : ℝ)) ^ (k - width s) * parameterLambda n k d t ε *
          pD (SatF F) := by
  classical
  set M := parameterM n k d t ε
  set lam := parameterLambda n k d t ε
  set τ := parameterTau n k d t ε
  have hn : 1 ≤ n := by omega
  have hk1 : 1 ≤ k := by omega
  have hMpos : 0 < M := Aux.M_pos n k d t ε hk1 hd hn hε hε1
  have hlam : 0 < lam := Aux.lambda_pos n k d t ε hk1 hd hn ht hε hε1
  have hτlam : τ ≤ lam := by
    simp only [τ, parameterTau]
    have hM : (1 : ℝ) ≤ M := by exact_mod_cast hMpos
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hS : 0 < pD (SatF F) := pD_pos_of_nonempty F h
  set S := pD (SatF F)
  have hqeq : ∀ c, q F h c = pD (fun x => Violates c x ∧ SatF F x) / S := fun c => by
    unfold q; rw [eventProb_eq]
  have hbase1 : (1 : ℝ) ≤ 2 * k * (M : ℝ) := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hMpos
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    nlinarith
  -- trivial bound through the common subclause
  have hsmall : ∀ (s : Clause n) (A : CNF n), (∀ c ∈ A, Subclause s c) →
      pD (fun x => (∃ c ∈ A, Violates c x) ∧ SatF F x) ≤ q F h s * S := by
    intro s A hA
    rw [hqeq, div_mul_cancel₀ _ hS.ne']
    apply pD_mono
    rintro x ⟨⟨c, hc, hv⟩, hs⟩
    exact ⟨violates_of_subclause (hA c hc) hv, hs⟩
  have hempty : ∀ (A : CNF n), A = ∅ → pD (fun x => (∃ c ∈ A, Violates c x) ∧ SatF F x) = 0 := by
    intro A hA; subst hA
    rw [pD_eq]; simp
  intro j
  induction j with
  | zero =>
    intro s A hj hw hAr hAs hAo
    have hwk : width s = k := by omega
    rw [hwk, Nat.sub_self, pow_zero, one_mul]
    rcases A.eq_empty_or_nonempty with hA | ⟨c, hc⟩
    · rw [hempty A hA]; positivity
    · have hcs : s = c := eq_of_subclause_width (hAs c hc) (by rw [hwk, (mem_rare hkn (hAr hc)).1])
      have hq := (mem_rare hkn (hAr hc)).2
      rw [← hcs] at hq
      calc _ ≤ q F h s * S := hsmall s A hAs
        _ ≤ lam * S := mul_le_mul_of_nonneg_right (by linarith) hS.le
  | succ j ih =>
    intro s A hj hw hAr hAs hAo
    have hpow1 : (1 : ℝ) ≤ (2 * k * (M : ℝ)) ^ (k - width s) := one_le_pow₀ hbase1
    rcases A.eq_empty_or_nonempty with hA | ⟨c0, hc0⟩
    · rw [hempty A hA]; positivity
    by_cases hwk : width s = k
    · have hcs : s = c0 :=
        eq_of_subclause_width (hAs c0 hc0) (by rw [hwk, (mem_rare hkn (hAr hc0)).1])
      have hq := (mem_rare hkn (hAr hc0)).2
      rw [← hcs] at hq
      calc _ ≤ q F h s * S := hsmall s A hAs
        _ ≤ lam * S := mul_le_mul_of_nonneg_right (by linarith) hS.le
        _ = 1 * (lam * S) := by ring
        _ ≤ (2 * k * (M : ℝ)) ^ (k - width s) * (lam * S) :=
            mul_le_mul_of_nonneg_right hpow1 (by positivity)
        _ = _ := by ring
    have hwlt : width s < k := lt_of_le_of_ne hw hwk
    by_cases hqs : q F h s ≤ lam
    · calc _ ≤ q F h s * S := hsmall s A hAs
        _ ≤ lam * S := mul_le_mul_of_nonneg_right hqs hS.le
        _ = 1 * (lam * S) := by ring
        _ ≤ (2 * k * (M : ℝ)) ^ (k - width s) * (lam * S) :=
            mul_le_mul_of_nonneg_right hpow1 (by positivity)
        _ = _ := by ring
    push Not at hqs
    -- maximal family with disjoint residuals
    let DR : CNF n → Prop := fun R => ∀ c ∈ R, ∀ c' ∈ R, c ≠ c' →
      Disjoint (support c \ support s) (support c' \ support s)
    obtain ⟨R, hRmem, hRmax⟩ := Finset.exists_max_image (A.powerset.filter DR) Finset.card
      ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, fun c hc => absurd hc (by simp)⟩⟩
    obtain ⟨hRA, hRDR⟩ := Finset.mem_filter.mp hRmem
    rw [Finset.mem_powerset] at hRA
    have hRM : R.card ≤ M := by
      by_contra hc
      push Not at hc
      exact key_lemma F h k d t ε hk hd ht hLLL hF hkn hε hε1 s hwlt hqs R hc
        (fun c hc => (mem_rare hkn (hAr (hRA hc))).1) (fun c hc => hAs c (hRA hc))
        (fun c hc => (mem_rare hkn (hAr (hRA hc))).2) (fun c hc => hAo c (hRA hc)) hRDR
    set H := R.biUnion (fun c => support c \ support s) with hH
    have hHcard : H.card ≤ M * k := by
      refine Finset.card_biUnion_le.trans ?_
      calc ∑ c ∈ R, (support c \ support s).card ≤ ∑ _c ∈ R, k := by
            apply Finset.sum_le_sum
            intro c hc
            refine (Finset.card_le_card Finset.sdiff_subset).trans ?_
            rw [← width_eq, (mem_rare hkn (hAr (hRA hc))).1]
        _ = R.card * k := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ M * k := Nat.mul_le_mul_right _ hRM
    -- every clause meets H outside s
    have hcover : ∀ c ∈ A, ∃ v ∈ H, v ∈ support c \ support s := by
      intro c hc
      by_cases hcR : c ∈ R
      · have hne : (support c \ support s).Nonempty := by
          rw [← Finset.card_pos]
          have := width_res (hAs c hc)
          rw [width_eq, support_res, (mem_rare hkn (hAr hc)).1] at this
          omega
        obtain ⟨v, hv⟩ := hne
        exact ⟨v, Finset.mem_biUnion.mpr ⟨c, hcR, hv⟩, hv⟩
      · by_contra hno
        push Not at hno
        have hDR' : DR (insert c R) := by
          intro a ha a' ha' hne
          rcases Finset.mem_insert.mp ha with h1 | h1
          · rcases Finset.mem_insert.mp ha' with h2 | h2
            · exact absurd (h1.trans h2.symm) hne
            · rw [Finset.disjoint_left]
              intro v hv hv'
              exact hno v (Finset.mem_biUnion.mpr ⟨a', h2, hv'⟩) (h1 ▸ hv)
          · rcases Finset.mem_insert.mp ha' with h2 | h2
            · rw [Finset.disjoint_left]
              intro v hv hv'
              exact hno v (Finset.mem_biUnion.mpr ⟨a, h1, hv⟩) (h2 ▸ hv')
            · exact hRDR a h1 a' h2 hne
        have hmem : insert c R ∈ A.powerset.filter DR :=
          Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hc hRA), hDR'⟩
        have := hRmax _ hmem
        rw [Finset.card_insert_of_notMem hcR] at this
        omega
    -- children
    let Ap : Fin n × Bool → CNF n := fun p => A.filter (fun c => p.1 ∉ support s ∧ c p.1 = some p.2)
    let sp : Fin n × Bool → Clause n := fun p => Function.update s p.1 (some p.2)
    have hchild : ∀ p : Fin n × Bool,
        pD (fun x => (∃ c ∈ Ap p, Violates c x) ∧ SatF F x) ≤
          (2 * k * (M : ℝ)) ^ (k - width s - 1) * lam * S := by
      intro p
      rcases (Ap p).eq_empty_or_nonempty with he | ⟨c1, hc1⟩
      · rw [hempty _ he]; positivity
      have hpv : p.1 ∉ support s := (Finset.mem_filter.mp hc1).2.1
      have hwsp : width (sp p) = width s + 1 := by
        simp only [sp, width_eq, support_update, Finset.card_insert_of_notMem hpv]
      have := ih (sp p) (Ap p) (by rw [hwsp]; omega) (by rw [hwsp]; omega)
        ((Finset.filter_subset _ _).trans hAr)
        (by
          intro c hc w b hwb
          obtain ⟨hcA, -, hcv⟩ := Finset.mem_filter.mp hc
          by_cases hw : w = p.1
          · subst hw
            simp only [sp, Function.update_self, Option.some.injEq] at hwb
            rw [hcv, hwb]
          · simp only [sp, Function.update_of_ne hw] at hwb
            exact hAs c hcA w b hwb)
        (by
          intro c hc f hf
          have hcA := (Finset.mem_filter.mp hc).1
          refine le_trans ?_ (hAo c hcA f hf)
          apply Nat.cast_le.mpr
          apply Finset.card_le_card
          apply Finset.inter_subset_inter_right
          apply Finset.sdiff_subset_sdiff le_rfl
          simp only [sp, support_update]; exact Finset.subset_insert _ _)
      rw [hwsp, show k - (width s + 1) = k - width s - 1 by omega] at this
      exact this
    have hunion : pD (fun x => (∃ c ∈ A, Violates c x) ∧ SatF F x) ≤
        ∑ p ∈ H ×ˢ (Finset.univ : Finset Bool),
          pD (fun x => (∃ c ∈ Ap p, Violates c x) ∧ SatF F x) := by
      refine le_trans (pD_mono ?_) (pD_exists_le _ _)
      rintro x ⟨⟨c, hc, hv⟩, hs⟩
      obtain ⟨v, hvH, hvc⟩ := hcover c hc
      rw [Finset.mem_sdiff] at hvc
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (mem_support.mp hvc.1)
      exact ⟨(v, b), Finset.mem_product.mpr ⟨hvH, Finset.mem_univ _⟩,
        ⟨c, Finset.mem_filter.mpr ⟨hc, hvc.2, hb⟩, hv⟩, hs⟩
    have hsum : ∑ p ∈ H ×ˢ (Finset.univ : Finset Bool),
        pD (fun x => (∃ c ∈ Ap p, Violates c x) ∧ SatF F x) ≤
          (H.card * 2 : ℕ) * ((2 * k * (M : ℝ)) ^ (k - width s - 1) * lam * S) := by
      calc _ ≤ ∑ _p ∈ H ×ˢ (Finset.univ : Finset Bool),
            (2 * k * (M : ℝ)) ^ (k - width s - 1) * lam * S := Finset.sum_le_sum (fun p _ => hchild p)
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_product, Finset.card_univ,
              Fintype.card_bool]
    have hH2 : ((H.card * 2 : ℕ) : ℝ) ≤ 2 * k * (M : ℝ) := by
      have : H.card * 2 ≤ 2 * k * M := by nlinarith
      exact_mod_cast this
    have hpos : 0 ≤ (2 * k * (M : ℝ)) ^ (k - width s - 1) * lam * S := by positivity
    have hexp : (2 * k * (M : ℝ)) ^ (k - width s) =
        (2 * k * (M : ℝ)) * (2 * k * (M : ℝ)) ^ (k - width s - 1) := by
      rw [← pow_succ']; congr 1; omega
    calc _ ≤ _ := hunion
      _ ≤ _ := hsum
      _ ≤ (2 * k * (M : ℝ)) * ((2 * k * (M : ℝ)) ^ (k - width s - 1) * lam * S) :=
          mul_le_mul_of_nonneg_right hH2 hpos
      _ = _ := by rw [hexp]; ring

end CNFLearning873.Valiant.L43


namespace CNFLearning873.Valiant.L43
open CNFLearning873.Valiant

variable {n : ℕ}

theorem card_inter_union (A U B : Finset (Fin n)) :
    (A ∩ (U ∪ B)).card = (A ∩ U).card + ((A \ U) ∩ B).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext v; simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]; tauto
  · rw [Finset.disjoint_left]; intro v hv hv'
    simp only [Finset.mem_inter, Finset.mem_sdiff] at hv hv'; exact hv'.1.2 hv.2

/-- greedy choice of at most `⌈t⌉` target clauses absorbing every large overlap -/
theorem exists_root (F : CNF n) (k : ℕ) (t : ℝ) (ht : 1 ≤ t) (c : Clause n) (hc : width c = k) :
    ∃ T ⊆ F, T.card ≤ r t ∧
      ∀ f ∈ F, (((support c \ T.biUnion support) ∩ support f).card : ℝ) ≤ k / (1 + t) := by
  classical
  have ht0 : 0 < 1 + t := by linarith
  set κ : ℝ := k / (1 + t) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  let P : CNF n → Prop := fun T =>
    T = ∅ ∨ (T.card : ℝ) * κ < ((support c ∩ T.biUnion support).card : ℝ)
  obtain ⟨T, hTmem, hTmax⟩ := Finset.exists_max_image (F.powerset.filter P) Finset.card
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, Or.inl rfl⟩⟩
  obtain ⟨hTF, hTP⟩ := Finset.mem_filter.mp hTmem
  rw [Finset.mem_powerset] at hTF
  refine ⟨T, hTF, ?_, ?_⟩
  · rcases hTP with h0 | hlt
    · rw [h0]; simp
    · have hle : ((support c ∩ T.biUnion support).card : ℝ) ≤ k := by
        rw [← hc, width_eq]; exact_mod_cast Finset.card_le_card Finset.inter_subset_left
      have hk0 : (0 : ℝ) < k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · exfalso; rw [h0] at hle hκ; simp at hκ; rw [hκ] at hlt; simp at hlt
          have := Finset.card_pos.mpr hlt
          have : (0 : ℝ) < ((support c ∩ T.biUnion support).card : ℝ) := by exact_mod_cast this
          push_cast at hle; linarith
        · exact_mod_cast h0
      have : (T.card : ℝ) < 1 + t := by
        have h1 : (T.card : ℝ) * κ < k := lt_of_lt_of_le hlt hle
        rw [hκ, mul_div_assoc', div_lt_iff₀ ht0] at h1
        nlinarith
      have htr : t ≤ (r t : ℝ) := Nat.le_ceil t
      have : (T.card : ℝ) < 1 + r t := by linarith
      have : T.card < 1 + r t := by exact_mod_cast this
      omega
  · intro f hf
    by_contra hbig
    push Not at hbig
    have hfT : f ∉ T := by
      intro hfT
      have : (support c \ T.biUnion support) ∩ support f = ∅ := by
        ext v; simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.notMem_empty, iff_false]
        rintro ⟨⟨_, hv⟩, hvf⟩; exact hv (Finset.mem_biUnion.mpr ⟨f, hfT, hvf⟩)
      rw [this, Finset.card_empty, Nat.cast_zero] at hbig; linarith
    have hP' : P (insert f T) := by
      right
      rw [Finset.biUnion_insert, Finset.union_comm, card_inter_union, Finset.card_insert_of_notMem hfT]
      push_cast
      rcases hTP with h0 | hlt
      · subst h0
        simp only [Finset.card_empty, Nat.cast_zero, zero_add, one_mul, Finset.biUnion_empty,
          Finset.inter_empty, Finset.sdiff_empty] at hbig ⊢
        linarith
      · nlinarith
    have hmem : insert f T ∈ F.powerset.filter P :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hf hTF), hP'⟩
    have := hTmax _ hmem
    rw [Finset.card_insert_of_notMem hfT] at this
    omega

/-- clauses supported in `U` -/
theorem card_supported_le (U : Finset (Fin n)) :
    (Finset.univ.filter (fun s : Clause n => support s ⊆ U)).card ≤ 3 ^ U.card := by
  classical
  have : (Finset.univ.filter (fun s : Clause n => support s ⊆ U)).card ≤
      (Finset.univ : Finset (U → Option Bool)).card := by
    apply Finset.card_le_card_of_injOn (fun s v => s v.1)
    · intro s _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
    · intro s hs s' hs' he
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hs hs'
      funext v
      by_cases hv : v ∈ U
      · exact congrFun he ⟨v, hv⟩
      · rw [not_mem_support.mp (fun h => hv (hs h)), not_mem_support.mp (fun h => hv (hs' h))]
  refine this.trans (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_option, Fintype.card_bool, Fintype.card_coe]

theorem card_F_le (F : CNF n) (k d : ℕ) (hk : 1 ≤ k) (hF : KD F k d) : F.card ≤ d * n := by
  classical
  have h1 : ∑ f ∈ F, (support f).card = ∑ v : Fin n, (F.filter (fun f => v ∈ support f)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro f _
    rw [← Finset.sum_filter]; congr 1; ext v; simp
  have h2 : ∑ f ∈ F, (support f).card = F.card * k := by
    rw [Finset.sum_congr rfl (fun f hf => by rw [← width_eq, hF.1 f hf]), Finset.sum_const,
      smul_eq_mul]
  have h3 : ∑ v : Fin n, (F.filter (fun f => v ∈ support f)).card ≤ n * d := by
    calc _ ≤ ∑ _v : Fin n, d := Finset.sum_le_sum (fun v _ => hF.2 v)
      _ = n * d := by simp
  have : F.card * k ≤ n * d := by rw [← h2, h1]; exact h3
  nlinarith

theorem geom_le (X : ℝ) (hX : 2 ≤ X) (r : ℕ) : ∑ j ∈ Finset.range (r + 1), X ^ j ≤ 2 * X ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ]
    have : 2 * X ^ r ≤ X ^ (r + 1) := by
      rw [pow_succ]; have : 0 ≤ X ^ r := by positivity
      nlinarith
    linarith

end CNFLearning873.Valiant.L43


namespace CNFLearning873.Valiant.L43
open CNFLearning873.Valiant

theorem lemma43 (n k d : ℕ) (t ε : ℝ) (F : CNF n)
    (hk : 100 ≤ k) (hd : 1 ≤ d) (ht : 1 ≤ t)
    (hε : 0 < ε) (hε' : ε < 1) (hF : KD F k d) (hLLL : LLLCondition k d t) :
    ∃ h : (solutions F).Nonempty,
      eventProb (solutionLaw F h)
        (fun x => ∃ c ∈ rare F h k d t ε, Violates c x) ≤ ε := by
  classical
  have hi := est_i k d t hk hd ht hLLL
  have hpos := lll_pos F _ (lllHyp_global F k d hk hd hF hi)
  have h := nonempty_of_pD F hpos
  refine ⟨h, ?_⟩
  rw [eventProb_eq, div_le_iff₀ hpos]
  set S := pD (SatF F)
  by_cases hnk : n < k
  · have hr : rare F h k d t ε = ∅ := by unfold rare; rw [if_pos hnk]
    have : pD (fun x => (∃ c ∈ rare F h k d t ε, Violates c x) ∧ SatF F x) = 0 := by
      rw [pD_eq, hr]; simp
    rw [this]; positivity
  push Not at hnk
  have hn : 1 ≤ n := by omega
  have hk1 : 1 ≤ k := by omega
  set M := parameterM n k d t ε
  set lam := parameterLambda n k d t ε
  have hMpos : 0 < M := Aux.M_pos n k d t ε hk1 hd hn hε hε'
  have hlam : 0 < lam := Aux.lambda_pos n k d t ε hk1 hd hn ht hε hε'
  -- roots
  let Tof : Clause n → CNF n := fun c =>
    if hc : width c = k then Classical.choose (exists_root F k t ht c hc) else ∅
  have hTof : ∀ c, width c = k → Tof c ⊆ F ∧ (Tof c).card ≤ r t ∧
      ∀ f ∈ F, (((support c \ (Tof c).biUnion support) ∩ support f).card : ℝ) ≤ k / (1 + t) := by
    intro c hc
    simp only [Tof, dif_pos hc]
    exact Classical.choose_spec (exists_root F k t ht c hc)
  let rootOf : Clause n → Clause n := fun c => restrict c (support c ∩ (Tof c).biUnion support)
  have hsupp_root : ∀ c, support c \ support (rootOf c) = support c \ (Tof c).biUnion support := by
    intro c; simp only [rootOf, support_restrict]
    ext v; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
  set Roots : CNF n := (Finset.range (r t + 1)).biUnion (fun j => (F.powersetCard j).biUnion
    (fun T => Finset.univ.filter (fun s : Clause n => support s ⊆ T.biUnion support)))
  have hroot_mem : ∀ c, width c = k → rootOf c ∈ Roots := by
    intro c hc
    obtain ⟨hTF, hTr, -⟩ := hTof c hc
    simp only [Roots, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard,
      Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨(Tof c).card, by omega, Tof c, ⟨hTF, rfl⟩, ?_⟩
    simp only [rootOf, support_restrict]
    exact Finset.inter_subset_right.trans Finset.inter_subset_right
  -- count of roots
  set X : ℝ := (d : ℝ) * n * (2 * (k : ℝ)) ^ k
  have hX2 : 2 ≤ X := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hk' : (100 : ℝ) ≤ k := by exact_mod_cast hk
    have : (2 * (k : ℝ)) ≤ (2 * (k : ℝ)) ^ k := le_self_pow₀ (by linarith) (by omega)
    have : (1 : ℝ) ≤ (d : ℝ) * n := by nlinarith
    nlinarith
  have hRoots : (Roots.card : ℝ) ≤ 2 * X ^ r t := by
    have h1 : Roots.card ≤ ∑ j ∈ Finset.range (r t + 1), (F.card * 3 ^ k) ^ j := by
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum ?_)
      intro j _
      refine Finset.card_biUnion_le.trans ?_
      calc ∑ T ∈ F.powersetCard j, (Finset.univ.filter
            (fun s : Clause n => support s ⊆ T.biUnion support)).card
          ≤ ∑ _T ∈ F.powersetCard j, 3 ^ (k * j) := by
            apply Finset.sum_le_sum
            intro T hT
            obtain ⟨hTF, hTc⟩ := Finset.mem_powersetCard.mp hT
            refine (card_supported_le _).trans (Nat.pow_le_pow_right (by norm_num) ?_)
            calc (T.biUnion support).card ≤ ∑ f ∈ T, (support f).card := Finset.card_biUnion_le
              _ = ∑ _f ∈ T, k := Finset.sum_congr rfl (fun f hf => by
                  rw [← width_eq, hF.1 f (hTF hf)])
              _ = k * j := by rw [Finset.sum_const, smul_eq_mul, hTc, mul_comm]
        _ = F.card.choose j * 3 ^ (k * j) := by
            rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]
        _ ≤ F.card ^ j * (3 ^ k) ^ j := by
            rw [← pow_mul]; exact Nat.mul_le_mul_right _ (Nat.choose_le_pow _ _)
        _ = (F.card * 3 ^ k) ^ j := by rw [mul_pow]
    have h2 : ((F.card * 3 ^ k : ℕ) : ℝ) ≤ X := by
      have hFc := card_F_le F k d hk1 hF
      have h3 : (3 : ℝ) ^ k ≤ (2 * (k : ℝ)) ^ k := by
        apply pow_le_pow_left₀ (by norm_num)
        have : (100 : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      push_cast
      have : (F.card : ℝ) ≤ d * n := by exact_mod_cast hFc
      exact mul_le_mul this h3 (by positivity) (by positivity)
    calc (Roots.card : ℝ) ≤ ∑ j ∈ Finset.range (r t + 1), ((F.card * 3 ^ k : ℕ) : ℝ) ^ j := by
          exact_mod_cast h1
      _ ≤ ∑ j ∈ Finset.range (r t + 1), X ^ j :=
          Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (by positivity) h2 j)
      _ ≤ 2 * X ^ r t := geom_le X hX2 (r t)
  -- union over groups
  have hbase1 : (1 : ℝ) ≤ 2 * k * (M : ℝ) := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hMpos
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    nlinarith
  set R := rare F h k d t ε
  have hgroup : ∀ s ∈ R.image rootOf,
      pD (fun x => (∃ c ∈ R.filter (fun c => rootOf c = s), Violates c x) ∧ SatF F x) ≤
        (2 * k * (M : ℝ)) ^ k * lam * S := by
    intro s hs
    obtain ⟨c0, hc0, rfl⟩ := Finset.mem_image.mp hs
    have hw0 := (mem_rare hnk hc0).1
    have hws : width (rootOf c0) ≤ k := by
      rw [← hw0, width_eq, width_eq]
      exact Finset.card_le_card (support_subset_of_subclause (subclause_restrict _ _))
    have := group_bound F h k d t ε hk hd ht hLLL hF hnk hε hε' k (rootOf c0)
      (R.filter (fun c => rootOf c = rootOf c0)) (Nat.sub_le _ _) hws
      (Finset.filter_subset _ _)
      (by
        intro c hc
        rw [← (Finset.mem_filter.mp hc).2]
        exact subclause_restrict _ _)
      (by
        intro c hc f hf
        obtain ⟨hcR, hcr⟩ := Finset.mem_filter.mp hc
        rw [← hcr, hsupp_root]
        exact (hTof c (mem_rare hnk hcR).1).2.2 f hf)
    refine this.trans ?_
    apply mul_le_mul_of_nonneg_right _ hpos.le
    apply mul_le_mul_of_nonneg_right _ hlam.le
    exact pow_le_pow_right₀ hbase1 (Nat.sub_le _ _)
  have hunion : pD (fun x => (∃ c ∈ R, Violates c x) ∧ SatF F x) ≤
      ∑ s ∈ R.image rootOf,
        pD (fun x => (∃ c ∈ R.filter (fun c => rootOf c = s), Violates c x) ∧ SatF F x) := by
    refine le_trans (pD_mono ?_) (pD_exists_le _ _)
    rintro x ⟨⟨c, hc, hv⟩, hs⟩
    exact ⟨rootOf c, Finset.mem_image_of_mem _ hc,
      ⟨c, Finset.mem_filter.mpr ⟨hc, rfl⟩, hv⟩, hs⟩
  have himage : ((R.image rootOf).card : ℝ) ≤ 2 * X ^ r t := by
    refine le_trans ?_ hRoots
    exact_mod_cast Finset.card_le_card (fun s hs => by
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hs
      exact hroot_mem c (mem_rare hnk hc).1)
  have hfinal : 2 * X ^ r t * ((2 * k * (M : ℝ)) ^ k * lam) = ε / t := by
    simp only [X, lam, parameterLambda]
    have eM : ((parameterM n k d t ε : ℕ) : ℝ) = (M : ℝ) := rfl
    rw [eM]
    have : (0 : ℝ) < t := by linarith
    have : (0 : ℝ) < M := by exact_mod_cast hMpos
    have : (0 : ℝ) < d := by exact_mod_cast hd
    have : (0 : ℝ) < k := by exact_mod_cast hk1
    have : (0 : ℝ) < n := by exact_mod_cast hn
    field_simp
    ring
  have hεt : ε / t ≤ ε := div_le_self hε.le ht
  calc pD (fun x => (∃ c ∈ R, Violates c x) ∧ SatF F x)
      ≤ _ := hunion
    _ ≤ ∑ _s ∈ R.image rootOf, (2 * k * (M : ℝ)) ^ k * lam * S := Finset.sum_le_sum hgroup
    _ = (R.image rootOf).card * ((2 * k * (M : ℝ)) ^ k * lam) * S := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ 2 * X ^ r t * ((2 * k * (M : ℝ)) ^ k * lam) * S := by
        apply mul_le_mul_of_nonneg_right _ hpos.le
        exact mul_le_mul_of_nonneg_right himage (by positivity)
    _ = ε / t * S := by rw [hfinal]
    _ ≤ ε * S := mul_le_mul_of_nonneg_right hεt hpos.le

end CNFLearning873.Valiant.L43

open CNFLearning873.Valiant in
theorem solution (n k d : ℕ) (t ε : ℝ) (F : CNF n)
    (hk : 100 ≤ k) (hd : 1 ≤ d) (ht : 1 ≤ t)
    (hε : 0 < ε) (hε' : ε < 1) (hF : KD F k d) (hLLL : LLLCondition k d t) :
    ∃ h : (solutions F).Nonempty,
      eventProb (solutionLaw F h)
        (fun x => ∃ c ∈ rare F h k d t ε, Violates c x) ≤ ε :=
  CNFLearning873.Valiant.L43.lemma43 n k d t ε F hk hd ht hε hε' hF hLLL
