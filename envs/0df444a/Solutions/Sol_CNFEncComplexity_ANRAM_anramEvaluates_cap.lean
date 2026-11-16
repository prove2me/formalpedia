-- Prove2me | solution 1 for CNFEncComplexity.ANRAM.anramEvaluates_cap
-- status  : ACCEPTED   (prove)
-- author  : @bersubs
-- created : 2026-11-15T07:24:21.236303+00:00
-- url     : https://prove2.me/submissions/ab9755ba-1c90-454b-8543-feddc1029e85

import Definitions.Def_CNFEncComplexity_AnramEvaluates

namespace CNFEncComplexity.ANRAM

private theorem step_cost_pos {prog : List Instr} {w : List Bool} {c d : Config} {k : ℕ}
    (h : Step prog w c d k) : 0 < k := by
  cases h <;> unfold bitLen <;> omega

private theorem step_head_le {prog : List Instr} {w : List Bool} {c d : Config} {k : ℕ}
    (h : Step prog w c d k) : d.head ≤ c.head + k := by
  cases h <;> simp only [bitLen] <;> omega

private theorem step_congr_read {prog : List Instr} {w v : List Bool} {c d : Config} {k : ℕ}
    (h : Step prog w c d k) (hRead : readSym w c.head = readSym v c.head) :
    Step prog v c d k := by
  cases h with
  | loadc h => exact .loadc h
  | load h => exact .load h
  | loadi h => exact .loadi h
  | store h => exact .store h
  | storei h => exact .storei h
  | add h => exact .add h
  | sub h => exact .sub h
  | read h =>
    have hStep := Step.read (w := v) h
    rw [← hRead] at hStep
    exact hStep
  | jump h => exact .jump h
  | jzeroTaken h h0 => exact .jzeroTaken h h0
  | jzeroNotTaken h h0 => exact .jzeroNotTaken h h0
  | njumpLeft h => exact .njumpLeft h
  | njumpRight h => exact .njumpRight h

private theorem reaches_of_prefix {prog : List Instr} {w v : List Bool} {c d : Config} {k t : ℕ}
    (hPrefix : ∀ i < t, w[i]? = v[i]?) (h : Reaches prog w c d k) :
    c.head + k ≤ t → Reaches prog v c d k := by
  induction h with
  | refl c => exact fun _ => .refl c
  | @step c d _ k k' hStep _ ih =>
    intro hBudget
    have hPos := step_cost_pos hStep
    have hHead := step_head_le hStep
    have hRead : readSym w c.head = readSym v c.head := by
      unfold readSym
      rw [hPrefix _ (by omega)]
    exact .step (step_congr_read hStep hRead) (ih (by omega))

private theorem acceptsWithin_of_prefix (prog : List Instr) (w v : List Bool) (t : ℕ)
    (hPrefix : ∀ i < t, w[i]? = v[i]?) (h : AcceptsWithin prog w t) :
    AcceptsWithin prog v t := by
  obtain ⟨c, k, hTrace, hHalt, hAnswer, hCost⟩ := h
  refine ⟨c, k, reaches_of_prefix hPrefix hTrace ?_, hHalt, hAnswer, hCost⟩
  change 0 + k ≤ t
  omega

theorem acceptsWithin_congr_prefix (prog : List Instr) (w v : List Bool) (t : ℕ)
    (hPrefix : ∀ i < t, w[i]? = v[i]?) :
    AcceptsWithin prog w t ↔ AcceptsWithin prog v t :=
  ⟨acceptsWithin_of_prefix prog w v t hPrefix,
   acceptsWithin_of_prefix prog v w t (fun i hi => (hPrefix i hi).symm)⟩

theorem acceptsWithin_append_of_length_le (prog : List Instr) (w suffix : List Bool) (t : ℕ)
    (hLength : t ≤ w.length) :
    AcceptsWithin prog (w ++ suffix) t ↔ AcceptsWithin prog w t :=
  acceptsWithin_congr_prefix prog _ _ t
    (fun _ hi => List.getElem?_append_left (hi.trans_le hLength))

theorem queryBits_length (A : List Bool) {b : ℕ} (idx : Fin b → Fin A.length) :
    (queryBits A idx).length = b * (Nat.clog 2 A.length + 1) := by
  simp [queryBits, bitsMSB, List.map_ofFn, Function.comp_def]

theorem queryBits_prefix (A : List Bool) {b k : ℕ} (hk : k ≤ b)
    (idx : Fin b → Fin A.length) :
    ∃ suffix, queryBits A idx =
      queryBits A (fun j : Fin k => idx (j.castLE hk)) ++ suffix := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  unfold queryBits
  rw [List.ofFn_add (n := k) (m := d), List.flatten_append]
  exact ⟨_, rfl⟩

private theorem query_tape_length_ge (x A : List Bool) {b : ℕ} (idx : Fin b → Fin A.length) :
    b ≤ (x ++ queryBits A idx).length := by
  have hQuery : b ≤ (queryBits A idx).length := by
    rw [queryBits_length]
    exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  exact hQuery.trans (by simp)

theorem acceptsAdviceQueries_cap (prog : List Instr) (A x : List Bool) (b t : ℕ)
    (hA : 0 < A.length) :
    (∃ idx : Fin b → Fin A.length, AcceptsWithin prog (x ++ queryBits A idx) t) ↔
      (∃ idx : Fin (min b t) → Fin A.length, AcceptsWithin prog (x ++ queryBits A idx) t) := by
  by_cases hb : b ≤ t
  · rw [min_eq_left hb]
  have htb : t ≤ b := by omega
  rw [min_eq_right htb]
  constructor
  · rintro ⟨idx, hAccept⟩
    let short : Fin t → Fin A.length := fun j => idx (j.castLE htb)
    obtain ⟨suffix, hSuffix⟩ := queryBits_prefix A htb idx
    have hLong : AcceptsWithin prog ((x ++ queryBits A short) ++ suffix) t := by
      rw [List.append_assoc, ← hSuffix]
      exact hAccept
    exact ⟨short, (acceptsWithin_append_of_length_le prog _ _ t (query_tape_length_ge x A short)).mp hLong⟩
  · rintro ⟨short, hAccept⟩
    let idx (j : Fin b) : Fin A.length :=
      if hj : j.val < t then short ⟨j.val, hj⟩ else ⟨0, hA⟩
    have hShort : (fun j : Fin t => idx (j.castLE htb)) = short := by
      funext j
      simp [idx, j.isLt]
    obtain ⟨suffix, hSuffix⟩ := queryBits_prefix A htb idx
    rw [hShort] at hSuffix
    refine ⟨idx, ?_⟩
    rw [hSuffix, ← List.append_assoc]
    exact (acceptsWithin_append_of_length_le prog _ _ t (query_tape_length_ge x A short)).mpr hAccept

theorem _root_.solution {n : ℕ} (prog : List Instr) (A : List Bool) (b t : ℕ)
    (f : (Fin n → Bool) → Bool) (hA : 0 < A.length) :
    AnramEvaluates prog A b t f ↔ AnramEvaluates prog A (min b t) t f := by
  constructor
  · intro h x
    exact (h x).trans (acceptsAdviceQueries_cap prog A (List.ofFn x) b t hA)
  · intro h x
    exact (h x).trans (acceptsAdviceQueries_cap prog A (List.ofFn x) b t hA).symm

end CNFEncComplexity.ANRAM
