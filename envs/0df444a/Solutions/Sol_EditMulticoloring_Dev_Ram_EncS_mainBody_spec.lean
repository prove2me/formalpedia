-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.EncS.mainBody_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:36:10.261811+00:00
-- url     : https://prove2.me/submissions/b88419cc-21e2-4729-814d-5a30a5242f3a

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_EncS_markEnum_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_EncS_reprW_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_EncS_reprW_word
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_congr
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le
import Theorems.Thm_EditMulticoloring_Dev_Ram_self_mem_visits
import Theorems.Thm_EditMulticoloring_Dev_Ram_upd_eq
import Theorems.Thm_EditMulticoloring_Dev_Ram_upd_ne
import Theorems.Thm_EditMulticoloring_Dev_Ram_visits_length_le

section
-- module Solutions.EditMulticoloring.RamLib2
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# Word utilities on `Cmd` (q379, Part L)

Each utility is a counted loop on registers given as parameters; every spec gives the effect,
the frame (registers outside the written list, memory, cursor, output) and a cost bound of the
form `(a * N + b) * kappa B (RAM.bits M)` under a data bound `… ≤ M`.

* `eqW`     — compare two stored blocks (flag register: 1 iff equal);
* `emitW`   — emit a stored block;
* `readW`   — read `N` input symbols, storing `v - 1`;
* `readRun` — the same, also computing the length of the leading non-EOF run (`runLen`);
* `valueW`  — Horner evaluation `V := q * V + a` (`= EditMulticoloring.Code.value`);
* `digitsW` — `D[off + i] := (V / Q ^ i) % Q` for `i < K`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

section Utils
variable (inp : ℕ → ℕ) (B : ℕ)

/-! ### Equality test -/

/-! ### Emitting a stored block -/

/-! ### Reading input -/

/-! ### Horner evaluation -/

theorem horner_value {q : ℕ} (w : Word q) (g : ℕ → ℕ) (hg : ∀ i (h : i < w.length), g i = (w[i]).val) :
    horner q g w.length = value w := by
  have key : ∀ k ≤ w.length, horner q g k = (w.take k).foldl (fun a b => q * a + b.val) 0 := by
    intro k hk
    induction k with
    | zero => simp [horner]
    | succ k ih =>
      have ht : w.take (k + 1) = w.take k ++ [w[k]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (show k < w.length by omega)]; rfl
      rw [horner, ih (by omega), ht, List.foldl_append]
      simp [hg k (by omega)]
  rw [key _ le_rfl, List.take_length]; rfl

/-! ### Digits -/

end Utils

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamEncodeS1
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-! Verbatim copy of `RamShort.lean` (q379, Part S) in namespace `EditMulticoloring.Dev.Ram.EncS`:
the original clashes with `RamColor` on the names `value_lt` and `visBound`, so the two chains
cannot be imported together; the encoder uses this copy. -/

/-!
# Short table, part 1: words, values, representations, greedy (q379, Part S)

* `value_cons`, `value_lt`, `value_inj` — `value` is a bijection from words of length `l`
  onto `[0, q^l)`;
* `repr_length`, `repr_getElem`, `value_repr`, `repr_value` — `Code.repr q l` is its inverse;
* `words_eq` — `words q l = (List.range (q^l)).map (Code.repr q l)`;
* `greedy` facts: sublist of the input, no duplicates, lengths;
* the RAM routine `reprW` writing the digits of a number (`repr`) into an array.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram.EncS

open EditMulticoloring.Code

/-! ## `value` -/

/-! ## `repr` -/

theorem repr_eq_map {q : ℕ} (hq : 0 < q) (l N : ℕ) :
    Code.repr q l N = (List.range l).map (fun i => (⟨(N / q ^ (l - 1 - i)) % q, Nat.mod_lt _ hq⟩ : Fin q)) := by
  unfold Code.repr
  rw [← List.filterMap_eq_map]
  apply List.filterMap_congr
  intro i _
  simp [Nat.mod_lt _ hq]

theorem repr_length {q : ℕ} (hq : 0 < q) (l N : ℕ) : (Code.repr q l N).length = l := by
  rw [repr_eq_map hq]; simp

theorem repr_getElem {q : ℕ} (hq : 0 < q) (l N i : ℕ) (hi : i < (Code.repr q l N).length) :
    ((Code.repr q l N)[i]).val = (N / q ^ (l - 1 - i)) % q := by
  simp only [repr_eq_map hq, List.getElem_map, List.getElem_range]

/-- The digit Horner identity: `horner` of the first `k` digits is `N / q^(l-k)`. -/
theorem horner_digits (q l N : ℕ) (hN : N < q ^ l) :
    ∀ k ≤ l, horner q (fun i => (N / q ^ (l - 1 - i)) % q) k = N / q ^ (l - k) := by
  intro k hk
  induction k with
  | zero =>
    simp only [horner, Nat.sub_zero]
    exact (Nat.div_eq_of_lt hN).symm
  | succ k ih =>
    simp only [horner]
    rw [ih (by omega)]
    have e : l - k = (l - 1 - k) + 1 := by omega
    have e2 : l - (k + 1) = l - 1 - k := by omega
    rw [e, e2, pow_succ, ← Nat.div_div_eq_div_mul]
    exact Nat.div_add_mod _ _

theorem value_repr {q : ℕ} (hq : 0 < q) (l N : ℕ) (hN : N < q ^ l) : value (Code.repr q l N) = N := by
  rw [← horner_value (Code.repr q l N) (fun i => (N / q ^ (l - 1 - i)) % q)
    (fun i h => (repr_getElem hq l N i h).symm), repr_length hq, horner_digits q l N hN l le_rfl]
  simp

/-! ## `words` -/

/-! ## `greedy` -/

theorem foldl_greedyStep_sublist {q : ℕ} (t : ℕ) (xs : List (Word q)) :
    ∀ acc : List (Word q), ∃ l, l.Sublist xs ∧ xs.foldl (greedyStep t) acc = acc ++ l := by
  induction xs with
  | nil => intro acc; exact ⟨[], List.Sublist.slnil, by simp⟩
  | cons x xs ih =>
    intro acc
    rw [List.foldl_cons]
    by_cases h : acc.any (fun z => decide (x ∈ ball (2 * t) z))
    · rw [show greedyStep t acc x = acc by simp [greedyStep, h]]
      obtain ⟨l, hl, he⟩ := ih acc
      exact ⟨l, hl.cons x, he⟩
    · rw [show greedyStep t acc x = acc ++ [x] by simp only [greedyStep, h]; simp]
      obtain ⟨l, hl, he⟩ := ih (acc ++ [x])
      exact ⟨x :: l, hl.cons_cons x, by rw [he]; simp⟩

/-! ## Writing the digits of a number -/

end EditMulticoloring.Dev.Ram.EncS
end

section
-- module Solutions.EditMulticoloring.RamEncodeS2
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# Short table, part 2: marking a ball (q379, Part S)

`markBody q r a` is the enumerator body: if the visited word has length `ρ` (register `r`),
set `MARK[value w] := 1` (array id in register `r + 7`, equal to `a + 1`).
`markEnum_spec`: running the enumerator of depth `2t` with this body on a word `x` of length `ρ`
turns the mark predicate "in a ball around `chosen`" into "in a ball around `chosen ++ [x]`".

Layout (relative to `r`, `a`): registers `r` = ρ, `r+5`, `r+9` scratch, `r+7` = `a+1`,
`r+20 .. r+28` the `valueW` block, `r+30 ..` the enumerator (`shortCfg r a = ⟨r+30, a+3⟩`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram.EncS

open EditMulticoloring.Code

section Mark
variable (inp : ℕ → ℕ) (B : ℕ)

theorem mem_ball_iff_visits {q : ℕ} (s : ℕ) (x u : Word q) : u ∈ ball s x ↔ u ∈ visits s x := by
  simp [ball, visits]

end Mark

end EditMulticoloring.Dev.Ram.EncS
end

section
-- module Solutions.EditMulticoloring.RamEncodeS3
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# Short table, part 3: one step of the greedy scan (q379, Part S)

`mainBody q t r a` processes the word `x = repr q ρ v` (`v` in register `r + 3`): if
`MARK[v] = 0` it appends `v` to the table (`T[cnt] := v`, `INV[v] := cnt + 1`, `cnt += 1`),
writes `x` into the enumerator's input buffer and marks the ball of radius `2t` around `x`.
`mainBody_spec`: the invariant `SInv` follows one step of `greedy` (`greedyStep`).

Registers (relative to `r`): `r` = ρ, `r+1` = q^ρ, `r+2` = cnt, `r+3` = v, `r+4` loop scratch,
`r+5`, `r+9` scratch, `r+6 r+7 r+8` = the array ids `a` (T), `a+1` (MARK), `a+2` (INV),
`r+10 .. r+17` the `reprW` block, `r+20 .. r+28` the `valueW` block, `r+30 .. r+48+6t` the
enumerator; arrays `a+3 .. a+4+2t` belong to the enumerator.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram.EncS

open EditMulticoloring.Code

theorem greedyStep_of_mem {q : ℕ} (t : ℕ) (chosen : List (Word q)) (x : Word q)
    (h : ∃ z ∈ chosen, x ∈ ball (2 * t) z) : greedyStep t chosen x = chosen := by
  unfold greedyStep
  rw [if_pos]; simpa [List.any_eq_true] using h

theorem greedyStep_of_not_mem {q : ℕ} (t : ℕ) (chosen : List (Word q)) (x : Word q)
    (h : ¬ ∃ z ∈ chosen, x ∈ ball (2 * t) z) : greedyStep t chosen x = chosen ++ [x] := by
  unfold greedyStep
  rw [if_neg]; simpa [List.any_eq_true] using h

theorem foldl_greedyStep_length_le {q : ℕ} (t ρ k : ℕ) :
    (((List.range k).map (Code.repr q ρ)).foldl (greedyStep t) []).length ≤ k := by
  obtain ⟨l, hl, he⟩ := foldl_greedyStep_sublist t ((List.range k).map (Code.repr q ρ)) []
  rw [he, List.nil_append]
  simpa using hl.length_le

section Main
variable (inp : ℕ → ℕ) (B : ℕ)

set_option maxHeartbeats 1000000 in
theorem mainBody_spec_oai {q : ℕ} (hq : 0 < q) (t r a ρ : ℕ) (st0 : HS) (k : ℕ) (hk : k < q ^ ρ)
    (chosen : List (Word q))
    (hch : chosen = ((List.range k).map (Code.repr q ρ)).foldl (greedyStep t) [])
    (st : HS) (hS : SInv t r a ρ st0 chosen st) (hj : st.regs (r + 3) = k) :
    ((mainBody q t r a).exec inp st).regs (r + 3) = k ∧
    SInv t r a ρ st0 (greedyStep t chosen (Code.repr q ρ k))
      ((((mainBody q t r a).exec inp st).setR (r + 4) 1).setR (r + 3) (k + 1)) ∧
    (mainBody q t r a).cost inp B st ≤ mainD B q t ρ a := by
  obtain ⟨e0, e1, e2, e6, e7, e8, hT, hMk, hINV, hfr, hfa, hcur, hout⟩ := hS
  set M := shortM q t ρ a with hMdef
  set κ := kappa B (RAM.bits M) with hκ
  set x := Code.repr q ρ k with hxdef
  have hxl : x.length = ρ := repr_length hq ρ k
  have hvx : value x = k := value_repr hq ρ k hk
  have hcl : chosen.length ≤ k := hch ▸ foldl_greedyStep_length_le t ρ k
  set c := chosen.length with hc
  have hqρ : 1 ≤ q ^ ρ := Nat.one_le_pow _ _ hq
  have K0 := kappa_bits_le B (a := 0) (M := M) (by omega)
  have hmark : st.arr (a + 1) k = if ∃ z ∈ chosen, x ∈ ball (2 * t) z then 1 else 0 := hMk k hk
  set s1 := st.setR (r + 5) (st.arr (a + 1) k) with hs1
  have hex1 : (ald (r + 5) (r + 7) (r + 3)).exec inp st = s1 := by
    simp [exec_ald, e7, hj, hs1]
  have hcost1 : (ald (r + 5) (r + 7) (r + 3)).cost inp B st ≤ κ := by
    rw [cost_ald, e7, hj]
    refine kappa_bits_le B ?_
    rw [hmark, hMdef, shortM]; split_ifs <;> omega
  by_cases hm : ∃ z ∈ chosen, x ∈ ball (2 * t) z
  · -- already marked: skip
    have hex : (mainBody q t r a).exec inp st = s1 := by
      show (Cmd.ifz (r + 5) _ .skip).exec inp ((ald (r + 5) (r + 7) (r + 3)).exec inp st) = _
      rw [hex1, exec_ifz, if_neg (by simp [hs1, hmark, hm])]; rfl
    rw [greedyStep_of_mem t chosen x hm, hex]
    refine ⟨by simp (disch := omega) [hs1, upd_ne, hj], ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp (disch := omega) [hs1, upd_ne, e0]
    · simp (disch := omega) [hs1, upd_ne, e1]
    · simp (disch := omega) [hs1, upd_ne, e2, hc]
    · simp (disch := omega) [hs1, upd_ne, e6]
    · simp (disch := omega) [hs1, upd_ne, e7]
    · simp (disch := omega) [hs1, upd_ne, e8]
    · intro i h; simpa [hs1] using hT i h
    · intro u hu; simpa [hs1] using hMk u hu
    · intro u hu; simpa [hs1] using hINV u hu
    · intro r' h; simp (disch := omega) [hs1, upd_ne]; exact hfr r' h
    · intro y i h; simpa [hs1] using hfa y i h
    · simp [hs1, hcur]
    · simp [hs1, hout]
    · have hc' : (mainBody q t r a).cost inp B st = (ald (r + 5) (r + 7) (r + 3)).cost inp B st +
          (kappa B (RAM.bits (s1.regs (r + 5))) + 0) := by
        show _ + (Cmd.ifz (r + 5) _ .skip).cost inp B ((ald (r + 5) (r + 7) (r + 3)).exec inp st) = _
        rw [hex1, cost_ifz, if_neg (by simp [hs1, hmark, hm])]; rfl
      rw [hc']
      have : kappa B (RAM.bits (s1.regs (r + 5))) ≤ κ := by
        refine kappa_bits_le B ?_
        simp only [hs1, HS.setR_regs, Function.update_self, hmark, hMdef, shortM]
        split_ifs <;> omega
      unfold mainD
      rw [← hMdef, ← hκ]
      have : 2 * κ ≤ (7 * ρ + 20) * κ := Nat.mul_le_mul_right _ (by omega)
      omega
  · -- a new word
    have hxnot : x ∉ chosen := fun h => hm ⟨x, h, (mem_ball_iff_visits _ _ _).mpr (self_mem_visits _ _)⟩
    have hm0 : st.arr (a + 1) k = 0 := by rw [hmark, if_neg hm]
    rw [greedyStep_of_not_mem t chosen x hm]
    have d1 : s1.regs (r + 5) = 0 := by simp [hs1, hm0]
    set s2 := (chooseA q t r a).exec inp s1 with hs2
    have r2 : ∀ r', r' ≠ r + 2 → r' ≠ r + 5 → r' ≠ r + 9 → (r' < r + 10 ∨ r + 15 ≤ r') →
        s2.regs r' = st.regs r' := by
      intro r' h1 h2 h3 h4
      simp (disch := omega) [hs2, hs1, chooseA, upd_ne]
    have v2 : s2.regs (r + 2) = c + 1 := by
      simp (disch := omega) [hs2, hs1, chooseA, upd_ne, e2]
    have v10 : s2.regs (r + 10) = a + 4 + 2 * t := by
      simp (disch := omega) [hs2, hs1, chooseA, upd_ne, shortCfg] <;> omega
    have v11 : s2.regs (r + 11) = k := by simp (disch := omega) [hs2, hs1, chooseA, upd_ne, hj]
    have v12 : s2.regs (r + 12) = q ^ ρ := by simp (disch := omega) [hs2, hs1, chooseA, upd_ne, e1]
    have v13 : s2.regs (r + 13) = ρ := by simp (disch := omega) [hs2, hs1, chooseA, upd_ne, e0]
    have v14 : s2.regs (r + 14) = q := by simp (disch := omega) [hs2, hs1, chooseA, upd_ne]
    have a2 : ∀ y i, s2.arr y i =
        if y = a + 2 ∧ i = k then c + 1 else if y = a ∧ i = c then k else st.arr y i := by
      intro y i
      simp (disch := omega) [hs2, hs1, chooseA, upd_ne, e2, e6, e8, hj]
    have c2 : s2.cur = st.cur := by simp [hs2, hs1, chooseA]
    have o2 : s2.out = st.out := by simp [hs2, hs1, chooseA]
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := reprW_spec inp B (r + 10) s2 M (by rw [v14]; exact hq)
      (by rw [v12, v13, v14])
      (by rw [v10, v11, v13, v14, hMdef, shortM]; omega)
    have hw3 := reprW_word inp hq (r + 10) s2 v14 (by rw [v12, v13])
    rw [v10, v13, v11] at hw3
    rw [v10, v13] at p2
    rw [v13] at p6
    set s3 := (reprW (r + 10)).exec inp s2 with hs3
    set L := (shortCfg r a).lenR (2 * t) with hL
    have hLv : L = r + 48 + 6 * t := by simp [hL, shortCfg] <;> omega
    set s4 := (cp L r).exec inp s3 with hs4
    have r34 : ∀ r', r' ≠ L → s4.regs r' = s3.regs r' := by
      intro r' h; simp [hs4, upd_ne h]
    have a4 : ∀ y i, s4.arr y i = s3.arr y i := by intro y i; simp [hs4]
    have e4r : s4.regs r = ρ := by
      rw [r34 r (by omega), p3 r (by omega) (by omega) (by omega) (by omega),
        r2 r (by omega) (by omega) (by omega) (by omega), e0]
    have e47 : s4.regs (r + 7) = a + 1 := by
      rw [r34 _ (by omega), p3 _ (by omega) (by omega) (by omega) (by omega),
        r2 _ (by omega) (by omega) (by omega) (by omega), e7]
    have hbuf : (shortCfg r a).buf (2 * t) = a + 4 + 2 * t := by simp [shortCfg] <;> omega
    obtain ⟨⟨n1, n2, n3, n4, n5, n6⟩, ncost⟩ := markEnum_spec inp B hq t r a ρ chosen s4 e4r e47 x hxl s4
      ⟨fun u hu => by
        rw [a4, p2 _ _ (by omega), a2, if_neg (by omega), if_neg (by omega), hMk u hu]
        simp, fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl⟩
      (by rw [← hL, hxl]; simp [hs4, e0]; rw [p3 r (by omega) (by omega) (by omega) (by omega),
        r2 r (by omega) (by omega) (by omega) (by omega), e0])
      (by rw [hbuf]; exact hw3.congr (fun i _ => a4 _ _))
    set s5 := (enumScripts q (2 * t) (shortCfg r a) (markBody q r a)).exec inp s4 with hs5
    have hex : (mainBody q t r a).exec inp st = s5 := by
      show (Cmd.ifz (r + 5) _ .skip).exec inp ((ald (r + 5) (r + 7) (r + 3)).exec inp st) = _
      rw [hex1, exec_ifz, if_pos d1]; rfl
    -- register chain: s5 = st on the client registers kept by every phase
    have R : ∀ r', r' ≠ r + 2 → r' ≠ r + 5 → r' ≠ r + 9 → (r' < r + 10 ∨ r + 49 + 6 * t ≤ r') →
        s5.regs r' = st.regs r' := by
      intro r' h1 h2 h3 h4
      have : s5.regs r' = s4.regs r' := by
        rcases h4 with h4 | h4
        · exact n2 r' (by omega) h2 h3
        · exact n3 r' h4
      rw [this, r34 r' (by omega), p3 r' (by omega) (by omega) (by omega) (by omega),
        r2 r' h1 h2 h3 (by omega)]
    have A : ∀ y i, y ≠ a + 1 → (y < a + 3 ∨ a + 5 + 2 * t ≤ y) → s5.arr y i =
        if y = a + 2 ∧ i = k then c + 1 else if y = a ∧ i = c then k else st.arr y i := by
      intro y i h1 h2
      rw [n4 y i h1 h2, a4, p2 _ _ (by omega), a2]
    rw [hex]
    refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [R _ (by omega) (by omega) (by omega) (by omega), hj]
    · simp (disch := omega) only [HS.setR_regs, upd_ne]; rw [R r (by omega) (by omega) (by omega) (by omega), e0]
    · simp (disch := omega) only [HS.setR_regs, upd_ne]; rw [R _ (by omega) (by omega) (by omega) (by omega), e1]
    · simp (disch := omega) only [HS.setR_regs, upd_ne]
      rw [n2 _ (by omega) (by omega) (by omega), r34 _ (by omega),
        p3 _ (by omega) (by omega) (by omega) (by omega), v2]
      simp [hc]
    · simp (disch := omega) only [HS.setR_regs, upd_ne]; rw [R _ (by omega) (by omega) (by omega) (by omega), e6]
    · simp (disch := omega) only [HS.setR_regs, upd_ne]; rw [R _ (by omega) (by omega) (by omega) (by omega), e7]
    · simp (disch := omega) only [HS.setR_regs, upd_ne]; rw [R _ (by omega) (by omega) (by omega) (by omega), e8]
    · intro i hi
      simp only [HS.setR_arr]
      rw [A a i (by omega) (by omega), if_neg (by omega)]
      simp only [List.length_append, List.length_singleton] at hi
      by_cases hic : i = c
      · rw [if_pos ⟨rfl, hic⟩]
        subst hic
        rw [List.getElem_append_right (by omega)]
        simp [hvx]
      · rw [if_neg (fun h => hic h.2), List.getElem_append_left (by omega)]
        exact hT i (by omega)
    · intro u hu
      simp only [HS.setR_arr]
      rw [n1 u hu]
      simp
    · intro u hu
      simp only [HS.setR_arr]
      rw [A (a + 2) u (by omega) (by omega),
        show (if a + 2 = a ∧ u = c then k else st.arr (a + 2) u) = st.arr (a + 2) u from
          if_neg (by omega)]
      by_cases huk : u = k
      · subst huk
        rw [if_pos ⟨rfl, rfl⟩, ← hxdef, if_pos (by simp), List.idxOf_append_of_notMem hxnot]
        simp [hc]
      · rw [if_neg (fun h => huk h.2), hINV u hu]
        have hne : Code.repr q ρ u ≠ x := by
          intro h; apply huk; rw [← value_repr hq ρ u hu, h, hvx]
        by_cases hin : Code.repr q ρ u ∈ chosen
        · rw [if_pos hin, if_pos (List.mem_append_left _ hin), List.idxOf_append_of_mem hin]
        · rw [if_neg hin, if_neg (by simp [hin, hne])]
    · intro r' h
      simp (disch := omega) only [HS.setR_regs, upd_ne]
      rw [R r' (by omega) (by omega) (by omega) (by omega)]; exact hfr r' h
    · intro y i h
      simp only [HS.setR_arr]
      rw [A y i (by omega) (by omega), if_neg (by omega), if_neg (by omega)]; exact hfa y i h
    · simp only [HS.setR_cur]; rw [n5]; simp [hs4, p4, c2, hcur]
    · simp only [HS.setR_out]; rw [n6]; simp [hs4, p5, o2, hout]
    · have hc' : (mainBody q t r a).cost inp B st = (ald (r + 5) (r + 7) (r + 3)).cost inp B st +
          (kappa B (RAM.bits (s1.regs (r + 5))) + ((chooseA q t r a).cost inp B s1 +
          ((reprW (r + 10)).cost inp B s2 + ((cp L r).cost inp B s3 +
          (enumScripts q (2 * t) (shortCfg r a) (markBody q r a)).cost inp B s4)))) := by
        show _ + (Cmd.ifz (r + 5) _ .skip).cost inp B ((ald (r + 5) (r + 7) (r + 3)).exec inp st) = _
        rw [hex1, cost_ifz, if_pos d1]; rfl
      rw [hc', d1]
      have cA : (chooseA q t r a).cost inp B s1 ≤ 10 * κ := by
        simp (disch := omega) only [chooseA, cost_seqs_cons, cost_seqs_nil, exec_seqs_cons,
          cost_ast, cost_lit, cost_ar, cost_cp, exec_ast, exec_lit, exec_ar, exec_cp, HS.setR_regs,
          HS.store_regs, upd_ne, upd_eq, hs1, e0, e1, e2, e6, e8, hj, arith_add]
        have hb := hbuf
        have hKM : ∀ v, v ≤ M → kappa B (RAM.bits v) ≤ κ := fun v hv => kappa_bits_le B hv
        have := hKM (a + c + k) (by rw [hMdef, shortM]; omega)
        have := hKM 1 (by rw [hMdef, shortM]; omega)
        have := hKM (c + 1) (by rw [hMdef, shortM]; omega)
        have := hKM (a + 2 + k + (c + 1)) (by rw [hMdef, shortM]; omega)
        have := hKM ((shortCfg r a).buf (2 * t)) (by rw [hb, hMdef, shortM]; omega)
        have := hKM k (by rw [hMdef, shortM]; omega)
        have := hKM (q ^ ρ) (by rw [hMdef, shortM]; omega)
        have := hKM ρ (by rw [hMdef, shortM]; omega)
        have := hKM q (by rw [hMdef, shortM]; omega)
        omega
      have cC : (cp L r).cost inp B s3 ≤ κ := by
        rw [cost_cp, p3 r (by omega) (by omega) (by omega) (by omega),
          r2 r (by omega) (by omega) (by omega) (by omega), e0]
        exact kappa_bits_le B (by rw [hMdef, shortM]; omega)
      have hV : (visits (2 * t) x).length ≤ visBound q t ρ := by
        have := visits_length_le (2 * t) x
        rw [hxl] at this; exact this
      have cE : (enumScripts q (2 * t) (shortCfg r a) (markBody q r a)).cost inp B s4 ≤
          visBound q t ρ * ((7 * ρ + 20) * κ + (shortCfg 0 a).enumE B q ρ (2 * t)) :=
        ncost.trans (Nat.mul_le_mul_right _ hV)
      unfold mainD
      rw [← hMdef, ← hκ]
      have K0' : kappa B (RAM.bits 0) ≤ κ := K0
      have p6' : (reprW (r + 10)).cost inp B s2 ≤ (7 * ρ + 3) * κ := p6
      have : (7 * ρ + 20) * κ = κ + κ + 10 * κ + (7 * ρ + 3) * κ + κ + 4 * κ := by ring
      omega

end Main

end EditMulticoloring.Dev.Ram.EncS
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.EncS.mainBody_spec_oai := @EditMulticoloring.Dev.Ram.EncS.mainBody_spec_oai
