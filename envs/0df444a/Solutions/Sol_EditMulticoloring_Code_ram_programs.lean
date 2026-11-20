-- Prove2me | solution 1 for EditMulticoloring.Code.ram_programs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:05.999668+00:00
-- url     : https://prove2.me/submissions/10a76721-d60f-4c3f-8e61-a008e6d0f1b8

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Code_encoder_redundancy
import Theorems.Thm_EditMulticoloring_Code_short_edit_code
import Theorems.Thm_EditMulticoloring_Dev_Ram_decEnum_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_decPre_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_encProg_spec

section
-- module Solutions.EditMulticoloring.RamLib
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# Program-proof library for `Cmd` (q379, Part L)

* `simp` lemmas for `Cmd.exec` / `Cmd.cost` of every constructor and convenience constructor;
* `HS.setR` (register update) and `HS.arr` lemmas;
* syntactic frames: `Cmd.wregs` (registers possibly written), `Cmd.reads`, `Cmd.emits`, `Cmd.stores`;
* monotonicity of `kappa` and `RAM.bits`;
* the general loop lemma `loop_spec`, the counted for-loop `forLoop` with `forLoop_spec`
  (invariant + cost) and its list-fold form `forLoop_fold`;
* `copyW`, a word copy between (array, offset) places.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## States -/

/-! ## Small rewriting helpers (use with `simp (disch := omega)`) -/

theorem upd_ne {f : ℕ → ℕ} {a b v : ℕ} (h : b ≠ a) : Function.update f a v b = f b :=
  Function.update_of_ne h v f
theorem upd_eq {f : ℕ → ℕ} {a b v : ℕ} (h : b = a) : Function.update f a v b = v := by
  subst h; simp

/-! ## `exec` and `cost` of the constructors -/

section ExecCost
variable (inp : ℕ → ℕ) (B : ℕ)

theorem exec_loop (a : ℕ) (c : Cmd) (s : HS) :
    (Cmd.loop a c).exec inp s = (c.exec inp)^[s.regs a] s := rfl

end ExecCost

/-! ## Monotonicity of the charges -/

theorem bits_mono {a b : ℕ} (h : a ≤ b) : RAM.bits a ≤ RAM.bits b := by
  unfold RAM.bits
  have := Nat.log_mono_right (b := 2) h
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  omega

theorem one_le_bits (a : ℕ) : 1 ≤ RAM.bits a := by unfold RAM.bits; omega

theorem kappa_mono {B B' W W' : ℕ} (hB : B ≤ B') (hW : W ≤ W') : kappa B W ≤ kappa B' W' := by
  unfold kappa
  have : (W + 2) ^ 2 ≤ (W' + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

theorem kappa_mono_right (B : ℕ) {W W' : ℕ} (hW : W ≤ W') : kappa B W ≤ kappa B W' :=
  kappa_mono le_rfl hW

/-- The standard way to bound a charge: the data is at most `M`. -/
theorem kappa_bits_le (B : ℕ) {a M : ℕ} (h : a ≤ M) : kappa B (RAM.bits a) ≤ kappa B (RAM.bits M) :=
  kappa_mono_right B (bits_mono h)

theorem kappa_zero_le (B M : ℕ) : kappa B 0 ≤ kappa B (RAM.bits M) :=
  kappa_mono_right B (Nat.zero_le _)

/-! ## Syntactic frames -/

section Frames
variable (inp : ℕ → ℕ)

theorem iterate_induct {f : HS → HS} (P : HS → Prop) (h : ∀ s, P s → P (f s)) :
    ∀ (n : ℕ) (s : HS), P s → P (f^[n] s)
  | 0, _, hs => hs
  | n + 1, s, hs => by rw [Function.iterate_succ_apply]; exact iterate_induct P h n _ (h _ hs)

theorem exec_cur_of_reads (c : Cmd) (h : c.reads = false) (s : HS) :
    (c.exec inp s).cur = s.cur := by
  induction c generalizing s with
  | prim p => cases p <;> simp_all [Cmd.reads, Cmd.exec, Prim.exec]
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [Cmd.reads, Bool.or_eq_false_iff] at h
    simp [ih₁ h.1, ih₂ h.2]
  | ifz a c₁ c₂ ih₁ ih₂ =>
    simp only [Cmd.reads, Bool.or_eq_false_iff] at h
    simp only [exec_ifz]; split_ifs
    · exact ih₁ h.1 s
    · exact ih₂ h.2 s
  | loop a c ih =>
    simp only [Cmd.reads] at h
    rw [exec_loop]
    exact iterate_induct (fun t => t.cur = s.cur) (fun t ht => (ih h t).trans ht) _ _ rfl
  | skip => rfl

end Frames

/-! ## Loops -/

section Loops
variable (inp : ℕ → ℕ) (B : ℕ)

/-- `loop a c`, with an invariant indexed by the number of completed iterations, and a
per-iteration cost bound. -/
theorem loop_spec (a : ℕ) (c : Cmd) (s : HS) (P : ℕ → HS → Prop) (C : ℕ → ℕ)
    (h0 : P 0 s)
    (hstep : ∀ k < s.regs a, ∀ st, P k st → P (k + 1) (c.exec inp st) ∧ c.cost inp B st ≤ C k) :
    P (s.regs a) ((Cmd.loop a c).exec inp s) ∧
    (Cmd.loop a c).cost inp B s ≤
      (s.regs a + 2) * kappa B (RAM.bits (s.regs a)) + ∑ k ∈ Finset.range (s.regs a), C k := by
  set N := s.regs a with hN
  have key : ∀ v k st, k + v = N → P k st →
      P N ((c.exec inp)^[v] st) ∧
      loopCost B (c.exec inp) (c.cost inp B) v st ≤
        (v + 1) * kappa B (RAM.bits N) + ∑ j ∈ Finset.range v, C (k + j) := by
    intro v
    induction v with
    | zero =>
      intro k st hk hP
      simp only [Nat.add_zero] at hk
      subst hk
      refine ⟨hP, ?_⟩
      simp only [loopCost, Finset.range_zero, Finset.sum_empty, zero_add, one_mul, add_zero]
      exact kappa_zero_le B _
    | succ v ih =>
      intro k st hk hP
      have hkN : k < N := by omega
      obtain ⟨hP1, hc⟩ := hstep k hkN st hP
      obtain ⟨hP2, hc2⟩ := ih (k + 1) (c.exec inp st) (by omega) hP1
      refine ⟨by rw [Function.iterate_succ_apply]; exact hP2, ?_⟩
      simp only [loopCost]
      have hκ : kappa B (RAM.bits (v + 1)) ≤ kappa B (RAM.bits N) := kappa_bits_le B (by omega)
      rw [Finset.sum_range_succ']
      have : ∑ j ∈ Finset.range v, C (k + 1 + j) = ∑ j ∈ Finset.range v, C (k + (j + 1)) := by
        apply Finset.sum_congr rfl; intro j _; congr 1; omega
      rw [this] at hc2
      simp only [Nat.add_zero] at *
      nlinarith
  obtain ⟨h1, h2⟩ := key N 0 s (by omega) h0
  refine ⟨by rw [exec_loop]; exact h1, ?_⟩
  simp only [Cmd.cost]
  simp only [zero_add] at h2
  rw [← hN]
  nlinarith

/-- The for-loop lemma: invariant `P k` after `k` iterations (the counter register `i` holds
`k` at the start of iteration `k`, the body must keep it), and cost. -/
theorem forLoop_spec (i n one : ℕ) (body : Cmd) (s : HS) (hni : n ≠ i) (hio : i ≠ one)
    (P : ℕ → HS → Prop) (C : ℕ → ℕ)
    (h0 : P 0 (s.setR i 0))
    (hstep : ∀ k < s.regs n, ∀ st, P k st → st.regs i = k →
      (body.exec inp st).regs i = k ∧
      P (k + 1) (((body.exec inp st).setR one 1).setR i (k + 1)) ∧
      body.cost inp B st ≤ C k) :
    P (s.regs n) ((forLoop i n one body).exec inp s) ∧
    (forLoop i n one body).cost inp B s ≤
      3 * (s.regs n + 1) * kappa B (RAM.bits (s.regs n)) + ∑ k ∈ Finset.range (s.regs n), C k := by
  set N := s.regs n with hN
  have hN' : (s.setR i 0).regs n = N := by simp [hni, hN]
  have L := loop_spec inp B n (.seq body (.seq (lit one 1) (ar .add i i one))) (s.setR i 0)
    (fun k st => P k st ∧ st.regs i = k) (fun k => C k + 2 * kappa B (RAM.bits N))
    ⟨h0, by simp⟩ (by
      intro k hk st ⟨hP, hi⟩
      rw [hN'] at hk
      obtain ⟨hb1, hb2, hb3⟩ := hstep k hk st hP hi
      have hset : (Function.update (body.exec inp st).regs one 1) i +
          (Function.update (body.exec inp st).regs one 1) one = k + 1 := by
        simp [hio, hb1]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp only [exec_seq, exec_lit, exec_ar, arith_add, HS.setR_regs]
        rw [hset]; exact hb2
      · simp [hio, hb1]
      · simp only [cost_seq, cost_lit, cost_ar, exec_lit, HS.setR_regs]
        rw [Function.update_apply, if_neg hio, hb1, Function.update_apply, if_pos rfl]
        have e1 : kappa B (RAM.bits 1) ≤ kappa B (RAM.bits N) := kappa_bits_le B (by omega)
        have e2 : kappa B (RAM.bits (k + 1)) ≤ kappa B (RAM.bits N) := kappa_bits_le B (by omega)
        omega)
  rw [hN'] at L
  obtain ⟨⟨L1, -⟩, L2⟩ := L
  refine ⟨L1, ?_⟩
  simp only [forLoop, cost_seq, cost_lit]
  rw [Finset.sum_add_distrib] at L2
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at L2
  have e0 : kappa B (RAM.bits 0) ≤ kappa B (RAM.bits N) := kappa_bits_le B (by omega)
  simp only [exec_lit] at *
  rw [hN'] at *
  nlinarith

end Loops

/-! ## Words stored in arrays -/

theorem WordAt.congr {q : ℕ} {s s' : HS} {x off : ℕ} {w : Word q} (h : WordAt s x off w)
    (h' : ∀ i < w.length, s'.arr x (off + i) = s.arr x (off + i)) : WordAt s' x off w := by
  intro i hi; rw [h' i hi, h i hi]

theorem WordAt.lt {q : ℕ} {s : HS} {x off : ℕ} {w : Word q} (h : WordAt s x off w) :
    ∀ i < w.length, s.arr x (off + i) < q := by
  intro i hi; rw [h i hi]; exact (w[i]).isLt

/-! ## Copying a block of cells -/

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamEnum
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# The scripts enumerator (q379, Part L)

`enumScripts q s cfg body` runs `body` once per element of `visits s x` (in list order), each
time with the visited word in array `cfg.vis` (offset 0) and its length in register `cfg.VL`.
Main theorem: `enumScripts_spec` (RamEnum3.lean); level induction in RamEnum2.lean.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## The visit list -/

theorem insW_length {q : ℕ} (x : Word q) (i : ℕ) (a : Fin q) (hi : i ≤ x.length) :
    (insW x i a).length = x.length + 1 := by
  simp [insW]; omega
theorem delW_length {q : ℕ} (x : Word q) (i : ℕ) (hi : i < x.length) :
    (delW x i).length = x.length - 1 := by
  simp [delW]; omega
theorem repW_length {q : ℕ} (x : Word q) (i : ℕ) (a : Fin q) (hi : i < x.length) :
    (repW x i a).length = x.length := by
  simp [repW]; omega

theorem finRange_flatMap {q : ℕ} {β : Type*} (F : Fin q → List β) :
    (List.finRange q).flatMap F = (List.range q).flatMap (finFlat F) := by
  induction q with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ_last, List.range_succ, List.flatMap_append, List.flatMap_append,
      List.flatMap_map]
    rw [ih (fun a => F a.castSucc)]
    congr 1
    · apply List.flatMap_congr
      intro a ha
      have ha' : a < n := List.mem_range.mp ha
      simp [finFlat, ha', Nat.lt_succ_of_lt ha']
    · simp [finFlat, Fin.last]

theorem flatMap_filter_eq {α β : Type*} (l : List α) (p : α → Bool) (F : α → List β) :
    (l.filter p).flatMap F = l.flatMap (fun a => if p a then F a else []) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : p a <;> simp [List.filter_cons, h, ih]

theorem visits_zero {q : ℕ} (x : Word q) : visits 0 x = [x] := by
  simp [visits, scripts]

theorem visits_succ {q : ℕ} (s : ℕ) (x : Word q) :
    visits (s + 1) x = x ::
      ((List.range (x.length + 1)).flatMap (fun i =>
          (List.range q).flatMap (finFlat fun a => visits s (insW x i a))) ++
        (List.range x.length).flatMap (fun i => visits s (delW x i)) ++
        (List.range x.length).flatMap (fun i =>
          (List.range q).flatMap (finFlat fun a =>
            if x[i]? = some a then [] else visits s (repW x i a)))) := by
  simp only [visits, scripts, List.map_cons, availableEdits, List.flatMap_append, List.map_append,
    List.map_flatMap]
  congr 1
  congr 1
  congr 1
  · rw [List.flatMap_assoc]
    apply List.flatMap_congr
    intro i hi
    have hi' : i ≤ x.length := Nat.lt_succ_iff.mp (List.mem_range.mp hi)
    rw [List.flatMap_map, ← finRange_flatMap]
    apply List.flatMap_congr
    intro a _
    simp [applyEdit, hi', insW, List.map_map]
  · rw [List.flatMap_map]
    apply List.flatMap_congr
    intro i hi
    have hi' : i < x.length := List.mem_range.mp hi
    simp [applyEdit, hi', delW, List.map_map]
  · rw [List.flatMap_assoc]
    apply List.flatMap_congr
    intro i hi
    have hi' : i < x.length := List.mem_range.mp hi
    rw [List.flatMap_map, flatMap_filter_eq, ← finRange_flatMap]
    apply List.flatMap_congr
    intro a _
    by_cases ha : x[i]? = some a
    · simp [ha]
    · have ha2 : ¬ x[i] = a := fun h => ha (by rw [List.getElem?_eq_getElem hi', h])
      simp [applyEdit, hi', ha, ha2, repW, List.map_map]

/-! ## Configuration -/

/-! ## Specs of the pieces -/

end EditMulticoloring.Dev.Ram
end

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

theorem emitW_spec (r : ℕ) (s : HS) (V M : ℕ)
    (hV : ∀ i < s.regs (r + 2), s.arr (s.regs r) (s.regs (r + 1) + i) ≤ V)
    (hM : s.regs r + s.regs (r + 1) + s.regs (r + 2) + V + s.out.length ≤ M) :
    ((emitW r).exec inp s).out =
      s.out ++ (List.range (s.regs (r + 2))).map (fun i => s.arr (s.regs r) (s.regs (r + 1) + i)) ∧
    (∀ r', (r' < r + 3 ∨ r + 7 ≤ r') → ((emitW r).exec inp s).regs r' = s.regs r') ∧
    ((emitW r).exec inp s).mem = s.mem ∧
    ((emitW r).exec inp s).cur = s.cur ∧
    (emitW r).cost inp B s ≤ (6 * s.regs (r + 2) + 3) * kappa B (RAM.bits M) := by
  set vX := s.regs r
  set voff := s.regs (r + 1)
  have K := forLoop_spec inp B (r + 3) (r + 2) (r + 6)
    (seqs [ar .add (r + 4) (r + 1) (r + 3), ald (r + 5) r (r + 4), em (r + 5)]) s
    (by omega) (by omega)
    (fun k st => st.out = s.out ++ (List.range k).map (fun i => s.arr vX (voff + i)) ∧
      (∀ r', (r' < r + 3 ∨ r + 7 ≤ r') → st.regs r' = s.regs r') ∧ st.mem = s.mem)
    (fun _ => 3 * kappa B (RAM.bits M))
    ⟨by simp, fun r' h => by simp (disch := omega) [upd_ne], by simp⟩
    (by
      intro k hk st ⟨ho, hr, hm⟩ hj
      have eX : st.regs r = vX := hr r (by omega)
      have eoff : st.regs (r + 1) = voff := hr _ (by omega)
      have hA : st.arr vX (voff + k) = s.arr vX (voff + k) := by simp [HS.arr, hm]
      have hVA := hV k hk
      simp (disch := omega) only [exec_seqs_cons, exec_seqs_nil, exec_ar, exec_ald, exec_em,
        arith_add, HS.setR_regs, HS.setR_arr, HS.setR_mem, HS.setR_out,
        upd_ne, upd_eq, eX, eoff, hj, hA, cost_seqs_cons, cost_seqs_nil, cost_ar,
        cost_ald, cost_em]
      refine ⟨by simp (disch := omega) [upd_ne, hj], ⟨?_, ?_, ?_⟩, ?_⟩
      · simp [ho, List.range_succ]
      · intro r' h
        simp (disch := omega) only [upd_ne, HS.setR_regs]; exact hr r' h
      · simpa using hm
      · have e1 := kappa_bits_le B (a := voff + k) (M := M) (by omega)
        have e2 := kappa_bits_le B (a := vX + (voff + k) + s.arr vX (voff + k)) (M := M) (by omega)
        have e3 := kappa_bits_le B (a := s.arr vX (voff + k) + st.out.length) (M := M)
          (by rw [ho]; simp; omega)
        omega)
  obtain ⟨⟨k1, k2, k3⟩, k4⟩ := K
  have hcur : ((emitW r).exec inp s).cur = s.cur := exec_cur_of_reads inp _ rfl s
  refine ⟨k1, k2, k3, hcur, ?_⟩
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at k4
  have := kappa_bits_le B (a := s.regs (r + 2)) (M := M) (by omega)
  simp only [emitW]
  nlinarith

theorem emitW_word {q : ℕ} (r : ℕ) (s : HS) (w : Word q) (hw : WordAt s (s.regs r) (s.regs (r + 1)) w)
    (hn : s.regs (r + 2) = w.length) :
    ((emitW r).exec inp s).out = s.out ++ w.map (fun a => a.val) := by
  rw [(emitW_spec inp 0 r s q _ (fun i hi => (hw.lt i (by omega)).le) le_rfl).1, hn]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  exact hw i (by simpa using h1)

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
-- module Solutions.EditMulticoloring.RamEnum3
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# The scripts enumerator: main theorem, size bound, toy clients (q379, Part L)

* `enumScripts_spec` — the fold specification of `enumScripts q s cfg body`;
* `visits_length_le` — `(visits s x).length ≤ ∑ i ∈ range (s+1), (2q(|x|+s+1))^i`;
* toy clients `countProg` (count the visited words of length `|x|` other than `x`) and
  `listProg` (store them as a 2-D array, word `j` at offsets `j * S`), both proved.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

theorem EnumCfg.enumE_eq (cfg : EnumCfg) (B q L s : ℕ) :
    cfg.enumE B q L s = 100 * (q + 1) * (L + s + 2) ^ 2 *
      kappa B (RAM.bits (2 * cfg.a0 + 4 * (L + s + q) + 8)) := rfl

/-! ## Size of the visit list -/

theorem flatMap_range_length_le {β : Type*} (G : ℕ → List β) (n V : ℕ)
    (h : ∀ b < n, (G b).length ≤ V) : ((List.range n).flatMap G).length ≤ n * V := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    simp only [List.length_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have := ih (fun b hb => h b (by omega))
    have := h n (by omega)
    rw [Nat.succ_mul]; omega

theorem flatMap_range_length_le_skip {β : Type*} (G : ℕ → List β) (n V c : ℕ) (hc : c < n)
    (h : ∀ b < n, (G b).length ≤ V) (h0 : G c = []) :
    ((List.range n).flatMap G).length ≤ (n - 1) * V := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    simp only [List.length_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | rfl
    · have := ih hc (fun b hb => h b (by omega))
      have := h n (by omega)
      have e : n + 1 - 1 = (n - 1) + 1 := by omega
      rw [e, Nat.succ_mul]; omega
    · have := flatMap_range_length_le G c V (fun b hb => h b (by omega))
      rw [h0, List.length_nil, Nat.add_zero, Nat.add_sub_cancel]; exact this

theorem visits_length_le {q : ℕ} (k : ℕ) (x : Word q) :
    (visits k x).length ≤ ∑ i ∈ Finset.range (k + 1), (2 * q * (x.length + k + 1)) ^ i := by
  induction k generalizing x with
  | zero => simp [visits_zero]
  | succ k ih =>
    set T := 2 * q * (x.length + (k + 1) + 1) with hT
    set V := ∑ i ∈ Finset.range (k + 1), T ^ i with hV
    have hchild : ∀ z : Word q, z.length ≤ x.length + 1 → (visits k z).length ≤ V := by
      intro z hz
      refine (ih z).trans (Finset.sum_le_sum fun i _ => Nat.pow_le_pow_left ?_ i)
      apply Nat.mul_le_mul_left; omega
    rw [visits_succ]
    simp only [List.length_cons, List.length_append]
    have hA := flatMap_range_length_le (fun i =>
        (List.range q).flatMap (finFlat fun b => visits k (insW x i b))) (x.length + 1) (q * V)
      (fun i hi => flatMap_range_length_le (finFlat fun b => visits k (insW x i b)) q V
        (fun b hb => by
        simp only [finFlat, hb, dif_pos]
        exact hchild _ (by rw [insW_length _ _ _ (by omega)])))
    have hD := flatMap_range_length_le (fun i => visits k (delW x i)) x.length V
      (fun i hi => hchild _ (by
      rw [delW_length _ _ hi]; omega))
    have hR := flatMap_range_length_le (fun i => (List.range q).flatMap (finFlat fun b =>
        if x[i]? = some b then [] else visits k (repW x i b))) x.length ((q - 1) * V) (fun i hi => by
      apply flatMap_range_length_le_skip (finFlat fun b =>
        if x[i]? = some b then [] else visits k (repW x i b)) q V (x[i]).val (x[i]).isLt
      · intro b hb
        simp only [finFlat, hb, dif_pos]
        split_ifs
        · simp
        · exact hchild _ (by rw [repW_length _ _ _ hi]; omega)
      · simp [finFlat, (x[i]).isLt, List.getElem?_eq_getElem hi])
    have hsum : ∑ i ∈ Finset.range (k + 1 + 1), T ^ i = 1 + T * V := by
      rw [Finset.sum_range_succ', hV, Finset.mul_sum]
      simp only [pow_zero, pow_succ]
      rw [add_comm]; congr 1
      apply Finset.sum_congr rfl; intro i _; ring
    rw [hsum]
    rcases Nat.eq_zero_or_pos q with hq | hq
    · have hx0 : x.length = 0 := by
        cases x with
        | nil => rfl
        | cons a _ => exact (Fin.elim0 (hq ▸ a))
      have : (List.range x.length).flatMap (fun i => visits k (delW x i)) = [] := by
        rw [hx0]; rfl
      rw [this]
      have h1 : q * V = 0 := by rw [hq, zero_mul]
      have h2 : (q - 1) * V = 0 := by rw [hq]; simp
      rw [h1, mul_zero] at hA
      rw [h2, mul_zero] at hR
      simp only [List.length_nil, add_zero]
      have : 1 ≤ 1 + T * V := by omega
      omega
    · have h1 : (x.length + 1) * (q * V) + x.length * V + x.length * ((q - 1) * V) ≤ T * V := by
        have e : x.length * V + x.length * ((q - 1) * V) = x.length * (q * V) := by
          rw [← mul_add]; congr 1
          have : q = (q - 1) + 1 := by omega
          conv_rhs => rw [this]
          ring
        calc _ = (x.length + 1) * (q * V) + x.length * (q * V) := by rw [add_assoc, e]
          _ = ((2 * x.length + 1) * q) * V := by ring
          _ ≤ T * V := by
            apply Nat.mul_le_mul_right
            rw [hT]; nlinarith
      omega

/-! ## Toy client (a): counting -/

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamGF
/-!
# GF(2)[X] arithmetic on `Cmd` (q379, Part G)

* fold forms of `binaryMul` / `binaryRem` with an arbitrary (large enough) loop count;
* value bounds (`binaryMul_lt`, `binaryRem_lt`, `fieldMul_lt`);
* `gfMul`, `gfRem`, `gfField` (= `fieldMul`) on a register block, `gfSetup` (the context).

Field-context block `g .. g+15`: `p lp P2 W N2 PN X Y Z` then scratch `g+9 .. g+15`, where
`lp = log2 p`, `P2 = 2^lp`, `N2 = 2W`, `PN = 2^(2W)`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## Arithmetic facts -/

theorem foldl_range_rev_stable (g : ℕ → ℕ → ℕ) (a n : ℕ) (h : ∀ i, n ≤ i → g a i = a) :
    ∀ m, n ≤ m → (List.range m).reverse.foldl g a = (List.range n).reverse.foldl g a := by
  intro m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [show n + (d + 1) = (n + d) + 1 by omega, List.range_succ, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      List.foldl_cons]
    rw [h _ (by omega), ih (by omega)]

theorem lt_two_pow_min {b N : ℕ} (hb : b < 2 ^ N) : b < 2 ^ (min N (b.log2 + 1)) := by
  rcases le_total N (b.log2 + 1) with h | h
  · rw [min_eq_left h]; exact hb
  · rw [min_eq_right h]; exact Nat.lt_log2_self

theorem testBit_false_of_lt_pow {b n i : ℕ} (hb : b < 2 ^ n) (hi : n ≤ i) : b.testBit i = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hi))

theorem binaryRem_fold_rev (p a N : ℕ) (ha : a < 2 ^ N) :
    binaryRem p a = (List.range N).reverse.foldl (remStep p) a := by
  have hn := lt_two_pow_min ha
  have hst : ∀ i, min N (a.log2 + 1) ≤ i → remStep p a i = a := by
    intro i hi; simp [remStep, testBit_false_of_lt_pow hn hi]
  have e1 := foldl_range_rev_stable (remStep p) a _ hst N (min_le_left _ _)
  have e2 := foldl_range_rev_stable (remStep p) a _ hst (a.log2 + 1) (min_le_right _ _)
  rw [e1, ← e2]; rfl

theorem range_reverse_eq_map (N : ℕ) :
    (List.range N).reverse = (List.range N).map (fun k => N - 1 - k) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_reverse, List.getElem_range, List.getElem_map, List.length_range]

/-- `binaryRem` as an upward loop over `k < N` processing bit `N - 1 - k`. -/
theorem binaryRem_fold (p a N : ℕ) (ha : a < 2 ^ N) :
    binaryRem p a = (List.range N).foldl (fun z k => remStep p z (N - 1 - k)) a := by
  rw [binaryRem_fold_rev p a N ha, range_reverse_eq_map, List.foldl_map]

theorem lt_pow_of_testBit_false {z i : ℕ} (hz : z < 2 ^ (i + 1)) (hb : z.testBit i = false) :
    z < 2 ^ i := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rcases Nat.eq_or_lt_of_le hj with rfl | hj
  · exact hb
  · exact testBit_false_of_lt_pow hz hj

theorem p_lt_pow (p : ℕ) : p < 2 ^ (p.log2 + 1) := Nat.lt_log2_self

theorem remStep_bound (p z i : ℕ) (hp : p ≠ 0) (hz : z < 2 ^ (max (i + 1) p.log2)) :
    remStep p z i < 2 ^ (max i p.log2) := by
  unfold remStep
  by_cases hi : p.log2 ≤ i
  · have hm1 : max (i + 1) p.log2 = i + 1 := by omega
    have hm2 : max i p.log2 = i := by omega
    rw [hm1] at hz; rw [hm2]
    have hpi : p * 2 ^ (i - p.log2) < 2 ^ (i + 1) := by
      calc p * 2 ^ (i - p.log2) < 2 ^ (p.log2 + 1) * 2 ^ (i - p.log2) :=
            Nat.mul_lt_mul_of_pos_right (p_lt_pow p) (by positivity)
        _ = 2 ^ (i + 1) := by rw [← pow_add]; congr 1; omega
    by_cases hb : z.testBit i = true
    · rw [if_pos ⟨hp, hi, hb⟩]
      apply lt_pow_of_testBit_false (Nat.xor_lt_two_pow hz hpi)
      have : (Nat.xor z (p * 2 ^ (i - p.log2))).testBit i = false := by
        show (z ^^^ (p * 2 ^ (i - p.log2))).testBit i = false
        rw [Nat.testBit_xor, Nat.testBit_mul_two_pow, hb]
        simp only [show i - (i - p.log2) = p.log2 by omega, Nat.testBit_log2 hp]
        simp
      exact this
    · rw [if_neg (fun h => hb h.2.2)]
      exact lt_pow_of_testBit_false hz (by simpa using hb)
  · rw [if_neg (fun h => hi h.2.1)]
    have hm1 : max (i + 1) p.log2 = p.log2 := by omega
    have hm2 : max i p.log2 = p.log2 := by omega
    rw [hm1] at hz; rw [hm2]; exact hz

theorem binaryRem_lt (p a : ℕ) (hp : p ≠ 0) : binaryRem p a < 2 ^ p.log2 := by
  set n := a.log2 + 1
  have key : ∀ k ≤ n, (List.range k).foldl (fun z k => remStep p z (n - 1 - k)) a <
      2 ^ (max (n - k) p.log2) := by
    intro k hk
    induction k with
    | zero =>
      simp only [List.range_zero, List.foldl_nil, Nat.sub_zero]
      exact lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
    | succ k ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      have := remStep_bound p _ (n - 1 - k) hp (by
        have e : n - 1 - k + 1 = n - k := by omega
        rw [e]; exact ih (by omega))
      rw [show n - (k + 1) = n - 1 - k by omega]; exact this
  have h := key n le_rfl
  rw [Nat.sub_self, Nat.zero_max] at h
  rw [binaryRem_fold p a n Nat.lt_log2_self]; exact h

theorem two_pow_log2_le (p : ℕ) (hp : p ≠ 0) : 2 ^ p.log2 ≤ p := (Nat.le_log2 hp).mp le_rfl

theorem fieldMul_lt (p a b : ℕ) (hp : p ≠ 0) : fieldMul p a b < 2 ^ p.log2 := binaryRem_lt p _ hp


/-! ## `gfMul` -/

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamColor
/-!
# `localColor` on `Cmd` (q379, Part G): setup and neighbour-list facts

Register map of `colorOf` (base `g`, all registers `g .. g+50`; the enumerator `cfg` must
start at `cfg.r0 ≥ g + 51`):
* `g .. g+15` field context and scratch (`RamGF`), `g+16 g+17 g+18 g+19` = `D off K E` of
  `bitEvalW` (`D` is the digit array, `K` is kept there throughout);
* `g+24` `Q`, `g+25` `|x|`, `g+26` `J` (number of neighbours), `g+27` `α`, `g+28` `found`,
  `g+29` `ok`, `g+30` `bitEval(x,a)`, `g+31` `a`, `g+32` `j`, `g+33 g+35` loop `one`s,
  `g+34 g+36 g+38 g+39` scratch, `g+36` the result;
* `g+40 .. g+50` the block of the word utilities.
Arrays: `XA` (a copy of `x`), `DG` (digits: row `0` is `x`, row `m+1` neighbour `m`, stride `K`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## The neighbour list -/

theorem mem_confusionNeighbors {q : ℕ} (t : ℕ) (x y : Word q) :
    y ∈ confusionNeighbors t x ↔ y ∈ nbrList t x := by
  unfold confusionNeighbors nbrList visits
  rw [List.mem_eraseDups, (List.mergeSort_perm _ _).mem_iff]

theorem confusionNeighbors_all {q : ℕ} (t : ℕ) (x : Word q) (f : Word q → Bool) :
    (confusionNeighbors t x).all f = (nbrList t x).all f := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  simp only [mem_confusionNeighbors]

/-! ## Initialisation: field context, a copy of `x`, the digits of `value x` -/

/-! ## Enumeration: digits of every neighbour -/

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamColor2
/-!
# `localColor` on `Cmd` (q379, Part G): the search for the first separating point

Digit array `DG`: row `m` (offset `m * K`) holds the base-`Q` digits of `ids m`, `m ≤ J`.
`okAt … a` says `bitEval` at `a` separates row `0` from every row `j + 1`, `j < J`; the search
computes `α = ((List.range Q).find? okAt).getD 0` with a `found` flag (no early exit).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

theorem bitEval_lt (Q p K W id a : ℕ) (hp : p ≠ 0) (hpW : p < 2 ^ W) (hQ0 : 0 < Q)
    (hQW : Q ≤ 2 ^ W) : bitEval Q p K id a < 2 ^ W := by
  unfold bitEval
  have : ∀ (l : List ℕ) z, z < 2 ^ W → l.foldl (fun z i =>
      Nat.xor (fieldMul p z a) ((id / Q ^ i) % Q)) z < 2 ^ W := by
    intro l
    induction l with
    | nil => intro z hz; exact hz
    | cons i l ih =>
      intro z _
      apply ih
      exact Nat.xor_lt_two_pow
        (lt_of_lt_of_le (fieldMul_lt p _ _ hp) (le_trans (two_pow_log2_le p hp) hpW.le))
        (lt_of_lt_of_le (Nat.mod_lt _ hQ0) hQW)
  exact this _ 0 (by positivity)

section Search
variable (inp : ℕ → ℕ) (B : ℕ)

theorem find_range_lt (P : ℕ → Bool) (a v : ℕ) (h : (List.range a).find? P = some v) : v < a := by
  have := List.mem_of_find?_eq_some h
  simpa using this

end Search

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamColor3
/-!
# `colorOf`: the program computing `localColor t P p x` (q379, Part G)

Main theorem `colorOf_spec`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

theorem bne_eq_decide_ne (a b : ℕ) : (a != b) = decide (a ≠ b) := by
  by_cases h : a = b <;> simp [h]

theorem all_range_getD {α : Type*} (l : List α) (d : α) (f : α → Bool) :
    (List.range l.length).all (fun j => f (l.getD j d)) = l.all f := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro h y hy
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
    have := h j (by simpa using hj)
    rwa [List.getD_eq_getElem _ _ hj] at this
  · intro h j hj
    simp only [List.mem_range] at hj
    rw [List.getD_eq_getElem _ _ hj]; exact h _ (List.getElem_mem hj)

/-- `localColor` in terms of `okAt` on `rowIds`. -/
theorem localColor_eq {q : ℕ} (t : ℕ) (P : Parameters) (p : ℕ) (x : Word q) :
    localColor t P p x =
      let α := ((List.range P.Q).find? (okAt P.Q p P.K (rowIds t x) (nbrList t x).length)).getD 0
      P.Q * α + bitEval P.Q p P.K (value x) α := by
  unfold localColor
  have : (fun a => (confusionNeighbors t x).all fun y =>
      decide (bitEval P.Q p P.K (value x) a ≠ bitEval P.Q p P.K (value y) a)) =
      okAt P.Q p P.K (rowIds t x) (nbrList t x).length := by
    funext a
    rw [confusionNeighbors_all, okAt, ← all_range_getD (nbrList t x) []]
    simp only [rowIds, bne_eq_decide_ne]
  simp only [this]

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamColor4
/-!
# `colorsAll`: the colour of `x` and of each of its neighbours (q379, Part G)

`colorsAll q t cfg1 cfg2 g X2 XA DG CLA`: `colorOf` (block `g .. g+50`, enumerator `cfg2`) on `x`
(result `g+51`), then the enumerator `cfg1` over `visits (2t) x`; for every visited `w` of length
`|x|` other than `x` (in visit order, duplicates kept: the list `nbrList t x`) it copies `w`
into `cfg2.buf (2t)`, runs `colorOf` and stores the colour at `CLA[J]`, `J := J + 1` (`g+52`).
Own registers `g+51 .. g+67`; `cfg2.r0 ≥ g + 68`, `cfg1.r0` above the registers of `cfg2`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

theorem localColor_lt {q : ℕ} (t : ℕ) (P : Parameters) (p W : ℕ) (x : Word q) (hp : p ≠ 0)
    (hpW : p < 2 ^ W) (hQ0 : 0 < P.Q) (hQW : P.Q ≤ 2 ^ W) :
    localColor t P p x < P.Q * P.Q + 2 ^ W := by
  rw [localColor_eq]
  simp only
  set α := ((List.range P.Q).find? (okAt P.Q p P.K (rowIds t x) (nbrList t x).length)).getD 0
  have hα : α < P.Q := by
    rcases hf : (List.range P.Q).find? (okAt P.Q p P.K (rowIds t x) (nbrList t x).length) with _ | v
    · simp only [α, hf, Option.getD_none]; exact hQ0
    · simp only [α, hf, Option.getD_some]; exact find_range_lt _ _ _ hf
  have := bitEval_lt P.Q p P.K W (value x) α hp hpW hQ0 hQW
  have : P.Q * α ≤ P.Q * P.Q := Nat.mul_le_mul_left _ hα.le
  omega

/-! ## The program -/

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamDecode
/-!
# The decoder, part 1: good-index test, good-index count, writing `repr` (q379, Part D)

* `goodW r piR cxR vR CL`: `regs r := 1` iff `cx % pi ≠ CL[ℓ] % pi` for all `ℓ < V`
  (`pi = regs piR`, `cx = regs cxR`, `V = regs vR`); writes only `r .. r+7`.
* `countW r iR prR piR cxR vR CL`: `regs r := #{i' < regs iR : goodW-test with pi = PR[i']}`;
  writes only `r .. r+3`, `piR`, and the `goodW` block `r+4 .. r+11`.
* `reprOut r vR wR offR X qR`: writes `repr q w v` into array `X` at offset `off`;
  writes only `r .. r+6`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

section Dec1
variable (inp : ℕ → ℕ) (B : ℕ)

/-! ## The good-index test -/

/-! ## Counting the good indices below `i` -/

/-! ## Writing `repr q w v` into an array -/

theorem dec_repr_eq_map {q : ℕ} (hq : 0 < q) (w N : ℕ) :
    Code.repr q w N = (List.range w).map (fun i => (⟨(N / q ^ (w - 1 - i)) % q, Nat.mod_lt _ hq⟩ : Fin q)) := by
  unfold Code.repr
  rw [← List.filterMap_eq_map]
  congr 1; funext i
  simp [Nat.mod_lt _ hq]

theorem dec_repr_length {q : ℕ} (hq : 0 < q) (w N : ℕ) : (Code.repr q w N).length = w := by
  rw [dec_repr_eq_map hq]; simp

theorem dec_repr_getElem {q : ℕ} (hq : 0 < q) (w N i : ℕ) (hi : i < (Code.repr q w N).length) :
    ((Code.repr q w N)[i]).val = (N / q ^ (w - 1 - i)) % q := by
  simp [dec_repr_eq_map hq]

end Dec1

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamParams2
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# Part P (q379): the prime table

`primesW PR Mc S`: for every `m < regs Mc` (trial division), store the primes in increasing
order into array `regs PR`: afterwards `arr PR i = Nat.nth Nat.Prime i` for all
`i < Nat.count Nat.Prime (regs Mc)`, and register `S` holds that count.
With `regs Mc > (L + 2) * (2 * (Nat.log 2 (L + 2) + 3))` this covers every `i ≤ L`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ### A Chebyshev bound on the `N`-th prime (copied from the q373 record,
`Solutions/EditMulticoloring/EncoderRedundancyAux1.lean`, `nth_prime_le`). -/

theorem ramP_two_mul_add_one_le_two_pow : ∀ s : ℕ, 3 ≤ s → 2 * s + 1 ≤ 2 ^ s
  | 0, h => by omega
  | 1, h => by omega
  | 2, h => by omega
  | 3, _ => by norm_num
  | s + 4, _ => by
    have := ramP_two_mul_add_one_le_two_pow (s + 3) (by omega)
    rw [pow_succ]; omega

/-- A Chebyshev-type upper bound on the `N`-th prime (zero based). -/
theorem ramP_nth_prime_le (N : ℕ) :
    Nat.nth Nat.Prime N ≤ (N + 2) * (2 * (Nat.log 2 (N + 2) + 3)) := by
  set s := Nat.log 2 (N + 2) + 3 with hs
  set x := (N + 2) * (2 * s) with hx
  have h1 : N + 2 < 2 ^ s := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (N + 2)
    calc N + 2 < 2 ^ (Nat.log 2 (N + 2) + 1) := this
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 := ramP_two_mul_add_one_le_two_pow s (by omega)
  have h3 : x + 1 ≤ 2 ^ (2 * s) := by
    have : (N + 2) * (2 * s + 1) ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul h1.le h2
    rw [two_mul s, pow_add]
    have : (N + 2) * (2 * s + 1) = x + (N + 2) := by rw [hx]; ring
    omega
  have hx12 : 12 ≤ x := by
    have : 6 ≤ 2 * s := by omega
    calc 12 = 2 * 6 := by norm_num
      _ ≤ (N + 2) * (2 * s) := Nat.mul_le_mul (by omega) this
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlx : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hlx1 : Real.log (x : ℝ) ≤ Real.log ((x : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have h4 : Real.log ((x : ℝ) + 1) ≤ (2 * s : ℕ) * Real.log 2 := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast h3
  have h5 : ((N : ℝ) + 1) ≤ ((x : ℝ) * Real.log 2 - Real.log ((x : ℝ) + 1)) / Real.log x := by
    rw [le_div_iff₀ hlx]
    have hxr : (x : ℝ) = ((N : ℝ) + 2) * ((2 * s : ℕ) : ℝ) := by rw [hx]; push_cast; ring
    have : ((N : ℝ) + 2) * Real.log ((x : ℝ) + 1) ≤ (x : ℝ) * Real.log 2 := by
      calc ((N : ℝ) + 2) * Real.log ((x : ℝ) + 1)
          ≤ ((N : ℝ) + 2) * (((2 * s : ℕ) : ℝ) * Real.log 2) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = (x : ℝ) * Real.log 2 := by rw [hxr]; ring
    nlinarith
  have h6 := Chebyshev.pi_ge x
  have h7 : N < Nat.primeCounting x := by
    have : (N : ℝ) < (Nat.primeCounting x : ℝ) := by linarith
    exact_mod_cast this
  have h8 : Nat.nth Nat.Prime N < x + 1 := by
    apply Nat.nth_lt_of_lt_count
    rw [← Nat.primeCounting', ← Nat.primeCounting_eq_primeCounting'_succ] at *
    exact h7
  omega

/-- Indices below the count of primes below `M`. -/
theorem lt_count_prime_of_nth_lt {i M : ℕ} (h : Nat.nth Nat.Prime i < M) :
    i < Nat.count Nat.Prime M := by
  have h1 : Nat.count Nat.Prime (Nat.nth Nat.Prime i + 1) = i + 1 := by
    rw [Nat.count_succ, Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime,
      if_pos (Nat.prime_nth_prime i)]
  have h2 := Nat.count_monotone Nat.Prime (show Nat.nth Nat.Prime i + 1 ≤ M by omega)
  omega

theorem lt_count_prime_of_le {i L M : ℕ} (hi : i ≤ L)
    (hM : (L + 2) * (2 * (Nat.log 2 (L + 2) + 3)) < M) : i < Nat.count Nat.Prime M := by
  apply lt_count_prime_of_nth_lt
  have h1 : Nat.nth Nat.Prime i ≤ Nat.nth Nat.Prime L :=
    Nat.nth_monotone Nat.infinite_setOfPred_prime hi
  have := ramP_nth_prime_le L
  omega

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamParams5
/-!
# Part P (q379): the parameters, part P (prime table, `h₂`, `h`) and part R (`q^h, ρ, q^ρ, m, k`)
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

theorem primeAt_lt_primeBound {i L : ℕ} (hi : i ≤ L) : primeAt i < primeBound L := by
  have := lt_count_prime_of_le (M := primeBound L) hi (by unfold primeBound; omega)
  exact Nat.nth_lt_of_lt_count this

/-- From the nonemptiness of the defining set and `shortLength ≤ n`, a witness `≤ n`. -/
theorem rho_witness {q t h n : ℕ} (hne : ∃ l, rhoCond q t h l) (hle : shortLength q t h ≤ n) :
    ∃ l ≤ n, rhoCond q t h l :=
  ⟨shortLength q t h, hle, Nat.sInf_mem (s := {l : ℕ | h ≤ l ∧ q ^ h * radiusBound q (2 * t) l ≤ q ^ l}) hne⟩

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamParams6
/-!
# Part P (q379): `paramsW`, all fields of `parameters q t n`

`paramsW q t nR PR O` (with `nR, PR < O`, `n = regs nR`, `regs PR` an array id) leaves
`ParamsAt s' O q t n` (layout below), fills the prime table `arr (regs PR) i = primeAt i` for
`i ≤ L`, and writes only registers in `[O, O + 49)`.

Layout: `O+0 r, O+1 K, O+2 b, O+3 Q, O+4 B, O+5 L, O+6 W = b + 1, O+7 f = Nat.log q (L / 2),
O+8 J, O+9 h₁, O+10 h₂, O+11 h, O+12 q^h, O+13 ρ, O+14 q^ρ, O+15 m, O+16 k`,
where `b = ceilLog 2 (r * K + 1)`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ### Size bounds of the outputs -/

theorem two_pow_ceilLog_le (X : ℕ) (hX : 1 ≤ X) : 2 ^ ceilLog 2 X ≤ 2 * X := by
  show 2 ^ (if X ≤ 2 ^ Nat.log 2 X then Nat.log 2 X else Nat.log 2 X + 1) ≤ 2 * X
  have h1 := Nat.pow_log_le_self 2 (show X ≠ 0 by omega)
  split_ifs
  · omega
  · rw [pow_succ]; omega

theorem params_Q_le (q t n : ℕ) :
    (parameters q t n).Q ≤ 2 * ((parameters q t n).r * (parameters q t n).K + 1) :=
  two_pow_ceilLog_le _ (by omega)

theorem params_m_le (q t n : ℕ) : (parameters q t n).m ≤ n := Nat.sub_le _ _

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

/-! ## Writing the digits of a number -/

end EditMulticoloring.Dev.Ram.EncS
end

section
-- module Solutions.EditMulticoloring.RamDecode4
/-!
# The decoder, part 4: the program `decProg` and its specification (q379, Part D)

The short-table routine is taken from `RamEncodeS4` (namespace `EncS`, a verbatim copy of
`RamShort*`), because `RamShort` and `RamColor` cannot be imported together (name clashes
`value_lt`, `visBound`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## The split of a short-code index -/

theorem dec_mod_pow_div_mod (a q e H : ℕ) (hq : 0 < q) (he : e < H) :
    a % q ^ H / q ^ e % q = a / q ^ e % q := by
  have h1 : q ^ H = q ^ e * q ^ (H - e) := by rw [← pow_add]; congr 1; omega
  rw [h1, Nat.mod_mul_right_div_self]
  apply Nat.mod_mod_of_dvd
  exact dvd_pow_self q (by omega)

theorem dec_repr_split {q : ℕ} (hq : 0 < q) (h₁ h₂ idx : ℕ) :
    Code.repr q (h₁ + h₂) idx = Code.repr q h₁ (idx / q ^ h₂) ++ Code.repr q h₂ (idx % q ^ h₂) := by
  apply List.ext_getElem
  · simp [dec_repr_length hq]
  intro i h1 h2
  apply Fin.ext
  rw [dec_repr_getElem hq]
  rw [dec_repr_length hq] at h1
  by_cases hi : i < h₁
  · rw [List.getElem_append_left (by rw [dec_repr_length hq]; exact hi), dec_repr_getElem hq,
      Nat.div_div_eq_div_mul, ← pow_add]
    congr 3; omega
  · rw [List.getElem_append_right (by rw [dec_repr_length hq]; omega), dec_repr_getElem hq]
    simp only [dec_repr_length hq]
    have e : h₁ + h₂ - 1 - i = h₂ - 1 - (i - h₁) := by omega
    rw [e, dec_mod_pow_div_mod _ _ _ _ hq (by omega)]

theorem splitOK_of {q t n : ℕ} (hq : 0 < q) : SplitOK q t n := by
  intro idx hidx
  have hh : (parameters q t n).h = (parameters q t n).h₁ + (parameters q t n).h₂ := rfl
  rw [hh] at hidx ⊢
  rw [dec_repr_split hq]
  have l1 := dec_repr_length hq (parameters q t n).h₁ (idx / q ^ (parameters q t n).h₂)
  have hpos : 0 < q ^ (parameters q t n).h₂ := Nat.pow_pos hq
  have b1 : idx / q ^ (parameters q t n).h₂ < q ^ (parameters q t n).h₁ := by
    rw [Nat.div_lt_iff_lt_mul hpos, ← pow_add]; exact hidx
  have b2 : idx % q ^ (parameters q t n).h₂ < q ^ (parameters q t n).h₂ := Nat.mod_lt _ hpos
  refine ⟨?_, ?_⟩
  · rw [List.take_left' l1, EncS.value_repr hq _ _ b1]
  · rw [List.drop_left' l1, EncS.value_repr hq _ _ b2]

/-! ## Monotone bounds -/

theorem dec_enumE_mono (c : EnumCfg) (B q s : ℕ) {L L' : ℕ} (h : L ≤ L') :
    c.enumE B q L s ≤ c.enumE B q L' s := by
  rw [EnumCfg.enumE_eq, EnumCfg.enumE_eq]
  apply Nat.mul_le_mul
  · apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_left (by omega) 2
  · exact kappa_bits_le B (by omega)

theorem dec_visits_le {q : ℕ} (t n : ℕ) (z : Word q) (hz : z.length ≤ n + t) :
    (visits t z).length ≤ ∑ i ∈ Finset.range (t + 1), (2 * q * (n + 2 * t + 1)) ^ i := by
  refine (visits_length_le t z).trans (Finset.sum_le_sum fun i _ => Nat.pow_le_pow_left ?_ i)
  apply Nat.mul_le_mul_left; omega

/-! ## The program -/

section Top
variable (B : ℕ)

theorem decFinish_spec {q t n p : ℕ} (inp : ℕ → ℕ) (a : Option (Word q)) (st : HS)
    (hI : DInv q t n p a st) :
    let s' := (Cmd.ifz 2 .skip dEmit).exec inp st
    (if s'.regs 2 = 0 then none else some s'.out) = a.map (List.map Fin.val) ∧ s'.regs 2 ≤ 1 ∧
    (Cmd.ifz 2 .skip dEmit).cost inp B st ≤ (6 * (parameters q t n).k + 7) * kappa B (RAM.bits (DM q t n)) := by
  intro s'
  set P := parameters q t n with hP
  set κ := kappa B (RAM.bits (DM q t n)) with hκ
  have kb : ∀ a, a ≤ DM q t n → kappa B (RAM.bits a) ≤ κ := fun a h => kappa_bits_le B h
  have hDM : DM q t n = 4 * q ^ n + 2 * q ^ P.h + 2 * (P.Q * P.Q) + 2 * dTW q t n + primeBound P.L +
    dVb q t n + P.L + 4 * n + P.k + 2 * q + 100 * t + 1000 := rfl
  obtain ⟨hc, ho, hd⟩ := hI
  have hk : st.regs 116 = P.k := hc.par.hk
  rcases hd with ⟨ha, h2⟩ | ⟨r, ha, h2, h3, h4⟩
  · subst ha
    have hs : s' = st := by show (Cmd.ifz 2 _ _).exec inp st = st; rw [exec_ifz, if_pos h2]; rfl
    rw [hs, h2]
    refine ⟨by simp, by omega, ?_⟩
    rw [cost_ifz, if_pos h2, cost_skip, h2]
    have := kb 0 (by omega)
    have : κ ≤ (6 * P.k + 7) * κ := Nat.le_mul_of_pos_left _ (by omega)
    omega
  · subst ha
    have h4' : r.length = P.k := h4
    have hz : st.regs 2 ≠ 0 := by rw [h2]; omega
    set A := seqs [lit 280 2, lit 281 0, cp 282 116] with hA
    set s1 := A.exec inp st with hs1
    have r1 : ∀ r, (r < 280 ∨ 283 ≤ r) → s1.regs r = st.regs r := by
      intro r hr; simp (disch := omega) [hs1, hA, upd_ne]
    have v280 : s1.regs 280 = 2 := by simp (disch := omega) [hs1, hA, upd_ne]
    have v281 : s1.regs (280 + 1) = 0 := by simp (disch := omega) [hs1, hA, upd_ne]
    have v282 : s1.regs (280 + 2) = r.length := by simp (disch := omega) [hs1, hA, upd_ne, hk, h4']
    have m1 : s1.mem = st.mem := by simp [hs1, hA]
    have o1 : s1.out = [] := by simp [hs1, hA, ho]
    have hw1 : WordAt s1 (s1.regs 280) (s1.regs (280 + 1)) r := by
      rw [v280, v281]; exact h3.congr (fun i _ => by simp [HS.arr, m1])
    have E := emitW_word inp 280 s1 r hw1 v282
    obtain ⟨-, efr, -, -, ecost⟩ := emitW_spec inp B 280 s1 q (DM q t n)
      (fun i hi => by rw [v282] at hi; exact (hw1.lt i hi).le)
      (by rw [v280, v281, v282, o1, h4']; simp only [List.length_nil]; omega)
    have hs : s' = (emitW 280).exec inp s1 := by
      show (Cmd.ifz 2 _ _).exec inp st = _; rw [exec_ifz, if_neg hz]; rfl
    have e2 : s'.regs 2 = 1 := by rw [hs, efr 2 (by omega), r1 2 (by omega), h2]
    refine ⟨?_, by omega, ?_⟩
    · rw [e2, if_neg (by omega), hs, E, o1]; simp
    · rw [cost_ifz, if_neg hz, h2]
      have hco : dEmit.cost inp B st = A.cost inp B st + ((emitW 280).cost inp B s1 + 0) := by
        show (seqs [lit 280 2, lit 281 0, cp 282 116, emitW 280]).cost inp B st = _
        simp only [cost_seqs_cons, cost_seqs_nil, hA, hs1, exec_seqs_cons, exec_seqs_nil]
        ring
      rw [hco]
      have cA : A.cost inp B st ≤ 3 * κ := by
        simp (disch := omega) only [hA, cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp,
          exec_seqs_cons, exec_lit, HS.setR_regs, upd_ne, hk]
        have := kb 2 (by omega)
        have := kb 0 (by omega)
        have := kb P.k (by omega)
        omega
      rw [v282, h4'] at ecost
      have ecost' : (emitW 280).cost inp B s1 ≤ (6 * P.k + 3) * κ := ecost
      have := kb 1 (by omega)
      have e : (6 * P.k + 7) * κ = κ + 3 * κ + (6 * P.k + 3) * κ := by ring
      rw [e]; omega

/-- **The decoder.** -/
theorem decProg_spec (q t : ℕ) (hq : 2 ≤ q) (n : ℕ) (y : Word q)
    (H1 : ∃ l ≤ n, rhoCond q t (parameters q t n).h l)
    (H2 : 2 ^ ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) ≤
        modSearch (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1)) ∧
      modSearch (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1)) <
        2 ^ (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1))
    (H3 : 1 ≤ (parameters q t n).m ∧ (parameters q t n).m + (parameters q t n).ρ = n) :
    let s := (decProg q t).exec (RAM.inputAt y) (HS.init n)
    (if s.regs decFlag = 0 then none else some s.out) =
      (decode t n (modSearch (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1))) y).map
        (List.map Fin.val) ∧
    (decProg q t).cost (RAM.inputAt y) B (HS.init n) ≤ decCost q t n B ∧
    s.regs decFlag ≤ 1 := by
  intro s
  set inp := RAM.inputAt y with hinp
  set P := parameters q t n with hP
  have kb : ∀ a, a ≤ DM q t n → kappa B (RAM.bits a) ≤ kappa B (RAM.bits (DM q t n)) := fun a h => kappa_bits_le B h
  have hDM : DM q t n = 4 * q ^ n + 2 * q ^ P.h + 2 * (P.Q * P.Q) + 2 * dTW q t n + primeBound P.L +
    dVb q t n + P.L + 4 * n + P.k + 2 * q + 100 * t + 1000 := rfl
  set b := decB q t n with hb
  set p := modSearch b with hpdef
  have hQb : P.Q = 2 ^ b := rfl
  have hTW : dTW q t n = 2 ^ (b + 1) := rfl
  have H2' : 2 ^ b ≤ p ∧ p < 2 ^ (b + 1) := H2
  have hp0 : p ≠ 0 := Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le (Nat.two_pow_pos b) H2'.1)
  have hpW : p < dTW q t n := by rw [hTW]; exact H2'.2
  have hQ0 : 0 < P.Q := by rw [hQb]; exact Nat.two_pow_pos b
  have hQW : P.Q ≤ dTW q t n := by rw [hQb, hTW]; exact Nat.pow_le_pow_right (by omega) (by omega)
  have H : DHyp q t n p := ⟨hq, H3.2, fun x => by
      have := localColor_lt t P p (dW q t n) x hp0 hpW hQ0 hQW
      exact this, hp0, hpW, hQ0, hQW⟩
  have hsplit : SplitOK q t n := splitOK_of (by omega)
  obtain ⟨I, hlen, hzw, h10, hcost⟩ := decPre_spec B t n hq y H1 hpW H3.2
  have hcost' : (decPre q t).cost inp B (HS.init n) ≤ preCost q t n B := hcost
  set s10 := (decPre q t).exec inp (HS.init n) with hs10
  set z := y.take (n + t + 1) with hz
  set c := (if n + t < z.length then 1 else 0) + (if z.length + t < n then 1 else 0) with hc
  have hdec : decode t n p y = if c = 0 then ((scripts t z).map Prod.snd).findSome? (validate t n p)
      else none := by
    unfold decode
    rw [← hz]
    by_cases h1 : z.length > n + t
    · rw [if_pos (Or.inl h1), if_neg]; rw [hc]; simp [h1]
    · by_cases h2 : z.length + t < n
      · rw [if_pos (Or.inr h2), if_neg]; rw [hc]; simp [h2]
      · rw [if_neg (by omega), if_pos]; rw [hc]; simp [h2]; omega
  set s11 := (Cmd.ifz 10 (enumScripts q t (dC0 t) (pBody q t)) .skip).exec inp s10 with hs11
  have hs : s = (Cmd.ifz 2 .skip dEmit).exec inp s11 := rfl
  have hco : (decProg q t).cost inp B (HS.init n) = (decPre q t).cost inp B (HS.init n) +
      ((Cmd.ifz 10 (enumScripts q t (dC0 t) (pBody q t)) .skip).cost inp B s10 +
      ((Cmd.ifz 2 .skip dEmit).cost inp B s11 + 0)) := rfl
  have hvis : ∀ zz : Word q, zz.length ≤ n + t →
      (visits t zz).length * (dBodyCost q t n B + (dC0 t).enumE B q zz.length t) ≤
      (∑ i ∈ Finset.range (t + 1), (2 * q * (n + 2 * t + 1)) ^ i) *
        (dBodyCost q t n B + (dC0 t).enumE B q (n + t) t) := fun zz hzz =>
    Nat.mul_le_mul (dec_visits_le t n zz hzz)
      (Nat.add_le_add_left (dec_enumE_mono (dC0 t) B q t hzz) _)
  have hdc : decCost q t n B = preCost q t n B +
      (∑ i ∈ Finset.range (t + 1), (2 * q * (n + 2 * t + 1)) ^ i) *
        (dBodyCost q t n B + (dC0 t).enumE B q (n + t) t) + (6 * P.k + 20) * kappa B (RAM.bits (DM q t n)) := rfl
  have hc2 : c ≤ 2 := by rw [hc]; split_ifs <;> omega
  have hk10 : kappa B (RAM.bits (s10.regs 10)) ≤ kappa B (RAM.bits (DM q t n)) := kb (s10.regs 10) (by rw [h10]; omega)
  have hdec' : decode t n (modSearch (ceilLog 2 (P.r * P.K + 1))) y = if c = 0 then
      ((scripts t z).map Prod.snd).findSome? (validate t n p) else none := hdec
  by_cases hc0 : c = 0
  · have hz10 : s10.regs 10 = 0 := by rw [h10]; exact hc0
    have hzl : z.length ≤ n + t := by
      by_contra hh; rw [hc, if_pos (by omega)] at hc0; omega
    obtain ⟨E1, E2⟩ := decEnum_spec inp B H hsplit z hzl s10 I hlen hzw
    have hs11 : s11 = (enumScripts q t (dC0 t) (pBody q t)).exec inp s10 := by
      rw [hs11, exec_ifz, if_pos hz10]
    rw [← hs11] at E1
    obtain ⟨F1, F2, F3⟩ := decFinish_spec B inp _ s11 E1
    rw [← hs] at F1 F2
    refine ⟨?_, ?_, F2⟩
    · rw [show decFlag = 2 from rfl, F1, hdec', if_pos hc0]
    · rw [hco, hdc]
      rw [cost_ifz, if_pos hz10]
      have := hvis z hzl
      have F3' : (Cmd.ifz 2 .skip dEmit).cost inp B s11 ≤ (6 * P.k + 7) * kappa B (RAM.bits (DM q t n)) := F3
      have e : (6 * P.k + 20) * kappa B (RAM.bits (DM q t n)) = kappa B (RAM.bits (DM q t n)) + (6 * P.k + 7) * kappa B (RAM.bits (DM q t n)) + 12 * kappa B (RAM.bits (DM q t n)) := by ring
      rw [e]; omega
  · have hz10 : s10.regs 10 ≠ 0 := by rw [h10]; exact hc0
    have hs11 : s11 = s10 := by rw [hs11, exec_ifz, if_neg hz10]; rfl
    rw [← hs11] at I
    obtain ⟨F1, F2, F3⟩ := decFinish_spec B inp _ s11 I
    rw [← hs] at F1 F2
    refine ⟨?_, ?_, F2⟩
    · rw [show decFlag = 2 from rfl, F1, hdec', if_neg hc0]
    · rw [hco, hdc]
      rw [cost_ifz, if_neg hz10, cost_skip]
      have F3' : (Cmd.ifz 2 .skip dEmit).cost inp B s11 ≤ (6 * P.k + 7) * kappa B (RAM.bits (DM q t n)) := F3
      have e : (6 * P.k + 20) * kappa B (RAM.bits (DM q t n)) = kappa B (RAM.bits (DM q t n)) + (6 * P.k + 7) * kappa B (RAM.bits (DM q t n)) + 12 * kappa B (RAM.bits (DM q t n)) := by ring
      rw [e]
      have := Nat.zero_le ((∑ i ∈ Finset.range (t + 1), (2 * q * (n + 2 * t + 1)) ^ i) *
        (dBodyCost q t n B + (dC0 t).enumE B q (n + t) t))
      omega

end Top

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamModulus
/-! Part M (q379): the modulus found by `modSearch` is valid. -/

set_option autoImplicit false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

namespace Modulus

open Polynomial

/-! ## Bit polynomials -/

lemma cast_div_mod (a i : ℕ) : (((a / 2 ^ i) % 2 : ℕ) : ZMod 2) = mbit a i := by
  unfold mbit
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (a / 2 ^ i) with h | h <;> simp [h]

lemma mbit_eq_zero_of_lt {a i : ℕ} (h : a < 2 ^ i) : mbit a i = 0 := by
  simp [mbit, Nat.testBit_lt_two_pow h]

lemma coeff_bp (a i : ℕ) : (binaryPoly a).coeff i = mbit a i := by
  unfold binaryPoly
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, mul_one, cast_div_mod]
  · intro j _ hj
    simp [Ne.symm hj]
  · intro hi
    simp only [Finset.mem_range, not_lt] at hi
    have : a < 2 ^ i := lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by norm_num) hi)
    rw [if_pos rfl, mul_one, cast_div_mod, mbit_eq_zero_of_lt this]

lemma bp_zero : binaryPoly 0 = 0 := by
  ext i; simp [coeff_bp, mbit]

lemma bp_one : binaryPoly 1 = 1 := by
  ext i
  rw [coeff_bp, Polynomial.coeff_one]
  rcases i with _ | i
  · simp [mbit]
  · simp [mbit, Nat.testBit_lt_two_pow (show 1 < 2 ^ (i + 1) from Nat.one_lt_two_pow (by omega))]

lemma bp_xor (a b : ℕ) : binaryPoly (Nat.xor a b) = binaryPoly a + binaryPoly b := by
  ext i
  rw [Polynomial.coeff_add, coeff_bp, coeff_bp, coeff_bp]
  unfold mbit
  rw [show Nat.xor a b = a ^^^ b from rfl, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> decide

lemma bp_shift (a k : ℕ) : binaryPoly (a * 2 ^ k) = binaryPoly a * X ^ k := by
  ext i
  rw [Polynomial.coeff_mul_X_pow', coeff_bp]
  unfold mbit
  rw [Nat.testBit_mul_two_pow]
  split_ifs with h1 h2 h2 <;> simp_all [coeff_bp, mbit]

lemma bp_inj {x y : ℕ} (h : binaryPoly x = binaryPoly y) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  have := congrArg (fun f => Polynomial.coeff f i) h
  simp only [coeff_bp, mbit] at this
  cases hx : x.testBit i <;> cases hy : y.testBit i <;> simp_all

lemma testBit_log2 {p : ℕ} (hp : p ≠ 0) : p.testBit p.log2 = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h1 := Nat.log2_self_le hp
  have h2 : p < 2 ^ p.log2 * 2 := by rw [← pow_succ]; exact Nat.lt_log2_self
  have : p / 2 ^ p.log2 = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  simp [this]

lemma natDegree_bp {d : ℕ} (hd : d ≠ 0) : (binaryPoly d).natDegree = d.log2 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [coeff_bp]
    apply mbit_eq_zero_of_lt
    exact lt_of_lt_of_le Nat.lt_log2_self
      (Nat.pow_le_pow_right (by norm_num) (by exact_mod_cast hm))
  · rw [coeff_bp, mbit, testBit_log2 hd]; simp

lemma monic_bp {d : ℕ} (hd : d ≠ 0) : (binaryPoly d).Monic := by
  unfold Polynomial.Monic Polynomial.leadingCoeff
  rw [natDegree_bp hd, coeff_bp, mbit, testBit_log2 hd]; simp

lemma bp_ne_zero {d : ℕ} (hd : d ≠ 0) : binaryPoly d ≠ 0 := (monic_bp hd).ne_zero

lemma degree_bp_lt {a N : ℕ} (h : a < 2 ^ N) : (binaryPoly a).degree < N := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_bp]
  exact mbit_eq_zero_of_lt (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hm))

lemma bp_C (c : ZMod 2) : ∃ a, a < 2 ∧ binaryPoly a = C c := by
  fin_cases c
  · exact ⟨0, by norm_num, by rw [bp_zero]; symm; exact Polynomial.C_eq_zero.mpr rfl⟩
  · exact ⟨1, by norm_num, by rw [bp_one]; symm; exact Polynomial.C_1⟩

/-- Every polynomial of degree `< N` is a bit polynomial with mask `< 2^N`. -/
lemma bp_surj : ∀ (N : ℕ) (q : (ZMod 2)[X]), q.degree < N → ∃ a, a < 2 ^ N ∧ binaryPoly a = q := by
  intro N
  induction N with
  | zero =>
    intro q hq
    refine ⟨0, by norm_num, ?_⟩
    rw [bp_zero]
    ext m
    rw [Polynomial.coeff_zero]
    exact (Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le hq (by exact_mod_cast Nat.zero_le m))).symm
  | succ N ih =>
    intro q hq
    set q' := q - C (q.coeff N) * X ^ N with hq'
    have hdeg : q'.degree < N := by
      rw [Polynomial.degree_lt_iff_coeff_zero]
      intro m hm
      rw [hq', Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow]
      rcases Nat.eq_or_lt_of_le hm with h | h
      · subst h; simp
      · rw [if_neg (by omega), sub_zero]
        exact Polynomial.coeff_eq_zero_of_degree_lt
          (lt_of_lt_of_le hq (by exact_mod_cast (show N + 1 ≤ m by omega)))
    obtain ⟨a', ha', ha'q⟩ := ih q' hdeg
    obtain ⟨c, hc, hcq⟩ := bp_C (q.coeff N)
    refine ⟨Nat.xor a' (c * 2 ^ N), ?_, ?_⟩
    · apply Nat.xor_lt_two_pow
      · exact lt_of_lt_of_le ha' (Nat.pow_le_pow_right (by norm_num) (by omega))
      · rw [pow_succ, mul_comm (2 ^ N)]
        exact Nat.mul_lt_mul_of_pos_right hc (by positivity)
    · rw [bp_xor, bp_shift, ha'q, hcq, hq']; ring

/-! ## The remainder -/

lemma binaryRem_cong (p : ℕ) : ∀ (l : List ℕ) (z : ℕ), ∃ c : (ZMod 2)[X],
    binaryPoly (l.foldl (fun z i =>
      if p ≠ 0 ∧ p.log2 ≤ i ∧ z.testBit i then
        Nat.xor z (p * 2 ^ (i - p.log2)) else z) z) = binaryPoly z + binaryPoly p * c := by
  intro l
  induction l with
  | nil => intro z; exact ⟨0, by simp⟩
  | cons i l ih =>
    intro z
    simp only [List.foldl_cons]
    split_ifs with h
    · obtain ⟨c, hc⟩ := ih (Nat.xor z (p * 2 ^ (i - p.log2)))
      refine ⟨c + X ^ (i - p.log2), ?_⟩
      rw [hc, bp_xor, bp_shift]; ring
    · exact ih z

lemma binaryRem_bits (p : ℕ) (hp : p ≠ 0) : ∀ (N z : ℕ),
    (∀ j, N ≤ j → p.log2 ≤ j → z.testBit j = false) →
    ∀ j, p.log2 ≤ j → ((List.range N).reverse.foldl (fun z i =>
      if p ≠ 0 ∧ p.log2 ≤ i ∧ z.testBit i then
        Nat.xor z (p * 2 ^ (i - p.log2)) else z) z).testBit j = false := by
  intro N
  induction N with
  | zero => intro z hz j hj; simpa using hz j (Nat.zero_le _) hj
  | succ N ih =>
    intro z hz
    rw [List.range_succ, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.foldl_cons]
    apply ih
    intro j hNj hpj
    split_ifs with h
    · rw [show Nat.xor z (p * 2 ^ (N - p.log2)) = z ^^^ (p * 2 ^ (N - p.log2)) from rfl,
        Nat.testBit_xor, Nat.testBit_mul_two_pow]
      rcases Nat.eq_or_lt_of_le hNj with hj | hj
      · subst hj
        rw [h.2.2, show N - (N - p.log2) = p.log2 by omega, testBit_log2 hp]
        simp
      · rw [hz j (by omega) hpj]
        have : p < 2 ^ (j - (N - p.log2)) :=
          lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by norm_num) (by omega))
        simp [Nat.testBit_lt_two_pow this]
    · rcases Nat.eq_or_lt_of_le hNj with hj | hj
      · subst hj
        simp only [ne_eq, hp, not_false_eq_true, true_and, not_and, Bool.not_eq_true] at h
        exact h hpj
      · exact hz j (by omega) hpj

lemma binaryRem_lt (p a : ℕ) (hp : p ≠ 0) : binaryRem p a < 2 ^ p.log2 := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  unfold binaryRem
  apply binaryRem_bits p hp _ a _ j hj
  intro i hi _
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le Nat.lt_log2_self
    (Nat.pow_le_pow_right (by norm_num) hi))

lemma binaryRem_eq_zero_iff {d : ℕ} (hd : d ≠ 0) (a : ℕ) :
    binaryRem d a = 0 ↔ binaryPoly d ∣ binaryPoly a := by
  obtain ⟨c, hc⟩ := binaryRem_cong d (List.range (a.log2 + 1)).reverse a
  change binaryPoly (binaryRem d a) = _ at hc
  have hdvd : binaryPoly d ∣ binaryPoly a ↔ binaryPoly d ∣ binaryPoly (binaryRem d a) := by
    rw [hc, dvd_add_left (dvd_mul_right _ _)]
  rw [hdvd]
  constructor
  · intro h; rw [h, bp_zero]; exact dvd_zero _
  · intro h
    have hz : binaryPoly (binaryRem d a) = 0 := by
      apply Polynomial.eq_zero_of_dvd_of_degree_lt h
      rw [Polynomial.degree_eq_natDegree (bp_ne_zero hd), natDegree_bp hd]
      exact degree_bp_lt (binaryRem_lt d a hd)
    exact bp_inj (hz.trans bp_zero.symm)

/-! ## The test -/

lemma log2_of_range {b p : ℕ} (h1 : 2 ^ b ≤ p) (h2 : p < 2 ^ (b + 1)) : p ≠ 0 ∧ p.log2 = b := by
  have hp0 : p ≠ 0 := by have := Nat.one_le_two_pow (n := b); omega
  exact ⟨hp0, (Nat.log2_eq_iff hp0).2 ⟨h1, h2⟩⟩

lemma modTest_iff (b p : ℕ) :
    modTest b p = true ↔ ∀ d, d < 2 ^ b → 2 ≤ d → ¬ binaryPoly d ∣ binaryPoly p := by
  unfold modTest
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne,
    ne_eq]
  refine forall_congr' fun d => imp_congr_right fun _ => ?_
  by_cases h2 : d < 2
  · simp [h2]
  · have hd : d ≠ 0 := by omega
    simp only [h2, false_or, binaryRem_eq_zero_iff hd]
    constructor
    · intro h _; exact h
    · intro h; exact h (by omega)

lemma irreducible_of_modTest {b p : ℕ} (hb : 1 ≤ b) (h1 : 2 ^ b ≤ p) (h2 : p < 2 ^ (b + 1))
    (ht : modTest b p = true) : Irreducible (binaryPoly p) := by
  obtain ⟨hp0, hlog⟩ := log2_of_range h1 h2
  have hdeg : (binaryPoly p).natDegree = b := by rw [natDegree_bp hp0, hlog]
  have hnu : ¬ IsUnit (binaryPoly p) := by
    intro hu
    have := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  rw [Polynomial.irreducible_iff_lt_natDegree_lt (bp_ne_zero hp0) hnu]
  intro q hq hqd
  rw [Finset.mem_Ioc, hdeg] at hqd
  have hqb : q.natDegree < b := by
    have := Nat.div_le_self b 2
    have : b / 2 < b := Nat.div_lt_self (by omega) (by norm_num)
    omega
  obtain ⟨d, hd, rfl⟩ := bp_surj b q (by
    rw [Polynomial.degree_eq_natDegree hq.ne_zero]; exact_mod_cast hqb)
  rw [modTest_iff] at ht
  apply ht d hd
  by_contra hlt
  replace hlt := Nat.lt_of_not_le hlt
  interval_cases d
  · simp [bp_zero] at hqd
  · simp [bp_one] at hqd

lemma modTest_of_irreducible {b p : ℕ} (h1 : 2 ^ b ≤ p) (h2 : p < 2 ^ (b + 1))
    (hi : Irreducible (binaryPoly p)) : modTest b p = true := by
  obtain ⟨hp0, hlog⟩ := log2_of_range h1 h2
  rw [modTest_iff]
  intro d hd h2d hdvd
  obtain ⟨c, hc⟩ := hdvd
  have hd0 : d ≠ 0 := by omega
  have hdl : d.log2 < b := by
    rw [Nat.log2_lt hd0]; exact hd
  have hdl1 : 1 ≤ d.log2 := by
    rw [Nat.le_log2 hd0]; simpa using h2d
  have hc0 : c ≠ 0 := by
    rintro rfl; rw [mul_zero] at hc; exact bp_ne_zero hp0 hc
  rcases hi.isUnit_or_isUnit hc with hu | hu
  · have := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [natDegree_bp hd0] at this; omega
  · have hcd := Polynomial.natDegree_eq_zero_of_isUnit hu
    have := congrArg Polynomial.natDegree hc
    rw [Polynomial.natDegree_mul (bp_ne_zero hd0) hc0, hcd, natDegree_bp hp0,
      natDegree_bp hd0, hlog] at this
    omega

/-! ## Existence of an irreducible polynomial of degree `b` -/

lemma exists_irreducible (b : ℕ) (hb : 1 ≤ b) :
    ∃ f : (ZMod 2)[X], f.Monic ∧ Irreducible f ∧ f.natDegree = b := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element_of_finite_bot (ZMod 2) (GaloisField 2 b)
  have hint : IsIntegral (ZMod 2) α := Algebra.IsIntegral.isIntegral α
  refine ⟨minpoly (ZMod 2) α, minpoly.monic hint, minpoly.irreducible hint, ?_⟩
  rw [← IntermediateField.adjoin.finrank hint, hα, IntermediateField.finrank_top',
    GaloisField.finrank 2 (by omega)]

lemma exists_valid (b : ℕ) (hb : 1 ≤ b) :
    ∃ p, 2 ^ b ≤ p ∧ p < 2 ^ (b + 1) ∧ Irreducible (binaryPoly p) := by
  obtain ⟨f, hm, hi, hd⟩ := exists_irreducible b hb
  obtain ⟨p, hp, rfl⟩ := bp_surj (b + 1) f (by
    rw [Polynomial.degree_eq_natDegree hm.ne_zero, hd]; exact_mod_cast Nat.lt_succ_self b)
  refine ⟨p, ?_, hp, hi⟩
  apply Nat.ge_two_pow_of_testBit
  have hc : (binaryPoly p).coeff b = 1 := by
    have := hm.leadingCoeff
    rwa [Polynomial.leadingCoeff, hd] at this
  rw [coeff_bp, mbit] at hc
  by_contra h
  simp [h] at hc

end Modulus

open Modulus in
theorem modSearch_valid (b : ℕ) (hb : 1 ≤ b) : ValidModulus b (modSearch b) := by
  obtain ⟨p0, h01, h02, h0i⟩ := exists_valid b hb
  have hsome : (((List.range (2^b)).map (· + 2^b)).find? (modTest b)).isSome := by
    rw [List.find?_isSome]
    refine ⟨p0, ?_, modTest_of_irreducible h01 h02 h0i⟩
    rw [List.mem_map]
    refine ⟨p0 - 2 ^ b, ?_, by omega⟩
    rw [List.mem_range]
    rw [pow_succ] at h02
    omega
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hsome
  have hmem := List.mem_of_find?_eq_some hp
  have htest := List.find?_some hp
  rw [List.mem_map] at hmem
  obtain ⟨i, hi, rfl⟩ := hmem
  rw [List.mem_range] at hi
  have hlo : 2 ^ b ≤ i + 2 ^ b := by omega
  have hhi : i + 2 ^ b < 2 ^ (b + 1) := by rw [pow_succ]; omega
  unfold modSearch
  rw [hp, Option.getD_some]
  exact ⟨hb, hlo, hhi, irreducible_of_modTest hb hlo hhi htest⟩

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamSim
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.HS.setR_arr _root_.EditMulticoloring.Dev.Ram.HS.setR_cur _root_.EditMulticoloring.Dev.Ram.HS.setR_mem _root_.EditMulticoloring.Dev.Ram.HS.setR_out _root_.EditMulticoloring.Dev.Ram.HS.setR_regs _root_.EditMulticoloring.Dev.Ram.HS.store_arr _root_.EditMulticoloring.Dev.Ram.HS.store_cur _root_.EditMulticoloring.Dev.Ram.HS.store_out _root_.EditMulticoloring.Dev.Ram.HS.store_regs _root_.EditMulticoloring.Dev.Ram.arith_add _root_.EditMulticoloring.Dev.Ram.arith_div _root_.EditMulticoloring.Dev.Ram.arith_lt _root_.EditMulticoloring.Dev.Ram.arith_mod _root_.EditMulticoloring.Dev.Ram.arith_mul _root_.EditMulticoloring.Dev.Ram.arith_sub _root_.EditMulticoloring.Dev.Ram.arith_xor _root_.EditMulticoloring.Dev.Ram.bits_one _root_.EditMulticoloring.Dev.Ram.bits_zero _root_.EditMulticoloring.Dev.Ram.cost_ald _root_.EditMulticoloring.Dev.Ram.cost_ar _root_.EditMulticoloring.Dev.Ram.cost_ast _root_.EditMulticoloring.Dev.Ram.cost_cp _root_.EditMulticoloring.Dev.Ram.cost_em _root_.EditMulticoloring.Dev.Ram.cost_ifz _root_.EditMulticoloring.Dev.Ram.cost_lit _root_.EditMulticoloring.Dev.Ram.cost_rd _root_.EditMulticoloring.Dev.Ram.cost_seq _root_.EditMulticoloring.Dev.Ram.cost_seqs_cons _root_.EditMulticoloring.Dev.Ram.cost_seqs_nil _root_.EditMulticoloring.Dev.Ram.cost_skip _root_.EditMulticoloring.Dev.Ram.exec_ald _root_.EditMulticoloring.Dev.Ram.exec_ar _root_.EditMulticoloring.Dev.Ram.exec_ast _root_.EditMulticoloring.Dev.Ram.exec_cp _root_.EditMulticoloring.Dev.Ram.exec_em _root_.EditMulticoloring.Dev.Ram.exec_ifz _root_.EditMulticoloring.Dev.Ram.exec_lit _root_.EditMulticoloring.Dev.Ram.exec_rd _root_.EditMulticoloring.Dev.Ram.exec_seq _root_.EditMulticoloring.Dev.Ram.exec_seqs_cons _root_.EditMulticoloring.Dev.Ram.exec_seqs_nil _root_.EditMulticoloring.Dev.Ram.exec_skip _root_.EditMulticoloring.Dev.Ram.forLoop_emits _root_.EditMulticoloring.Dev.Ram.forLoop_reads _root_.EditMulticoloring.Dev.Ram.forLoop_stores
/-!
# Compiling `Cmd` to `RAM.Program` (q379, Part F)

Design:
* user register `r` ↦ RAM register `2 * r` (so user register 0 holds `n` initially);
  RAM register `1` holds the constant 1, register `3` is the scratch register for
  computing `Nat.pair`, and register `2 * k + 7` is the loop counter at nesting depth `k`;
* `compile (c : Cmd) (k base : ℕ) : List RAM.Instruction` with absolute jump targets;
* the program is a prologue (set the hidden constant 1), the compiled body, then
  `jumpZero (2*flag) → reject`, `accept`, `reject`;
* `B := RAM.bits M` where `M` bounds every pc and every instruction field of the program;
* the simulation lemma `sim` by induction on `c` (fuel additivity of `RAM.run`), with the RAM
  cost increase bounded by `Cmd.cost`.
-/

set_option autoImplicit false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

namespace Sim

open RAM

/-! ### Bit-length facts -/

theorem bits_pos (a : ℕ) : 1 ≤ bits a := Nat.le_add_left 1 _

theorem lt_two_pow_bits (a : ℕ) : a < 2 ^ bits a := Nat.lt_log2_self

theorem bits_le_of_lt {a k : ℕ} (h : a < 2 ^ k) (hk : 1 ≤ k) : bits a ≤ k := by
  unfold bits
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [Nat.log2_zero]; omega
  · have := (Nat.log2_lt (Nat.pos_iff_ne_zero.mp ha)).2 h
    omega

theorem bits_mono {a b : ℕ} (h : a ≤ b) : bits a ≤ bits b :=
  bits_le_of_lt (lt_of_le_of_lt h (lt_two_pow_bits b)) (bits_pos b)

theorem bits_pair_le {a b W : ℕ} (ha : bits a ≤ W) (hb : bits b ≤ W) :
    bits (Nat.pair a b) ≤ 2 * W := by
  have ha' : a < 2 ^ W := lt_of_lt_of_le (lt_two_pow_bits a) (Nat.pow_le_pow_right (by norm_num) ha)
  have hb' : b < 2 ^ W := lt_of_lt_of_le (lt_two_pow_bits b) (Nat.pow_le_pow_right (by norm_num) hb)
  have hm : max a b + 1 ≤ 2 ^ W := by omega
  apply bits_le_of_lt _ (by have := bits_pos a; omega)
  calc Nat.pair a b < (max a b + 1) ^ 2 := Nat.pair_lt_max_add_one_sq a b
    _ ≤ (2 ^ W) ^ 2 := Nat.pow_le_pow_left hm 2
    _ = 2 ^ (2 * W) := by rw [← pow_mul, mul_comm]

theorem arithmeticCost_le (op : Arithmetic) {a b W : ℕ} (ha : bits a ≤ W) (hb : bits b ≤ W) :
    arithmeticCost op a b ≤ (W + 1) ^ 2 := by
  have h1 : (bits a + 1) * (bits b + 1) ≤ (W + 1) ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have h2 : bits a + bits b + 1 ≤ (W + 1) ^ 2 := by nlinarith
  cases op <;> simp only [arithmeticCost] <;> assumption

/-! ### Running -/

variable {q : ℕ} {P : Program} {input : Word q}

theorem step_eq {s : State} {ins : Instruction} (hs : s.status = none) (h : P[s.pc]? = some ins) :
    step P input s = stepI input ins s := by
  unfold step
  rw [if_neg (by simp [hs]), h]
  cases ins <;> rfl

theorem run_add (a b : ℕ) (s : State) :
    run P input (a + b) s = run P input b (run P input a s) := by
  induction a generalizing s with
  | zero => simp [run]
  | succ a ih => rw [Nat.add_right_comm]; exact ih _

theorem run_succ {s : State} {ins : Instruction} (n : ℕ) (hs : s.status = none)
    (h : P[s.pc]? = some ins) : run P input (n + 1) s = run P input n (stepI input ins s) := by
  show run P input n (step P input s) = _
  rw [step_eq hs h]

/-! ### Program embedding and field bounds -/

theorem Emb.left {base : ℕ} {L₁ L₂ : List Instruction} (h : Emb P base (L₁ ++ L₂)) :
    Emb P base L₁ := fun i hi => by
  rw [h i (by simp; omega), List.getElem?_append_left hi]

theorem Emb.right {base : ℕ} {L₁ L₂ : List Instruction} (h : Emb P base (L₁ ++ L₂)) :
    Emb P (base + L₁.length) L₂ := fun i hi => by
  rw [Nat.add_assoc, h _ (by simp; omega), List.getElem?_append_right (by omega)]
  simp

theorem Emb.head {base : ℕ} {x : Instruction} {L : List Instruction} (h : Emb P base (x :: L)) :
    P[base]? = some x := by simpa using h 0 (by simp)

theorem Emb.tail {base : ℕ} {x : Instruction} {L : List Instruction} (h : Emb P base (x :: L)) :
    Emb P (base + 1) L := fun i hi => by
  rw [Nat.add_assoc, Nat.add_comm 1 i, h (i + 1) (by simp; omega)]
  simp

theorem Good.pc {M pc : ℕ} {ins : Instruction} (hG : Good P M) (h : P[pc]? = some ins) :
    bits pc ≤ bits M := by
  have := (List.getElem?_eq_some_iff.mp h).1
  exact bits_mono (by have := hG.1; omega)

theorem Good.fs {M pc : ℕ} {ins : Instruction} (hG : Good P M) (h : P[pc]? = some ins) :
    fsum ins ≤ M := hG.2 _ (List.mem_of_getElem? h)

/-! ### The state relation -/


/-! ### The compiler -/

theorem length_compile (c : Cmd) (k base : ℕ) : (compile c k base).length = len c := by
  induction c generalizing k base with
  | prim p => cases p <;> simp [compile, primCode, primLen, len, pairCode]
  | seq c₁ c₂ ih₁ ih₂ => simp [compile, len, ih₁, ih₂]
  | ifz a c₁ c₂ ih₁ ih₂ => simp [compile, len, ih₁, ih₂]; try omega
  | loop a c ih => simp [compile, len, ih]; try omega
  | skip => simp [compile, len]

/-! ### Reachability with cost -/

theorem Reach.trans {t : State} {s₁ s₂ : HS} {pc₁ pc₂ c₁ c₂ k : ℕ}
    (h₁ : Reach P input t s₁ pc₁ c₁ k)
    (h₂ : ∀ t₁ : State, Rel s₁ t₁ → t₁.pc = pc₁ → Reach P input t₁ s₂ pc₂ c₂ k) :
    Reach P input t s₂ pc₂ (c₁ + c₂) k := by
  obtain ⟨f₁, r₁, p₁, k₁, fr₁⟩ := h₁
  obtain ⟨f₂, r₂, p₂, k₂, fr₂⟩ := h₂ _ r₁ p₁
  refine ⟨f₁ + f₂, ?_, ?_, ?_, ?_⟩ <;> rw [run_add]
  · exact r₂
  · exact p₂
  · omega
  · intro j hj; rw [fr₂ j hj, fr₁ j hj]

theorem Reach.mono {t : State} {s : HS} {pc c c' k : ℕ} (h : Reach P input t s pc c k)
    (hc : c ≤ c') : Reach P input t s pc c' k := by
  obtain ⟨f, r, p, k', fr⟩ := h
  exact ⟨f, r, p, by omega, fr⟩

theorem Reach.one {t : State} {s s' : HS} {ins : Instruction} {pc cst k : ℕ} (hr : Rel s t)
    (h : P[t.pc]? = some ins) (r' : Rel s' (stepI input ins t)) (hpc : (stepI input ins t).pc = pc)
    (hc : (stepI input ins t).cost ≤ t.cost + cst)
    (hf : ∀ j < k, (stepI input ins t).registers (2 * j + 7) = t.registers (2 * j + 7)) :
    Reach P input t s' pc cst k :=
  ⟨1, by rw [run_succ 0 hr.st h]; exact r', by rw [run_succ 0 hr.st h]; exact hpc,
    by rw [run_succ 0 hr.st h]; exact hc, by rw [run_succ 0 hr.st h]; exact hf⟩

theorem Reach.refl {t : State} {s : HS} {k : ℕ} (hr : Rel s t) : Reach P input t s t.pc 0 k :=
  ⟨0, hr, rfl, by simp [run], fun _ _ => rfl⟩

/-! ### Register-update facts -/

theorem setReg_even {s : HS} {t : State} (h : Rel s t) (d v r : ℕ) :
    setReg t (2 * d) v (2 * r) = Function.update s.regs d v r := by
  unfold setReg Function.update
  by_cases hr : r = d
  · subst hr; simp
  · rw [if_neg (by omega), dif_neg hr, h.reg]

theorem setReg_odd (t : State) (d v r : ℕ) : setReg t (2 * d) v (2 * r + 1) = t.registers (2 * r + 1) := by
  unfold setReg; rw [if_neg (by omega)]


/-! ### Primitives -/

section prims

variable {M k base : ℕ} {s : HS} {t : State}

theorem sim_lit (hG : Good P M) (hr : Rel s t) (hpc : t.pc = base) (d v : ℕ)
    (hE : Emb P base (primCode base (.lit d v))) :
    Reach P input t ((Prim.lit d v).exec (inputAt input) s) (base + 1)
      (kappa (bits M) ((Prim.lit d v).wt (inputAt input) s)) k := by
  have h0 : P[t.pc]? = some (.literal (2 * d) v) := hpc ▸ hE.head
  have hb := hG.pc h0
  have hf := bits_mono (show 2 * d ≤ M by have := hG.fs h0; simp [fsum] at this; omega)
  apply Reach.one hr h0
  · exact ⟨fun r => setReg_even hr d v r, (setReg_odd t d v 0).trans hr.one, hr.mem, hr.cur, hr.out, hr.st⟩
  · simp [stepI, hpc]
  · simp only [stepI, Prim.wt]; unfold kappa; nlinarith
  · intro j _; simp only [stepI]; exact setReg_odd t d v (j + 3)

theorem sim_copy (hG : Good P M) (hr : Rel s t) (hpc : t.pc = base) (d a : ℕ)
    (hE : Emb P base (primCode base (.copy d a))) :
    Reach P input t ((Prim.copy d a).exec (inputAt input) s) (base + 1)
      (kappa (bits M) ((Prim.copy d a).wt (inputAt input) s)) k := by
  have h0 : P[t.pc]? = some (.copy (2 * d) (2 * a)) := hpc ▸ hE.head
  have hb := hG.pc h0
  have hf := hG.fs h0; simp only [fsum] at hf
  have hf1 := bits_mono (show 2 * d ≤ M by omega)
  have hf2 := bits_mono (show 2 * a ≤ M by omega)
  apply Reach.one hr h0
  · refine ⟨fun r => ?_, (setReg_odd t d _ 0).trans hr.one, hr.mem, hr.cur, hr.out, hr.st⟩
    simp only [stepI, Prim.exec]; rw [setReg_even hr, hr.reg]
  · simp [stepI, hpc]
  · simp only [stepI, Prim.wt, hr.reg]; unfold kappa; nlinarith
  · intro j _; simp only [stepI]; exact setReg_odd t d _ (j + 3)

theorem sim_arith (hG : Good P M) (hr : Rel s t) (hpc : t.pc = base) (op : Arithmetic) (d a b : ℕ)
    (hE : Emb P base (primCode base (.arith op d a b))) :
    Reach P input t ((Prim.arith op d a b).exec (inputAt input) s) (base + 1)
      (kappa (bits M) ((Prim.arith op d a b).wt (inputAt input) s)) k := by
  have h0 : P[t.pc]? = some (.arithmetic op (2 * d) (2 * a) (2 * b)) := hpc ▸ hE.head
  have hb := hG.pc h0
  have hf := hG.fs h0; simp only [fsum] at hf
  have hf1 := bits_mono (show 2 * d ≤ M by omega)
  have hf2 := bits_mono (show 2 * a ≤ M by omega)
  have hf3 := bits_mono (show 2 * b ≤ M by omega)
  apply Reach.one hr h0
  · refine ⟨fun r => ?_, (setReg_odd t d _ 0).trans hr.one, hr.mem, hr.cur, hr.out, hr.st⟩
    simp only [stepI, Prim.exec]; rw [setReg_even hr, hr.reg, hr.reg]
  · simp [stepI, hpc]
  · simp only [stepI, Prim.wt, hr.reg]
    have := arithmeticCost_le op (bits_mono (Nat.le_add_right (s.regs a) (s.regs b)))
      (bits_mono (Nat.le_add_left (s.regs b) (s.regs a)))
    unfold kappa; nlinarith
  · intro j _; simp only [stepI]; exact setReg_odd t d _ (j + 3)

theorem sim_read (hG : Good P M) (hr : Rel s t) (hpc : t.pc = base) (d : ℕ)
    (hE : Emb P base (primCode base (.read d))) :
    Reach P input t ((Prim.read d).exec (inputAt input) s) (base + 1)
      (kappa (bits M) ((Prim.read d).wt (inputAt input) s)) k := by
  have h0 : P[t.pc]? = some (.read (2 * d)) := hpc ▸ hE.head
  have hb := hG.pc h0
  have hf := hG.fs h0; simp only [fsum] at hf
  have hf1 := bits_mono (show 2 * d ≤ M by omega)
  apply Reach.one hr h0
  · refine ⟨fun r => ?_, (setReg_odd t d _ 0).trans hr.one, hr.mem, ?_, hr.out, hr.st⟩
    · simp only [stepI, Prim.exec]; rw [setReg_even hr, hr.cur]
    · simp only [stepI, Prim.exec]; rw [hr.cur]
  · simp [stepI, hpc]
  · simp only [stepI, Prim.wt, hr.cur]
    have := bits_mono (Nat.le_add_right s.cur (inputAt input s.cur))
    have := bits_mono (Nat.le_add_left (inputAt input s.cur) s.cur)
    unfold kappa; nlinarith
  · intro j _; simp only [stepI]; exact setReg_odd t d _ (j + 3)

theorem sim_emit (hG : Good P M) (hr : Rel s t) (hpc : t.pc = base) (a : ℕ)
    (hE : Emb P base (primCode base (.emit a))) :
    Reach P input t ((Prim.emit a).exec (inputAt input) s) (base + 1)
      (kappa (bits M) ((Prim.emit a).wt (inputAt input) s)) k := by
  have h0 : P[t.pc]? = some (.emit (2 * a)) := hpc ▸ hE.head
  have hb := hG.pc h0
  have hf := hG.fs h0; simp only [fsum] at hf
  have hf1 := bits_mono (show 2 * a ≤ M by omega)
  apply Reach.one hr h0
  · refine ⟨hr.reg, hr.one, hr.mem, hr.cur, ?_, hr.st⟩
    simp only [stepI, Prim.exec]; rw [hr.out, hr.reg]
  · simp [stepI, hpc]
  · simp only [stepI, Prim.wt, hr.out, hr.reg]
    have := bits_mono (Nat.le_add_right (s.regs a) s.out.length)
    have := bits_mono (Nat.le_add_left s.out.length (s.regs a))
    unfold kappa; nlinarith
  · intro j _; rfl

theorem pair_run (hG : Good P M) (hst : t.status = none) (hpc : t.pc = base) (x i : ℕ)
    (hE : Emb P base (pairCode x i base)) :
    ∃ t' : State, run P input 5 t = t' ∧ t'.pc = base + 8 ∧
      t'.registers = setReg t 3 (Nat.pair (t.registers (2 * x)) (t.registers (2 * i))) ∧
      t'.memory = t.memory ∧ t'.cursor = t.cursor ∧ t'.output = t.output ∧ t'.status = none ∧
      t'.cost ≤ t.cost + 20 * (bits M + 1) +
        4 * (bits (Nat.pair (t.registers (2 * x)) (t.registers (2 * i))) + 1) ^ 2 := by
  have L : ∀ j, j < 8 → P[base + j]? = (pairCode x i base)[j]? := fun j hj =>
    hE j (by simp [pairCode]; omega)
  have L0 : P[base]? = some (.arithmetic .lt 3 (2 * x) (2 * i)) := by simpa [pairCode] using L 0 (by norm_num)
  have L1 : P[base + 1]? = some (.jumpZero 3 (base + 5)) := by simpa [pairCode] using L 1 (by norm_num)
  have L2 : P[base + 2]? = some (.arithmetic .mul 3 (2 * i) (2 * i)) := by simpa [pairCode] using L 2 (by norm_num)
  have L3 : P[base + 3]? = some (.arithmetic .add 3 3 (2 * x)) := by simpa [pairCode] using L 3 (by norm_num)
  have L4 : P[base + 4]? = some (.jump (base + 8)) := by simpa [pairCode] using L 4 (by norm_num)
  have L5 : P[base + 5]? = some (.arithmetic .mul 3 (2 * x) (2 * x)) := by simpa [pairCode] using L 5 (by norm_num)
  have L6 : P[base + 6]? = some (.arithmetic .add 3 3 (2 * x)) := by simpa [pairCode] using L 6 (by norm_num)
  have L7 : P[base + 7]? = some (.arithmetic .add 3 3 (2 * i)) := by simpa [pairCode] using L 7 (by norm_num)
  have b0 := hG.pc L0
  have b1 := hG.pc L1
  have b2 := hG.pc L2
  have b3 := hG.pc L3
  have b4 := hG.pc L4
  have b5 := hG.pc L5
  have b6 := hG.pc L6
  have b7 := hG.pc L7
  have f1 := hG.fs L1; simp only [fsum] at f1
  have f4 := hG.fs L4; simp only [fsum] at f4
  have f5 := hG.fs L5; simp only [fsum] at f5
  have f7 := hG.fs L7; simp only [fsum] at f7
  have e3 := bits_mono (show 3 ≤ M by omega)
  have ex := bits_mono (show 2 * x ≤ M by omega)
  have ei := bits_mono (show 2 * i ≤ M by omega)
  have eb5 := bits_mono (show base + 5 ≤ M by omega)
  have eb8 := bits_mono (show base + 8 ≤ M by omega)
  have c1 := bits_mono (show base + 1 + 1 ≤ M by omega)
  have c2 := bits_mono (show base + 1 + 1 + 1 ≤ M by omega)
  have c3 := bits_mono (show base + 1 + 1 + 1 + 1 ≤ M by omega)
  have c5 := bits_mono (show base + 5 + 1 ≤ M by omega)
  have c6 := bits_mono (show base + 5 + 1 + 1 ≤ M by omega)
  have one1 : bits 1 ≤ 1 := bits_le_of_lt (by norm_num) le_rfl
  have zero1 : bits 0 ≤ 1 := bits_le_of_lt (by norm_num) le_rfl
  have hx3 : 2 * x ≠ 3 := by omega
  have hi3 : 2 * i ≠ 3 := by omega
  have ba : bits (t.registers (2 * x)) ≤ bits (Nat.pair (t.registers (2 * x)) (t.registers (2 * i))) :=
    bits_mono (Nat.left_le_pair _ _)
  have bb : bits (t.registers (2 * i)) ≤ bits (Nat.pair (t.registers (2 * x)) (t.registers (2 * i))) :=
    bits_mono (Nat.right_le_pair _ _)
  have b01 : ∀ v, v ≤ 1 → bits v ≤ bits (Nat.pair (t.registers (2 * x)) (t.registers (2 * i))) :=
    fun v hv => le_trans (bits_mono hv) (le_trans (bits_le_of_lt (by norm_num) le_rfl) (bits_pos _))
  have m1 : (bits (t.registers (2 * i)) + 1) * (bits (t.registers (2 * i)) + 1) ≤
      (bits (Nat.pair (t.registers (2 * x)) (t.registers (2 * i))) + 1) ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have m1' : (bits (t.registers (2 * x)) + 1) * (bits (t.registers (2 * x)) + 1) ≤
      (bits (Nat.pair (t.registers (2 * x)) (t.registers (2 * i))) + 1) ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have m2 : 2 * bits (Nat.pair (t.registers (2 * x)) (t.registers (2 * i))) + 2 ≤
      (bits (Nat.pair (t.registers (2 * x)) (t.registers (2 * i))) + 1) ^ 2 := by
    have := bits_pos (Nat.pair (t.registers (2 * x)) (t.registers (2 * i))); nlinarith
  have hrun : run P input 5 t = step P input (step P input (step P input (step P input
      (step P input t)))) := rfl
  refine ⟨_, rfl, ?_⟩
  rw [hrun, step_eq hst (hpc ▸ L0)]
  by_cases hab : t.registers (2 * x) < t.registers (2 * i)
  · have hp : Nat.pair (t.registers (2 * x)) (t.registers (2 * i)) =
        t.registers (2 * i) * t.registers (2 * i) + t.registers (2 * x) := by simp [Nat.pair, hab]
    have bbb : bits (t.registers (2 * i) * t.registers (2 * i)) ≤
        bits (Nat.pair (t.registers (2 * x)) (t.registers (2 * i))) := bits_mono (by rw [hp]; omega)
    rw [step_eq (s := stepI input (.arithmetic .lt 3 (2 * x) (2 * i)) t) (by simp [stepI, hst])
      (by convert L1 using 2; simp [stepI, hpc])]
    rw [step_eq (s := stepI input (.jumpZero 3 (base + 5))
        (stepI input (.arithmetic .lt 3 (2 * x) (2 * i)) t)) (by simp [stepI, hst])
      (by convert L2 using 2; simp [stepI, hpc, setReg, arithmeticValue, hab])]
    rw [step_eq (s := stepI input (.arithmetic .mul 3 (2 * i) (2 * i)) (stepI input (.jumpZero 3 (base + 5))
        (stepI input (.arithmetic .lt 3 (2 * x) (2 * i)) t))) (by simp [stepI, hst])
      (by convert L3 using 2; simp [stepI, hpc, setReg, arithmeticValue, hab])]
    rw [step_eq (s := stepI input (.arithmetic .add 3 3 (2 * x))
        (stepI input (.arithmetic .mul 3 (2 * i) (2 * i)) (stepI input (.jumpZero 3 (base + 5))
        (stepI input (.arithmetic .lt 3 (2 * x) (2 * i)) t)))) (by simp [stepI, hst])
      (by convert L4 using 2; simp [stepI, hpc, setReg, arithmeticValue, hab])]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [stepI]
    · funext r; by_cases hr : r = 3
      · subst hr; simp [stepI, setReg, arithmeticValue, hab, hp, hx3, hi3]
      · simp [stepI, setReg, hr]
    · simp [stepI]
    · simp [stepI]
    · simp [stepI]
    · simp [stepI, hst]
    · simp only [stepI, setReg, arithmeticValue, arithmeticCost, if_pos hab, hpc, if_true, hx3, hi3,
        if_false, one_ne_zero]
      linarith
  · have hp : Nat.pair (t.registers (2 * x)) (t.registers (2 * i)) =
        t.registers (2 * x) * t.registers (2 * x) + t.registers (2 * x) + t.registers (2 * i) := by
      simp [Nat.pair, hab]
    have baa : bits (t.registers (2 * x) * t.registers (2 * x)) ≤
        bits (Nat.pair (t.registers (2 * x)) (t.registers (2 * i))) := bits_mono (by rw [hp]; omega)
    have baa' : bits (t.registers (2 * x) * t.registers (2 * x) + t.registers (2 * x)) ≤
        bits (Nat.pair (t.registers (2 * x)) (t.registers (2 * i))) := bits_mono (by rw [hp]; omega)
    rw [step_eq (s := stepI input (.arithmetic .lt 3 (2 * x) (2 * i)) t) (by simp [stepI, hst])
      (by convert L1 using 2; simp [stepI, hpc])]
    rw [step_eq (s := stepI input (.jumpZero 3 (base + 5))
        (stepI input (.arithmetic .lt 3 (2 * x) (2 * i)) t)) (by simp [stepI, hst])
      (by convert L5 using 2; simp [stepI, hpc, setReg, arithmeticValue, hab])]
    rw [step_eq (s := stepI input (.arithmetic .mul 3 (2 * x) (2 * x)) (stepI input (.jumpZero 3 (base + 5))
        (stepI input (.arithmetic .lt 3 (2 * x) (2 * i)) t))) (by simp [stepI, hst])
      (by convert L6 using 2; simp [stepI, hpc, setReg, arithmeticValue, hab])]
    rw [step_eq (s := stepI input (.arithmetic .add 3 3 (2 * x))
        (stepI input (.arithmetic .mul 3 (2 * x) (2 * x)) (stepI input (.jumpZero 3 (base + 5))
        (stepI input (.arithmetic .lt 3 (2 * x) (2 * i)) t)))) (by simp [stepI, hst])
      (by convert L7 using 2; simp [stepI, hpc, setReg, arithmeticValue, hab])]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [stepI, setReg, arithmeticValue, hab]
    · funext r; by_cases hr : r = 3
      · subst hr; simp [stepI, setReg, arithmeticValue, hab, hp, hx3, hi3]
      · simp [stepI, setReg, hr]
    · simp [stepI]
    · simp [stepI]
    · simp [stepI]
    · simp [stepI, hst]
    · simp only [stepI, setReg, arithmeticValue, arithmeticCost, if_neg hab, hpc, if_true, hx3, hi3,
        if_false]
      linarith

theorem pair_cost_le {a b W B : ℕ} (ha : bits a ≤ W) (hb : bits b ≤ W) :
    20 * (B + 1) + 4 * (bits (Nat.pair a b) + 1) ^ 2 ≤ 20 * (B + 1) + 16 * (W + 2) ^ 2 := by
  have := bits_pair_le ha hb
  have : (bits (Nat.pair a b) + 1) ^ 2 ≤ 4 * (W + 2) ^ 2 := by nlinarith
  omega

theorem sim_aload (hG : Good P M) (hr : Rel s t) (hpc : t.pc = base) (d x i : ℕ)
    (hE : Emb P base (primCode base (.aload d x i))) :
    Reach P input t ((Prim.aload d x i).exec (inputAt input) s) (base + 9)
      (kappa (bits M) ((Prim.aload d x i).wt (inputAt input) s)) k := by
  obtain ⟨t', e, p', r', m', c', o', st', k'⟩ := pair_run (input := input) hG hr.st hpc x i hE.left
  have L8 : P[t'.pc]? = some (.load (2 * d) 3) := by
    have := hE.right.head; simpa [pairCode, p'] using this
  have hb := hG.pc L8
  have hf := hG.fs L8; simp only [fsum] at hf
  have hf1 := bits_mono (show 2 * d ≤ M by omega)
  have hf2 := bits_mono (show 3 ≤ M by omega)
  have h3 : t'.registers 3 = Nat.pair (s.regs x) (s.regs i) := by
    rw [r', ← hr.reg x, ← hr.reg i]; simp [setReg]
  refine ⟨5 + 1, ?_⟩
  rw [run_add, e, run_succ 0 st' L8]
  simp only [run]
  refine ⟨⟨fun r => ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [stepI, Prim.exec]
    rw [h3, m', hr.mem]
    unfold setReg Function.update
    by_cases hrd : r = d
    · subst hrd; simp
    · rw [if_neg (by omega), dif_neg hrd, r']; unfold setReg; rw [if_neg (by omega), hr.reg]
  · simp only [stepI]; unfold setReg; rw [if_neg (by omega), r']; unfold setReg
    rw [if_neg (by omega)]; exact hr.one
  · simp only [stepI]; rw [m', hr.mem]; rfl
  · simp only [stepI]; rw [c', hr.cur]; rfl
  · simp only [stepI]; rw [o', hr.out]; rfl
  · simp only [stepI]; exact st'
  · simp only [stepI]; rw [p']
  · simp only [stepI, Prim.wt, h3, m', hr.mem]
    rw [hr.reg x, hr.reg i] at k'
    have hW1 := bits_mono (show s.regs x ≤ s.regs x + s.regs i + s.mem (Nat.pair (s.regs x) (s.regs i)) by omega)
    have hW2 := bits_mono (show s.regs i ≤ s.regs x + s.regs i + s.mem (Nat.pair (s.regs x) (s.regs i)) by omega)
    have hW3 := bits_mono (show s.mem (Nat.pair (s.regs x) (s.regs i)) ≤
      s.regs x + s.regs i + s.mem (Nat.pair (s.regs x) (s.regs i)) by omega)
    have hp := bits_pair_le hW1 hW2
    have := pair_cost_le (B := bits M) hW1 hW2
    unfold kappa; nlinarith
  · intro j _; simp only [stepI]; unfold setReg; rw [if_neg (by omega), r']; unfold setReg
    rw [if_neg (by omega)]

theorem sim_astore (hG : Good P M) (hr : Rel s t) (hpc : t.pc = base) (x i v : ℕ)
    (hE : Emb P base (primCode base (.astore x i v))) :
    Reach P input t ((Prim.astore x i v).exec (inputAt input) s) (base + 9)
      (kappa (bits M) ((Prim.astore x i v).wt (inputAt input) s)) k := by
  obtain ⟨t', e, p', r', m', c', o', st', k'⟩ := pair_run (input := input) hG hr.st hpc x i hE.left
  have L8 : P[t'.pc]? = some (.store 3 (2 * v)) := by
    have := hE.right.head; simpa [pairCode, p'] using this
  have hb := hG.pc L8
  have hf := hG.fs L8; simp only [fsum] at hf
  have hf1 := bits_mono (show 2 * v ≤ M by omega)
  have hf2 := bits_mono (show 3 ≤ M by omega)
  have h3 : t'.registers 3 = Nat.pair (s.regs x) (s.regs i) := by
    rw [r', ← hr.reg x, ← hr.reg i]; simp [setReg]
  have hv : t'.registers (2 * v) = s.regs v := by
    rw [r']; unfold setReg; rw [if_neg (by omega), hr.reg]
  refine ⟨5 + 1, ?_⟩
  rw [run_add, e, run_succ 0 st' L8]
  simp only [run]
  refine ⟨⟨fun r => ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [stepI, Prim.exec]
    rw [r']; unfold setReg; rw [if_neg (by omega), hr.reg]
  · simp only [stepI]; rw [r']; unfold setReg; rw [if_neg (by omega)]; exact hr.one
  · simp only [stepI, Prim.exec]; rw [h3, hv, m', hr.mem]; funext a; simp [Function.update]
  · simp only [stepI]; rw [c', hr.cur]; rfl
  · simp only [stepI]; rw [o', hr.out]; rfl
  · simp only [stepI]; exact st'
  · simp only [stepI]; rw [p']
  · simp only [stepI, Prim.wt, h3, hv]
    rw [hr.reg x, hr.reg i] at k'
    have hW1 := bits_mono (show s.regs x ≤ s.regs x + s.regs i + s.regs v by omega)
    have hW2 := bits_mono (show s.regs i ≤ s.regs x + s.regs i + s.regs v by omega)
    have hW3 := bits_mono (show s.regs v ≤ s.regs x + s.regs i + s.regs v by omega)
    have hp := bits_pair_le hW1 hW2
    have := pair_cost_le (B := bits M) hW1 hW2
    unfold kappa; nlinarith
  · intro j _; simp only [stepI]; rw [r']; unfold setReg; rw [if_neg (by omega)]

theorem sim_prim (hG : Good P M) (hr : Rel s t) (hpc : t.pc = base) (p : Prim)
    (hE : Emb P base (primCode base p)) :
    Reach P input t (p.exec (inputAt input) s) (base + primLen p)
      (kappa (bits M) (p.wt (inputAt input) s)) k := by
  cases p with
  | lit d v => exact sim_lit hG hr hpc d v hE
  | copy d a => exact sim_copy hG hr hpc d a hE
  | arith op d a b => exact sim_arith hG hr hpc op d a b hE
  | aload d x i => exact sim_aload hG hr hpc d x i hE
  | astore x i v => exact sim_astore hG hr hpc x i v hE
  | read d => exact sim_read hG hr hpc d hE
  | emit a => exact sim_emit hG hr hpc a hE

end prims

/-! ### Structured commands -/

theorem Reach.trans_frame {t : State} {s₁ s₂ : HS} {pc₁ pc₂ c₁ c₂ k k₁ : ℕ}
    (h₁ : Reach P input t s₁ pc₁ c₁ k₁)
    (h₂ : ∀ t₁ : State, Rel s₁ t₁ → t₁.pc = pc₁ →
      (∀ j < k₁, t₁.registers (2 * j + 7) = t.registers (2 * j + 7)) → Reach P input t₁ s₂ pc₂ c₂ k)
    (hk : k ≤ k₁) :
    Reach P input t s₂ pc₂ (c₁ + c₂) k := by
  obtain ⟨f₁, r₁, p₁, k₁', fr₁⟩ := h₁
  obtain ⟨f₂, r₂, p₂, k₂, fr₂⟩ := h₂ _ r₁ p₁ fr₁
  refine ⟨f₁ + f₂, ?_, ?_, ?_, ?_⟩ <;> rw [run_add]
  · exact r₂
  · exact p₂
  · omega
  · intro j hj; rw [fr₂ j hj, fr₁ j (by omega)]

theorem Reach.cons {t : State} {s' : HS} {ins : Instruction} {pc c₀ c k : ℕ} (hst : t.status = none)
    (h : P[t.pc]? = some ins) (hc : (stepI input ins t).cost ≤ t.cost + c₀)
    (hf : ∀ j < k, (stepI input ins t).registers (2 * j + 7) = t.registers (2 * j + 7))
    (hR : Reach P input (stepI input ins t) s' pc c k) : Reach P input t s' pc (c₀ + c) k := by
  obtain ⟨f, r, p, k', fr⟩ := hR
  refine ⟨f + 1, ?_, ?_, ?_, ?_⟩ <;> rw [run_succ f hst h]
  · exact r
  · exact p
  · omega
  · intro j hj; rw [fr j hj, hf j hj]

theorem Reach.congr_pc {t : State} {s : HS} {pc pc' c k : ℕ} (h : Reach P input t s pc c k)
    (e : pc = pc') : Reach P input t s pc' c k := e ▸ h

variable {M : ℕ}

theorem simSpec_prim (hG : Good P M) (p : Prim) : SimSpec P input M (.prim p) :=
  fun _ _ _ _ hE hr hpc => sim_prim hG hr hpc p hE

theorem simSpec_skip : SimSpec P input M .skip :=
  fun _ _ _ _ _ hr hpc => by
    simpa [Cmd.exec, Cmd.cost, len, hpc] using (Reach.refl (P := P) (input := input) hr)

theorem simSpec_seq {c₁ c₂ : Cmd} (h₁ : SimSpec P input M c₁) (h₂ : SimSpec P input M c₂) :
    SimSpec P input M (.seq c₁ c₂) := by
  intro k base s t hE hr hpc
  simp only [compile] at hE
  have hE₂ := hE.right
  rw [length_compile] at hE₂
  have := (h₁ k base s t hE.left hr hpc).trans fun t₁ r₁ p₁ => h₂ k (base + len c₁) _ t₁ hE₂ r₁ p₁
  simpa [Cmd.exec, Cmd.cost, len, Nat.add_assoc] using this

theorem Emb.congr {b b' : ℕ} {L : List Instruction} (h : Emb P b L) (e : b = b') : Emb P b' L := e ▸ h

theorem kappa_ge' (B W : ℕ) : 20 * (B + 1) + 4 * W + 4 ≤ kappa B W := by
  unfold kappa; nlinarith

theorem simSpec_ifz (hG : Good P M) {a : ℕ} {c₁ c₂ : Cmd} (h₁ : SimSpec P input M c₁)
    (h₂ : SimSpec P input M c₂) : SimSpec P input M (.ifz a c₁ c₂) := by
  intro k base s t hE hr hpc
  simp only [compile] at hE
  have E0 : P[t.pc]? = some (.jumpZero (2 * a) (base + len c₂ + 2)) := hpc ▸ hE.left.left.left.head
  have E2 := hE.left.left.right.congr (b' := base + 1) (by simp)
  have E3 : P[base + 1 + len c₂]? = some (.jump (base + len c₂ + 2 + len c₁)) := by
    have := hE.left.right.head; convert this using 2; simp [length_compile]; omega
  have E1 := hE.right.congr (b' := base + len c₂ + 2) (by simp [length_compile]; omega)
  have b0 := hG.pc E0
  have f0 := hG.fs E0; simp only [fsum] at f0
  have b3 := hG.pc E3
  have f3 := hG.fs E3; simp only [fsum] at f3
  have ea := bits_mono (show 2 * a ≤ M by omega)
  have et := bits_mono (show base + len c₂ + 2 ≤ M by omega)
  have ee := bits_mono (show base + len c₂ + 2 + len c₁ ≤ M by omega)
  have hk := kappa_ge' (bits M) (bits (s.regs a))
  have hr0 : Rel s (stepI input (.jumpZero (2 * a) (base + len c₂ + 2)) t) :=
    ⟨hr.reg, hr.one, hr.mem, hr.cur, hr.out, hr.st⟩
  have hc0 : (stepI input (.jumpZero (2 * a) (base + len c₂ + 2)) t).cost ≤
      t.cost + (3 * (bits M + 1) + bits (s.regs a)) := by
    simp only [stepI, hr.reg]; omega
  by_cases hz : s.regs a = 0
  · have R := Reach.cons hr.st E0 hc0 (fun _ _ => rfl)
      (h₁ k _ s _ E1 hr0 (by simp [stepI, hr.reg, hz]))
    simp only [Cmd.exec, Cmd.cost, len]; rw [if_pos hz, if_pos hz]
    exact (R.congr_pc (by omega)).mono (by omega)
  · have R := Reach.cons hr.st E0 hc0 (fun _ _ => rfl)
      ((h₂ k (base + 1) s _ E2 hr0 (by simp [stepI, hr.reg, hz, hpc])).trans fun t₁ r₁ p₁ =>
        Reach.cons (c := 0) r₁.st (p₁ ▸ E3)
          (show _ ≤ t₁.cost + 2 * (bits M + 1) by simp only [stepI, p₁]; omega) (fun _ _ => rfl)
          (Reach.refl (s := Cmd.exec (inputAt input) c₂ s)
            (t := stepI input (.jump (base + len c₂ + 2 + len c₁)) t₁) ⟨r₁.reg, r₁.one, r₁.mem, r₁.cur, r₁.out, r₁.st⟩))
    simp only [Cmd.exec, Cmd.cost, len]; rw [if_neg hz, if_neg hz]
    exact (R.congr_pc (by simp; omega)).mono (by omega)

theorem loop_iter (hG : Good P M) {a k base : ℕ} {c : Cmd} (hc : SimSpec P input M c)
    (hE : Emb P base (compile (.loop a c) k base)) :
    ∀ (v : ℕ) (s : HS) (t : State), Rel s t → t.pc = base + 1 → t.registers (2 * k + 7) = v →
      Reach P input t ((Cmd.exec (inputAt input) c)^[v] s) (base + len c + 4)
        (loopCost (bits M) (Cmd.exec (inputAt input) c) (Cmd.cost (inputAt input) (bits M) c) v s) k := by
  simp only [compile] at hE
  have Ejz : P[base + 1]? = some (.jumpZero (2 * k + 7) (base + len c + 4)) := hE.left.left.tail.head
  have EC := hE.left.right.congr (b' := base + 2) (by simp)
  have Esub : P[base + 2 + len c]? = some (.arithmetic .sub (2 * k + 7) (2 * k + 7) 1) := by
    have := hE.right.head; convert this using 2; simp [length_compile]; omega
  have Ejmp : P[base + 2 + len c + 1]? = some (.jump (base + 1)) := by
    have := hE.right.tail.head; convert this using 2; simp [length_compile]; omega
  have b1 := hG.pc Ejz
  have f1 := hG.fs Ejz; simp only [fsum] at f1
  have b2 := hG.pc Esub
  have f2 := hG.fs Esub; simp only [fsum] at f2
  have b3 := hG.pc Ejmp
  have f3 := hG.fs Ejmp; simp only [fsum] at f3
  have ek := bits_mono (show 2 * k + 7 ≤ M by omega)
  have et := bits_mono (show base + len c + 4 ≤ M by omega)
  have e1 := bits_mono (show 1 ≤ M by omega)
  have eb := bits_mono (show base + 1 ≤ M by omega)
  intro v
  induction v with
  | zero =>
    intro s t hr hpc hv
    have hk := kappa_ge' (bits M) 0
    have z1 : bits 0 ≤ 1 := bits_le_of_lt (by norm_num) le_rfl
    apply Reach.one (ins := .jumpZero (2 * k + 7) (base + len c + 4)) hr (hpc ▸ Ejz) ⟨hr.reg, hr.one, hr.mem, hr.cur, hr.out, hr.st⟩
    · simp [stepI, hv]
    · simp only [loopCost, stepI, hv, hpc]; omega
    · intro _ _; rfl
  | succ v ih =>
    intro s t hr hpc hv
    have hk := kappa_ge' (bits M) (bits (v + 1))
    have one1 : bits 1 ≤ 1 := bits_le_of_lt (by norm_num) le_rfl
    have R := Reach.cons (c₀ := 3 * (bits M + 1) + bits (v + 1)) hr.st (hpc ▸ Ejz)
      (by simp only [stepI, hv, hpc]; omega) (fun _ _ => rfl)
      (Reach.trans_frame (k₁ := k + 1)
        (hc (k + 1) (base + 2) s (stepI input (.jumpZero (2 * k + 7) (base + len c + 4)) t) EC ⟨hr.reg, hr.one, hr.mem, hr.cur, hr.out, hr.st⟩
          (by simp [stepI, hv, hpc]))
        (fun t₂ r₂ p₂ fr₂ => by
          have hv₂ : t₂.registers (2 * k + 7) = v + 1 := by
            rw [fr₂ k (by omega)]; simpa [stepI] using hv
          have L2 : P[t₂.pc]? = some (.arithmetic .sub (2 * k + 7) (2 * k + 7) 1) := p₂ ▸ Esub
          set t₃ := stepI input (.arithmetic .sub (2 * k + 7) (2 * k + 7) 1) t₂ with ht₃
          have r₃ : Rel (Cmd.exec (inputAt input) c s) t₃ := by
            refine ⟨fun r => ?_, ?_, r₂.mem, r₂.cur, r₂.out, r₂.st⟩
            · simp only [ht₃, stepI]; unfold setReg; rw [if_neg (by omega)]; exact r₂.reg r
            · simp only [ht₃, stepI]; unfold setReg; rw [if_neg (by omega)]; exact r₂.one
          have hv₃ : t₃.registers (2 * k + 7) = v := by
            simp [ht₃, stepI, setReg, arithmeticValue, hv₂, r₂.one]
          have L3 : P[t₃.pc]? = some (.jump (base + 1)) := by
            convert Ejmp using 2; simp [ht₃, stepI, p₂]
          have c3 : t₃.cost ≤ t₂.cost + (4 * (bits M + 1) + bits (v + 1)) := by
            simp only [ht₃, stepI, arithmeticCost, hv₂, r₂.one, p₂]; omega
          have f3 : ∀ j < k, t₃.registers (2 * j + 7) = t₂.registers (2 * j + 7) := by
            intro j hj; simp only [ht₃, stepI]; unfold setReg; rw [if_neg (by omega)]
          have R4 := Reach.cons (c₀ := 2 * (bits M + 1)) r₃.st L3
            (by simp only [stepI]; rw [show t₃.pc = base + 2 + len c + 1 by simp [ht₃, stepI, p₂]]; omega)
            (fun _ _ => rfl)
            (ih (Cmd.exec (inputAt input) c s) _ ⟨r₃.reg, r₃.one, r₃.mem, r₃.cur, r₃.out, r₃.st⟩
              (by simp [stepI]) (by simpa [stepI] using hv₃))
          have := Reach.cons (c₀ := 4 * (bits M + 1) + bits (v + 1)) r₂.st L2 c3 f3 R4
          exact this)
        (by omega))
    rw [Function.iterate_succ_apply]
    simp only [loopCost]
    exact R.mono (by omega)

theorem simSpec_loop (hG : Good P M) {a : ℕ} {c : Cmd} (hc : SimSpec P input M c) :
    SimSpec P input M (.loop a c) := by
  intro k base s t hE hr hpc
  have hE' := hE
  simp only [compile] at hE'
  have Ecp : P[t.pc]? = some (.copy (2 * k + 7) (2 * a)) := hpc ▸ hE'.left.left.head
  have b0 := hG.pc Ecp
  have f0 := hG.fs Ecp; simp only [fsum] at f0
  have ek := bits_mono (show 2 * k + 7 ≤ M by omega)
  have ea := bits_mono (show 2 * a ≤ M by omega)
  have hk := kappa_ge' (bits M) (bits (s.regs a))
  have R := Reach.cons (c₀ := 3 * (bits M + 1) + bits (s.regs a)) hr.st Ecp
    (by simp only [stepI, hr.reg]; omega)
    (fun j hj => by simp only [stepI]; unfold setReg; rw [if_neg (by omega)])
    (loop_iter hG hc hE (s.regs a) s _
      ⟨fun r => by simp only [stepI]; unfold setReg; rw [if_neg (by omega)]; exact hr.reg r,
        by simp only [stepI]; unfold setReg; rw [if_neg (by omega)]; exact hr.one,
        hr.mem, hr.cur, hr.out, hr.st⟩
      (by simp [stepI, hpc]) (by simp [stepI, setReg, hr.reg]))
  simp only [Cmd.exec, Cmd.cost, len]
  exact (R.congr_pc (by omega)).mono (by omega)

theorem simSpec (hG : Good P M) (c : Cmd) : SimSpec P input M c := by
  induction c with
  | prim p => exact simSpec_prim hG p
  | seq c₁ c₂ ih₁ ih₂ => exact simSpec_seq ih₁ ih₂
  | ifz a c₁ c₂ ih₁ ih₂ => exact simSpec_ifz hG ih₁ ih₂
  | loop a c ih => exact simSpec_loop hG ih
  | skip => exact simSpec_skip

theorem good_progBound (P : Program) : Good P (progBound P) :=
  ⟨Nat.le_add_right _ _, fun _ h =>
    le_trans (List.le_sum_of_mem (List.mem_map_of_mem h)) (Nat.le_add_left _ _)⟩

theorem emb_self (P : Program) : Emb P 0 P := fun i _ => by simp

end Sim

open Sim in
theorem toProgram_spec (c : Cmd) (flag : ℕ) :
    ∃ (P : RAM.Program) (B K0 : ℕ), ∀ {q : ℕ} (input : Word q) (n : ℕ),
      ∃ fuel : ℕ,
        (RAM.run P input fuel (RAM.initial n)).status =
            some (decide ((c.exec (RAM.inputAt input) (HS.init n)).regs flag ≠ 0)) ∧
        (RAM.run P input fuel (RAM.initial n)).output =
            (c.exec (RAM.inputAt input) (HS.init n)).out ∧
        (RAM.run P input fuel (RAM.initial n)).cost ≤
            RAM.bits n + K0 + c.cost (RAM.inputAt input) B (HS.init n) +
              RAM.bits ((c.exec (RAM.inputAt input) (HS.init n)).regs flag) := by
  refine ⟨toProg c flag, RAM.bits (progBound (toProg c flag)),
    4 + 5 * (RAM.bits (progBound (toProg c flag)) + 1), ?_⟩
  intro q input n
  set P := toProg c flag with hP
  set M := progBound P with hM
  have hG : Good P M := good_progBound P
  have E : Emb P 0 ([.literal 1 1] ++ compile c 0 1 ++ [.jumpZero (2 * flag) (len c + 3), .accept, .reject]) :=
    emb_self P
  have L0 : P[0]? = some (.literal 1 1) := E.left.left.head
  have EC := E.left.right.congr (b' := 1) (by simp)
  have Ljz : P[1 + len c]? = some (.jumpZero (2 * flag) (len c + 3)) := by
    have := E.right.head; convert this using 2; simp [length_compile]; try omega
  have Lacc : P[1 + len c + 1]? = some .accept := by
    have := E.right.tail.head; convert this using 2; simp [length_compile]; try omega
  have Lrej : P[len c + 3]? = some .reject := by
    have := E.right.tail.tail.head; convert this using 2; simp [length_compile]; try omega
  have bjz := hG.pc Ljz
  have fjz := hG.fs Ljz; simp only [fsum] at fjz
  have bacc := hG.pc Lacc
  have brej := hG.pc Lrej
  have ef := _root_.EditMulticoloring.Dev.Ram.Sim.bits_mono (show 2 * flag ≤ M by omega)
  have et := _root_.EditMulticoloring.Dev.Ram.Sim.bits_mono (show len c + 3 ≤ M by omega)
  have one1 : RAM.bits 1 ≤ 1 := bits_le_of_lt (by norm_num) le_rfl
  have zero1 : RAM.bits 0 ≤ 1 := bits_le_of_lt (by norm_num) le_rfl
  set t₁ := stepI input (.literal 1 1) (RAM.initial n) with ht₁
  have r₁ : Rel (HS.init n) t₁ := by
    refine ⟨fun r => ?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp only [ht₁, stepI, RAM.setReg, RAM.initial, HS.init]
      rw [if_neg (by omega)]
      by_cases hr : r = 0 <;> simp [hr]
    · simp [ht₁, stepI, RAM.setReg]
  obtain ⟨f, r₂, p₂, c₂, -⟩ := simSpec (input := input) hG c 0 1 (HS.init n) t₁ EC r₁ (by simp [ht₁, stepI, RAM.initial])
  set t₂ := RAM.run P input f t₁ with ht₂
  set s' := c.exec (RAM.inputAt input) (HS.init n) with hs'
  have hrun : RAM.run P input (1 + f + 2) (RAM.initial n) = RAM.run P input 2 t₂ := by
    rw [run_add, run_add, run_succ 0 rfl L0]; rfl
  have c₁ : t₁.cost ≤ RAM.bits n + 4 := by
    simp only [ht₁, stepI, RAM.initial]; omega
  have hjz : P[t₂.pc]? = some (.jumpZero (2 * flag) (len c + 3)) := by rw [p₂]; exact Ljz
  refine ⟨1 + f + 2, ?_⟩
  rw [hrun, run_succ 1 r₂.st hjz]
  set t₃ := stepI input (.jumpZero (2 * flag) (len c + 3)) t₂ with ht₃
  have c₃ : t₃.cost ≤ t₂.cost + 3 * (RAM.bits M + 1) + RAM.bits (s'.regs flag) := by
    simp only [ht₃, stepI, r₂.reg, p₂]; omega
  by_cases hz : s'.regs flag = 0
  · have L3 : P[t₃.pc]? = some .reject := by
      convert Lrej using 2; simp [ht₃, stepI, r₂.reg, hz]
    rw [run_succ 0 (by simp [ht₃, stepI, r₂.st]) L3]
    refine ⟨?_, ?_, ?_⟩
    · simp [RAM.run, stepI, hz]
    · simp [RAM.run, stepI, ht₃, r₂.out]
    · have : t₃.pc = len c + 3 := by simp [ht₃, stepI, r₂.reg, hz]
      simp only [RAM.run, stepI, this]
      omega
  · have L3 : P[t₃.pc]? = some .accept := by
      convert Lacc using 2; simp [ht₃, stepI, r₂.reg, hz, p₂]
    rw [run_succ 0 (by simp [ht₃, stepI, r₂.st]) L3]
    refine ⟨?_, ?_, ?_⟩
    · simp [RAM.run, stepI, hz]
    · simp [RAM.run, stepI, ht₃, r₂.out]
    · have : t₃.pc = 1 + len c + 1 := by simp [ht₃, stepI, r₂.reg, hz, p₂]
      simp only [RAM.run, stepI, this]
      omega

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamTop1
/-!
# Part A (q379), file 1: an asymptotic toolkit and size bounds for the parameters

`Big f a d` says `f n ≤ C * n ^ a * (bits n) ^ d` for all large `n` (with some constant `C`).
It is closed under sums, products, powers, `bits` (polynomial arguments give `Big _ 0 1`,
`q ^ e` gives the exponents of `e`) and `kappa`.  The size bounds of the fields of
`parameters q t n` are proved in this form.
-/

set_option autoImplicit false

namespace EditMulticoloring.Dev.Ram.Top

open EditMulticoloring.Code

/-! ## Bit lengths -/

theorem bits_eq (a : ℕ) : RAM.bits a = Nat.log 2 a + 1 := by
  unfold RAM.bits; rw [Nat.log2_eq_log_two]

theorem lt_two_pow_bits' (a : ℕ) : a < 2 ^ RAM.bits a := by
  rw [bits_eq]; exact Nat.lt_pow_succ_log_self (by norm_num) a

theorem bits_le_of_lt' {a k : ℕ} (h : a < 2 ^ k) (hk : 1 ≤ k) : RAM.bits a ≤ k := by
  rw [bits_eq]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp; omega
  · have := Nat.log_lt_of_lt_pow (by omega) h; omega

theorem bits_le_self {a : ℕ} (ha : 1 ≤ a) : RAM.bits a ≤ a :=
  bits_le_of_lt' Nat.lt_two_pow_self ha

theorem two_le_two_pow_bits (a : ℕ) : 2 ≤ 2 ^ RAM.bits a := by
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ RAM.bits a := Nat.pow_le_pow_right (by norm_num) (one_le_bits a)

theorem bits_add_le (a b : ℕ) : RAM.bits (a + b) ≤ RAM.bits a + RAM.bits b := by
  apply bits_le_of_lt' _ (by have := one_le_bits a; omega)
  have h1 := lt_two_pow_bits' a
  have h2 := lt_two_pow_bits' b
  have p1 := two_le_two_pow_bits a
  have p2 := two_le_two_pow_bits b
  rw [pow_add]
  nlinarith

theorem bits_mul_le (a b : ℕ) : RAM.bits (a * b) ≤ RAM.bits a + RAM.bits b := by
  apply bits_le_of_lt' _ (by have := one_le_bits a; omega)
  have h1 := lt_two_pow_bits' a
  have h2 := lt_two_pow_bits' b
  rw [pow_add]
  nlinarith

theorem bits_pow_le (q k : ℕ) : RAM.bits (q ^ k) ≤ k * RAM.bits q + 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have : RAM.bits (q ^ k) ≤ k * RAM.bits q := by
      apply bits_le_of_lt' _ (by have := one_le_bits q; nlinarith)
      rw [mul_comm, pow_mul]
      exact Nat.pow_lt_pow_left (lt_two_pow_bits' q) (by omega)
    omega

theorem lt_bits_pow {q : ℕ} (hq : 2 ≤ q) (k : ℕ) : k < RAM.bits (q ^ k) := by
  have h1 := lt_two_pow_bits' (q ^ k)
  have h2 : 2 ^ k ≤ q ^ k := Nat.pow_le_pow_left hq k
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 (lt_of_le_of_lt h2 h1)

theorem ceilLog_le_bits (X : ℕ) : ceilLog 2 X ≤ RAM.bits X := by
  rw [bits_eq]
  show (if X ≤ 2 ^ Nat.log 2 X then Nat.log 2 X else Nat.log 2 X + 1) ≤ _
  split_ifs <;> omega

theorem pow_ceilLog_le {q : ℕ} (hq : 2 ≤ q) {X : ℕ} (hX : 1 ≤ X) : q ^ ceilLog q X ≤ q * X := by
  show q ^ (if X ≤ q ^ Nat.log q X then Nat.log q X else Nat.log q X + 1) ≤ q * X
  have h1 := Nat.pow_log_le_self q (show X ≠ 0 by omega)
  split_ifs
  · nlinarith
  · rw [pow_succ]; nlinarith

theorem sum_range_pow_le (y s : ℕ) (hy : 1 ≤ y) :
    ∑ i ∈ Finset.range (s + 1), y ^ i ≤ (s + 1) * y ^ s := by
  calc ∑ i ∈ Finset.range (s + 1), y ^ i ≤ ∑ _i ∈ Finset.range (s + 1), y ^ s :=
        Finset.sum_le_sum fun i hi => Nat.pow_le_pow_right hy (by simp at hi; omega)
    _ = (s + 1) * y ^ s := by simp

theorem radiusBound_mono (q s : ℕ) {x y : ℕ} (h : x ≤ y) : radiusBound q s x ≤ radiusBound q s y := by
  unfold radiusBound
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (by omega)) s)

theorem one_le_radiusBound {q : ℕ} (hq : 1 ≤ q) (s x : ℕ) : 1 ≤ radiusBound q s x := by
  unfold radiusBound
  have : 1 ≤ (2 * q * (x + s + 1)) ^ s := Nat.one_le_pow _ _ (by positivity)
  nlinarith

/-! ## The `Big` predicate -/

namespace Big

theorem of_le {f g : ℕ → ℕ} {a d : ℕ} (N : ℕ) (h : ∀ n, N ≤ n → f n ≤ g n) (hg : Big g a d) :
    Big f a d := by
  obtain ⟨C, M, hC⟩ := hg
  exact ⟨C, max N M, fun n hn => (h n (le_of_max_le_left hn)).trans (hC n (le_of_max_le_right hn))⟩

theorem mono {f : ℕ → ℕ} {a d a' d' : ℕ} (hf : Big f a d) (ha : a ≤ a') (hd : d ≤ d') :
    Big f a' d' := by
  obtain ⟨C, N, hC⟩ := hf
  refine ⟨C, max N 1, fun n hn => (hC n (le_of_max_le_left hn)).trans ?_⟩
  have h1 : 1 ≤ n := le_of_max_le_right hn
  have e1 : n ^ a ≤ n ^ a' := Nat.pow_le_pow_right h1 ha
  have e2 : RAM.bits n ^ d ≤ RAM.bits n ^ d' := Nat.pow_le_pow_right (one_le_bits n) hd
  exact Nat.mul_le_mul (Nat.mul_le_mul_left C e1) e2

/-- Weakening of the exponents (side conditions by `omega` by default). -/
theorem up {f : ℕ → ℕ} {a d A D : ℕ} (hf : Big f a d) (h1 : a ≤ A := by omega)
    (h2 : d ≤ D := by omega) : Big f A D :=
  hf.mono h1 h2

theorem add {f g : ℕ → ℕ} {a d : ℕ} (hf : Big f a d) (hg : Big g a d) :
    Big (fun n => f n + g n) a d := by
  obtain ⟨C, N, hC⟩ := hf
  obtain ⟨D, M, hD⟩ := hg
  refine ⟨C + D, max N M, fun n hn => ?_⟩
  have := hC n (le_of_max_le_left hn)
  have := hD n (le_of_max_le_right hn)
  calc f n + g n ≤ C * n ^ a * RAM.bits n ^ d + D * n ^ a * RAM.bits n ^ d := by omega
    _ = (C + D) * n ^ a * RAM.bits n ^ d := by ring

theorem add' {f g : ℕ → ℕ} {a d a' d' A D : ℕ} (hf : Big f a d) (hg : Big g a' d')
    (h1 : a ≤ A) (h2 : a' ≤ A) (h3 : d ≤ D) (h4 : d' ≤ D) : Big (fun n => f n + g n) A D :=
  add (hf.mono h1 h3) (hg.mono h2 h4)

theorem mul {f g : ℕ → ℕ} {a d a' d' : ℕ} (hf : Big f a d) (hg : Big g a' d') :
    Big (fun n => f n * g n) (a + a') (d + d') := by
  obtain ⟨C, N, hC⟩ := hf
  obtain ⟨D, M, hD⟩ := hg
  refine ⟨C * D, max N M, fun n hn => ?_⟩
  calc f n * g n ≤ (C * n ^ a * RAM.bits n ^ d) * (D * n ^ a' * RAM.bits n ^ d') :=
        Nat.mul_le_mul (hC n (le_of_max_le_left hn)) (hD n (le_of_max_le_right hn))
    _ = C * D * n ^ (a + a') * RAM.bits n ^ (d + d') := by ring

theorem const (c : ℕ) : Big (fun _ => c) 0 0 := ⟨c, 0, fun n _ => by simp⟩

theorem const' (c a d : ℕ) : Big (fun _ => c) a d := (const c).mono (Nat.zero_le _) (Nat.zero_le _)

theorem cmul {f : ℕ → ℕ} {a d : ℕ} (c : ℕ) (hf : Big f a d) : Big (fun n => c * f n) a d :=
  (mul (const c) hf).mono (by omega) (by omega)

theorem mulc {f : ℕ → ℕ} {a d : ℕ} (hf : Big f a d) (c : ℕ) : Big (fun n => f n * c) a d :=
  (mul hf (const c)).mono (by omega) (by omega)

theorem addc {f : ℕ → ℕ} {a d : ℕ} (hf : Big f a d) (c : ℕ) : Big (fun n => f n + c) a d :=
  add hf (const' c a d)

theorem nat : Big (fun n => n) 1 0 := ⟨1, 0, fun n _ => by simp⟩

theorem bits : Big (fun n => RAM.bits n) 0 1 := ⟨1, 0, fun n _ => by simp⟩

theorem pow {f : ℕ → ℕ} {a d : ℕ} (hf : Big f a d) (k : ℕ) :
    Big (fun n => f n ^ k) (a * k) (d * k) := by
  obtain ⟨C, N, hC⟩ := hf
  refine ⟨C ^ k, N, fun n hn => ?_⟩
  calc f n ^ k ≤ (C * n ^ a * RAM.bits n ^ d) ^ k := Nat.pow_le_pow_left (hC n hn) k
    _ = C ^ k * n ^ (a * k) * RAM.bits n ^ (d * k) := by
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]

/-- The bit length of a polynomially bounded quantity is `O(log n)`. -/
theorem bitsOf {f : ℕ → ℕ} {a d : ℕ} (hf : Big f a d) : Big (fun n => RAM.bits (f n)) 0 1 := by
  obtain ⟨C, N, hC⟩ := hf
  refine ⟨RAM.bits C + a + d + 1, max N 1, fun n hn => ?_⟩
  have h1 : 1 ≤ n := le_of_max_le_right hn
  have hb : RAM.bits n ≤ n := bits_le_self h1
  have e1 : f n ≤ C * n ^ (a + d) := by
    calc f n ≤ C * n ^ a * RAM.bits n ^ d := hC n (le_of_max_le_left hn)
      _ ≤ C * n ^ a * n ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb d)
      _ = C * n ^ (a + d) := by ring
  have e2 := bits_mono e1
  have e3 := bits_mul_le C (n ^ (a + d))
  have e4 := bits_pow_le n (a + d)
  have hbn := one_le_bits n
  have e6 : RAM.bits C ≤ RAM.bits C * RAM.bits n := Nat.le_mul_of_pos_right _ hbn
  simp only [pow_zero, pow_one, mul_one]
  nlinarith

/-- The bit length of `q ^ e n` has the size of `e n`. -/
theorem bitsPow (q : ℕ) {e : ℕ → ℕ} {a d : ℕ} (he : Big e a d) :
    Big (fun n => RAM.bits (q ^ e n)) a d := by
  obtain ⟨C, N, hC⟩ := he
  refine ⟨C * RAM.bits q + 1, max N 1, fun n hn => ?_⟩
  have h1 : 1 ≤ n := le_of_max_le_right hn
  have hX : 1 ≤ n ^ a * RAM.bits n ^ d :=
    Nat.mul_le_mul (Nat.one_le_pow _ _ h1) (Nat.one_le_pow _ _ (one_le_bits n))
  have e1 := bits_pow_le q (e n)
  have e2 : e n ≤ C * (n ^ a * RAM.bits n ^ d) := by rw [← mul_assoc]; exact hC n (le_of_max_le_left hn)
  rw [mul_assoc]
  generalize n ^ a * RAM.bits n ^ d = X at hX e2 ⊢
  have e3 : e n * RAM.bits q ≤ C * X * RAM.bits q := Nat.mul_le_mul_right _ e2
  have e4 : (C * RAM.bits q + 1) * X = C * X * RAM.bits q + X := by ring
  show RAM.bits (q ^ e n) ≤ _
  omega

theorem bitsAdd {f g : ℕ → ℕ} {a d a' d' A D : ℕ} (hf : Big (fun n => RAM.bits (f n)) a d)
    (hg : Big (fun n => RAM.bits (g n)) a' d') (h1 : a ≤ A) (h2 : a' ≤ A) (h3 : d ≤ D) (h4 : d' ≤ D) :
    Big (fun n => RAM.bits (f n + g n)) A D :=
  of_le 0 (fun n _ => bits_add_le (f n) (g n)) (add' hf hg h1 h2 h3 h4)

theorem bitsMul {f g : ℕ → ℕ} {a d a' d' A D : ℕ} (hf : Big (fun n => RAM.bits (f n)) a d)
    (hg : Big (fun n => RAM.bits (g n)) a' d') (h1 : a ≤ A) (h2 : a' ≤ A) (h3 : d ≤ D) (h4 : d' ≤ D) :
    Big (fun n => RAM.bits (f n * g n)) A D :=
  of_le 0 (fun n _ => bits_mul_le (f n) (g n)) (add' hf hg h1 h2 h3 h4)

/-- Peel a polynomially bounded summand off the right of a bit length. -/
theorem bitsAddP {f g : ℕ → ℕ} {a' d' A D : ℕ} (hf : Big (fun n => RAM.bits (f n)) A D)
    (hg : Big g a' d') (h4 : 1 ≤ D := by omega) :
    Big (fun n => RAM.bits (f n + g n)) A D :=
  bitsAdd hf hg.bitsOf le_rfl (Nat.zero_le _) le_rfl h4

/-- A polynomially bounded summand on the left of a bit length. -/
theorem bitsAddL {f g : ℕ → ℕ} {a d A D : ℕ} (hf : Big f a d)
    (hg : Big (fun n => RAM.bits (g n)) A D) (h4 : 1 ≤ D := by omega) :
    Big (fun n => RAM.bits (f n + g n)) A D :=
  bitsAdd hf.bitsOf hg (Nat.zero_le _) le_rfl h4 le_rfl

theorem bitsCmul {f : ℕ → ℕ} {a d : ℕ} (c : ℕ) (hf : Big (fun n => RAM.bits (f n)) a d) :
    Big (fun n => RAM.bits (c * f n)) a d :=
  bitsMul (const (RAM.bits c)) hf (Nat.zero_le _) le_rfl (Nat.zero_le _) le_rfl

theorem kap {g : ℕ → ℕ} {a d : ℕ} (B : ℕ) (hg : Big g a d) :
    Big (fun n => kappa B (g n)) (2 * a) (2 * d) := by
  have h2 := (hg.addc 2).pow 2
  have h3 : Big (fun n => 1000 * (g n + 2) ^ 2) (2 * a) (2 * d) :=
    ((h2.cmul 1000)).mono (by omega) (by omega)
  exact add (const' (1000 * (B + 1)) (2 * a) (2 * d)) h3

/-- A sum `∑_{i ≤ s} (2 q (e n + c + 1))^i`. -/
theorem geom (q c s : ℕ) (hq : 1 ≤ q) {e : ℕ → ℕ} {a d : ℕ} (he : Big e a d) :
    Big (fun n => ∑ i ∈ Finset.range (s + 1), (2 * q * (e n + c + 1)) ^ i) (a * s) (d * s) := by
  have h1 : Big (fun n => 2 * q * (e n + c + 1)) a d := ((he.addc c).addc 1).cmul (2 * q)
  have h2 : Big (fun n => (s + 1) * (2 * q * (e n + c + 1)) ^ s) (a * s) (d * s) :=
    (h1.pow s).cmul (s + 1)
  exact of_le 0 (fun n _ => sum_range_pow_le _ s (Nat.mul_pos (by omega) (by omega))) h2

theorem radius (q s : ℕ) {e : ℕ → ℕ} {a d : ℕ} (he : Big e a d) :
    Big (fun n => radiusBound q s (e n)) (a * s) (d * s) := by
  have h1 : Big (fun n => 2 * q * (e n + s + 1)) a d := ((he.addc s).addc 1).cmul (2 * q)
  exact (h1.pow s).cmul (s + 1)

end Big

/-! ## The parameters -/

section Params

variable (q t : ℕ)

theorem big_r : Big (fun n => (parameters q t n).r) (2 * t) 0 :=
  (Big.radius q (2 * t) Big.nat).mono (by omega) (by omega)

theorem big_K : Big (fun n => (parameters q t n).K) 1 0 :=
  (Big.mul Big.nat (Big.const (ceilLog 2 q))).mono (by omega) (by omega)

theorem big_rK1 : Big (fun n => (parameters q t n).r * (parameters q t n).K + 1) (2 * t + 1) 0 :=
  (Big.mul (big_r q t) (big_K q t)).addc 1

theorem big_b : Big (fun n => ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1)) 0 1 :=
  Big.of_le 0 (fun _ _ => ceilLog_le_bits _) (big_rK1 q t).bitsOf

theorem big_Q : Big (fun n => (parameters q t n).Q) (2 * t + 1) 0 :=
  Big.of_le 0 (fun n _ => params_Q_le q t n) ((big_rK1 q t).cmul 2)

theorem params_L_eq (n : ℕ) : (parameters q t n).L =
    4 * ((parameters q t n).r + 1) * (2 * ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1) :=
  rfl

theorem big_L : Big (fun n => (parameters q t n).L) (2 * t) 1 := by
  have h1 : Big (fun n => 4 * ((parameters q t n).r + 1)) (2 * t) 0 := ((big_r q t).addc 1).cmul 4
  have h2 : Big (fun n => 2 * ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1) 0 1 :=
    ((big_b q t).cmul 2).addc 1
  exact Big.of_le 0 (fun n _ => (params_L_eq q t n).le) ((Big.mul h1 h2).mono (by omega) (by omega))

theorem one_le_L (n : ℕ) : 1 ≤ (parameters q t n).L := by
  rw [params_L_eq]; exact Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)

/-- Polynomially bounded `L` gives a polynomially bounded `primeBound L`. -/
theorem big_primeBound {f : ℕ → ℕ} {a d : ℕ} (hf : Big f a d) :
    Big (fun n => primeBound (f n)) a (d + 1) := by
  have h1 : Big (fun n => RAM.bits (f n + 2)) 0 1 := (hf.addc 2).bitsOf
  have h2 : Big (fun n => (f n + 2) * (2 * (RAM.bits (f n + 2) + 3)) + 1) a (d + 1) :=
    ((Big.mul (hf.addc 2) ((h1.addc 3).cmul 2)).mono (by omega) (by omega)).addc 1
  refine Big.of_le 0 (fun n _ => ?_) h2
  unfold primeBound
  have := bits_eq (f n + 2)
  have : 2 * (Nat.log 2 (f n + 2) + 3) ≤ 2 * (RAM.bits (f n + 2) + 3) := by omega
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ this) 1

theorem big_PB : Big (fun n => primeBound (parameters q t n).L) (2 * t) 2 :=
  big_primeBound (big_L q t)

theorem qh_le (hq : 2 ≤ q) (n : ℕ) : q ^ (parameters q t n).h ≤
    (q * (parameters q t n).L) * (q * primeBound (parameters q t n).L) := by
  have hh : q ^ (parameters q t n).h = q ^ (parameters q t n).h₁ * q ^ (parameters q t n).h₂ := by
    rw [← pow_add]; rfl
  rw [hh]
  have hL := one_le_L q t n
  have hp : primeAt ((parameters q t n).L - 1) < primeBound (parameters q t n).L :=
    primeAt_lt_primeBound (by omega)
  have hp1 : 1 ≤ primeAt ((parameters q t n).L - 1) := (Nat.prime_nth_prime _).one_lt.le
  apply Nat.mul_le_mul
  · exact pow_ceilLog_le hq hL
  · calc q ^ (parameters q t n).h₂ ≤ q * primeAt ((parameters q t n).L - 1) := pow_ceilLog_le hq hp1
      _ ≤ q * primeBound (parameters q t n).L := Nat.mul_le_mul_left _ hp.le

theorem big_qh (hq : 2 ≤ q) : Big (fun n => q ^ (parameters q t n).h) (4 * t) 3 :=
  Big.of_le 0 (fun n _ => qh_le q t hq n)
    ((Big.mul ((big_L q t).cmul q) ((big_PB q t).cmul q)).mono (by omega) (by omega))

theorem big_h (hq : 2 ≤ q) : Big (fun n => (parameters q t n).h) 0 1 :=
  Big.of_le 0 (fun _ _ => (lt_bits_pow hq _).le) (big_qh q t hq).bitsOf

theorem big_m : Big (fun n => (parameters q t n).m) 1 0 :=
  Big.of_le 0 (fun n _ => params_m_le q t n) Big.nat

theorem params_k_le' (hq : 2 ≤ q) (n : ℕ) :
    (parameters q t n).k ≤ n + RAM.bits (parameters q t n).L := by
  have h1 : floorLog q (parameters q t n).J = Nat.log q ((parameters q t n).L / 2) :=
    Nat.log_pow (by omega) _
  have h2 : Nat.log q ((parameters q t n).L / 2) ≤ Nat.log 2 ((parameters q t n).L / 2) :=
    Nat.log_anti_left (by norm_num) hq
  have h3 : Nat.log 2 ((parameters q t n).L / 2) ≤ Nat.log 2 (parameters q t n).L :=
    Nat.log_mono_right (Nat.div_le_self _ _)
  have h4 := bits_eq (parameters q t n).L
  have h5 := params_m_le q t n
  show (parameters q t n).m + floorLog q (parameters q t n).J ≤ _
  omega

theorem big_k (hq : 2 ≤ q) : Big (fun n => (parameters q t n).k) 1 1 :=
  Big.of_le 0 (fun n _ => params_k_le' q t hq n)
    (Big.add' Big.nat (big_L q t).bitsOf (by omega) (by omega) (by omega) (by omega))

/-- The minimality of `ρ = shortLength q t h`. -/
theorem qρ_le (hq : 2 ≤ q) (n : ℕ) : q ^ (parameters q t n).ρ ≤
    q * q ^ (parameters q t n).h * radiusBound q (2 * t) (parameters q t n).ρ := by
  have hρ : (parameters q t n).ρ = shortLength q t (parameters q t n).h := rfl
  generalize (parameters q t n).h = h at hρ ⊢
  generalize (parameters q t n).ρ = ρ at hρ ⊢
  have hR := one_le_radiusBound (show 1 ≤ q by omega) (2 * t) ρ
  have hqh : 1 ≤ q ^ h := Nat.one_le_pow _ _ (by omega)
  rcases Nat.eq_zero_or_pos ρ with h0 | hpos
  · subst h0
    simp only [pow_zero]
    exact Nat.mul_pos (Nat.mul_pos (by omega) hqh) hR
  · have hnot : ¬ (h ≤ ρ - 1 ∧ q ^ h * radiusBound q (2 * t) (ρ - 1) ≤ q ^ (ρ - 1)) := by
      intro hc
      have := Nat.sInf_le (s := {l : ℕ | h ≤ l ∧ q ^ h * radiusBound q (2 * t) l ≤ q ^ l}) hc
      have e : shortLength q t h ≤ ρ - 1 := this
      rw [← hρ] at e
      omega
    have hm : radiusBound q (2 * t) (ρ - 1) ≤ radiusBound q (2 * t) ρ :=
      radiusBound_mono q (2 * t) (by omega)
    have e : q ^ ρ = q * q ^ (ρ - 1) := by rw [← pow_succ']; congr 1; omega
    by_cases hc : h ≤ ρ - 1
    · have h1 : q ^ (ρ - 1) < q ^ h * radiusBound q (2 * t) (ρ - 1) := by
        by_contra hh; exact hnot ⟨hc, by omega⟩
      have h2 : q * q ^ (ρ - 1) ≤ q * (q ^ h * radiusBound q (2 * t) (ρ - 1)) :=
        Nat.mul_le_mul_left _ h1.le
      have h3 : q * (q ^ h * radiusBound q (2 * t) (ρ - 1)) ≤ q * (q ^ h * radiusBound q (2 * t) ρ) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hm)
      rw [e]
      calc q * q ^ (ρ - 1) ≤ q * (q ^ h * radiusBound q (2 * t) ρ) := h2.trans h3
        _ = q * q ^ h * radiusBound q (2 * t) ρ := by ring
    · have h1 : q ^ ρ ≤ q ^ h := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : q ^ h ≤ q * q ^ h := Nat.le_mul_of_pos_left _ (by omega)
      have h3 : q * q ^ h ≤ q * q ^ h * radiusBound q (2 * t) ρ := Nat.le_mul_of_pos_right _ (by omega)
      omega

variable (N0 : ℕ) (hρn : ∀ n, N0 ≤ n → (parameters q t n).ρ ≤ n)
include hρn

theorem big_ρ (hq : 2 ≤ q) : Big (fun n => (parameters q t n).ρ) 0 1 := by
  have hc : Big (fun n => q * q ^ (parameters q t n).h * radiusBound q (2 * t) n) (6 * t) 3 :=
    (Big.mul ((big_qh q t hq).cmul q) (Big.radius q (2 * t) Big.nat)).mono (by omega) (by omega)
  have hqρ : Big (fun n => q ^ (parameters q t n).ρ) (6 * t) 3 :=
    Big.of_le N0 (fun n hn => (qρ_le q t hq n).trans
      (Nat.mul_le_mul_left _ (radiusBound_mono q (2 * t) (hρn n hn)))) hc
  exact Big.of_le 0 (fun n _ => (lt_bits_pow hq _).le) hqρ.bitsOf

theorem big_qρ (hq : 2 ≤ q) : Big (fun n => q ^ (parameters q t n).ρ) (4 * t) (3 + 2 * t) :=
  Big.of_le 0 (fun n _ => qρ_le q t hq n)
    ((Big.mul ((big_qh q t hq).cmul q) (Big.radius q (2 * t) (big_ρ q t N0 hρn hq))).mono
      (by omega) (by omega))

end Params

end EditMulticoloring.Dev.Ram.Top
end

section
-- module Solutions.EditMulticoloring.RamTop2
/-!
# Part A (q379), file 2: size bounds of the cost pieces shared by the encoder and the decoder

`paramsCost`, the `paramsW` data bound, the modulus search, `EncS.shortCost` and the generic
`colorOfCost`, all in the `Big` form of `RamTop1`.
-/

set_option autoImplicit false

namespace EditMulticoloring.Dev.Ram.Top

open EditMulticoloring.Code

section Leaves

variable (q t : ℕ)

theorem big_PW : Big (fun n => 2 ^ (2 * (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1)))
    (4 * t + 2) 0 := by
  have e : ∀ n, 2 ^ (2 * (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1)) =
      4 * (parameters q t n).Q ^ 2 := by
    intro n
    have hQ : (parameters q t n).Q = 2 ^ ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) := rfl
    rw [hQ, ← pow_mul, show 2 * (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1)
      = ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) * 2 + 2 by ring, pow_add]
    ring
  exact Big.of_le 0 (fun n _ => (e n).le) (((big_Q q t).pow 2).cmul 4 |>.up)

theorem big_Q1 : Big (fun n => 2 ^ (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1))
    (2 * t + 1) 0 :=
  Big.of_le 0 (fun _ _ => (pow_succ 2 _).le) ((big_Q q t).mulc 2)

theorem big_h₁ (hq : 2 ≤ q) : Big (fun n => (parameters q t n).h₁) 0 1 :=
  Big.of_le 0 (fun _ _ => Nat.le_add_right _ _) (big_h q t hq)

theorem big_vis_m (hq : 2 ≤ q) : Big (fun n => visBound q t (parameters q t n).m) (2 * t) 0 :=
  (Big.geom q (2 * t) (2 * t) (by omega) (big_m q t)).up

theorem big_paramsCost (hq : 2 ≤ q) (ht : 1 ≤ t) : Big (fun n => paramsCost q t n) (4 * t) 4 := by
  have hPB := big_PB q t
  have hPB2 : Big (fun n => (8 * primeBound (parameters q t n).L + 13) *
      (primeBound (parameters q t n).L + 1)) (4 * t) 4 :=
    (Big.mul ((hPB.cmul 8).addc 13) (hPB.addc 1)).up
  have T1 : Big (fun n => 7 * ((parameters q t n).r * (parameters q t n).K + 1) + 4 * t + 40) (4 * t) 4 :=
    (((big_rK1 q t).cmul 7).addc (4 * t)).addc 40 |>.up
  have T2 : Big (fun n => 11 * (parameters q t n).L + 19) (4 * t) 4 := ((big_L q t).cmul 11).addc 19 |>.up
  have T3 : Big (fun n => (8 * primeBound (parameters q t n).L + 13) * (primeBound (parameters q t n).L + 1) +
      14 * primeBound (parameters q t n).L + 40) (4 * t) 4 :=
    Big.addc (Big.add hPB2 (hPB.cmul 14).up) 40
  have T4 : Big (fun n => (4 * t + 24) * (n + 1) + 2 * (parameters q t n).h + 2 * n + 20) (4 * t) 4 :=
    Big.addc (Big.add (Big.add ((Big.nat.addc 1).cmul (4 * t + 24)).up ((big_h q t hq).cmul 2).up)
      (Big.nat.cmul 2).up) 20
  exact Big.add (Big.add (Big.add T1 T2) T3) T4

theorem big_pA (_hq : 2 ≤ q) (ht : 1 ≤ t) : Big (fun n => pABound q t n) (2 * t + 1) 1 := by
  unfold pABound
  have R := Big.radius q (2 * t) Big.nat
  have A : Big (fun n => 2 * q * (n + 2 * t + 1)) 1 0 := ((Big.nat.addc (2 * t)).addc 1).cmul (2 * q)
  exact Big.addc (Big.add (Big.add (Big.add (Big.add (Big.addc (Big.add (Big.addc (Big.addc
    (Big.add R.up A.up) (2 * q)) (2 * t)) Big.nat.up) (ceilLog 2 q)) (big_K q t).up)
    (((big_rK1 q t).addc 2).cmul 5).up) (big_L q t).up) (big_Q q t).up) 10

theorem log_half_le (L : ℕ) : Nat.log q (L / 2) ≤ L :=
  (Nat.log_le_self q _).trans (Nat.div_le_self _ _)

theorem big_paramsBound_bits (hq : 2 ≤ q) (ht : 1 ≤ t) :
    Big (fun n => RAM.bits (paramsBound q t n 1)) 1 1 := by
  unfold paramsBound pRBound
  have hL := big_L q t
  have hPB := big_PB q t
  have hqh := big_qh q t hq
  have G : Big (fun n => pABound q t n + (((parameters q t n).L + 2) * (q + 1) + (parameters q t n).L) +
      ((primeBound (parameters q t n).L + 2) * (q + 1) + 1 + 3 * primeBound (parameters q t n).L +
        (parameters q t n).h₁ + 10)) (2 * t + 1) 2 :=
    Big.add (Big.add (big_pA q t hq ht).up (Big.add (Big.up (Big.mulc (hL.addc 2) (q + 1))) hL.up))
      (Big.addc (Big.add (Big.add (Big.up (Big.addc (Big.mulc (hPB.addc 2) (q + 1)) 1)) (Big.up (hPB.cmul 3)))
        (big_h₁ q t hq).up) 10)
  have F : Big (fun n => Nat.log q ((parameters q t n).L / 2)) (2 * t) 1 :=
    Big.of_le 0 (fun n _ => log_half_le q _) hL
  have P0 : Big (fun n => RAM.bits (q ^ (n + 1))) 1 0 := Big.bitsPow q (Big.nat.addc 1)
  have HR : Big (fun n => 2 * (q ^ (parameters q t n).h * radiusBound q (2 * t) n)) (6 * t) 3 :=
    ((Big.mul hqh (Big.radius q (2 * t) Big.nat)).cmul 2).up
  exact Big.bitsAddL G (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP
    (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP P0.up HR)
    (((Big.nat.addc (2 * t)).addc 1).cmul (2 * q))) (Big.const (2 * q)))
    (Big.const (2 * t))) (big_h q t hq)) Big.nat) (Big.const 4))
    hqh) F)

/-! ## The modulus search, the short code, the enumerator and `colorOfCost` -/

theorem big_Qb : Big (fun n => 2 ^ ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1))
    (2 * t + 1) 0 := big_Q q t

theorem big_modulus (B : ℕ) : Big (fun n =>
    (2 ^ ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1) ^ 2 *
      (44 * ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 90) *
      kappa B (RAM.bits ((2 ^ ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 4) *
        2 ^ (2 * (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1))))) (4 * t + 2) 3 :=
  Big.up (Big.mul (Big.mul (((big_Qb q t).addc 1).pow 2) (((big_b q t).cmul 44).addc 90))
    (Big.kap B (Big.mul ((big_Qb q t).addc 4) (big_PW q t)).bitsOf))

theorem big_enumE (B : ℕ) (cfg : EnumCfg) (s : ℕ) {Lf : ℕ → ℕ} (hL : Big Lf 1 0) :
    Big (fun n => cfg.enumE B q (Lf n) s) 2 2 := by
  unfold EnumCfg.enumE EnumCfg.enumM
  exact Big.up (Big.mul (Big.cmul (100 * (q + 1)) (((hL.addc s).addc 2).pow 2))
    (Big.kap B (Big.addc (Big.add (Big.const' (2 * cfg.a0) 1 0) (Big.cmul 4 ((hL.addc s).addc q))) 8).bitsOf))

theorem big_colorOf (B : ℕ) (cfg : EnumCfg) (ht : 1 ≤ t) {Lf Kf Qf Wf Vb Ms Mb : ℕ → ℕ}
    (hL : Big Lf 1 0) (hK : Big Kf 1 0) (hQ : Big Qf (2 * t + 1) 0) (hW : Big Wf 0 1)
    (hV : Big Vb (2 * t) 0) (hMs : Big (fun n => RAM.bits (Ms n)) 0 1)
    (hMb : Big (fun n => RAM.bits (Mb n)) 1 1) :
    Big (fun n => colorOfCost B q t (Lf n) (Kf n) (Qf n) (Wf n) (Vb n) (Ms n) (Mb n) cfg) (4 * t + 2) 3 := by
  unfold colorOfCost
  have X1 : Big (fun n => (19 * Lf n + 7 * Kf n + 40) * kappa B (RAM.bits (Mb n))) 3 2 :=
    Big.up (Big.mul (Big.addc (Big.add (hL.cmul 19) (hK.cmul 7)) 40) (Big.kap B hMb))
  have X2 : Big (fun n => (19 * Lf n + 7 * Kf n + 40) * kappa B (RAM.bits (Mb n)) +
      cfg.enumE B q (Lf n) (2 * t)) 3 2 := Big.add X1 (big_enumE q B cfg (2 * t) hL).up
  have T1 := Big.mul (hV.addc 1) X2
  have A1 : Big (fun n => (Qf n + 1) * (Vb n + 1) * (Kf n * (36 * Wf n + 24) + 15)) (4 * t + 2) 1 :=
    Big.up (Big.mul (Big.mul (hQ.addc 1) (hV.addc 1)) (Big.addc (Big.mul hK ((hW.cmul 36).addc 24)) 15))
  have A2 : Big (fun n => (Qf n + 1) * (Vb n + 1) * (Kf n * (36 * Wf n + 24) + 15) + 16 * Wf n +
      3 * Qf n + 18) (4 * t + 2) 1 :=
    Big.addc (Big.add (Big.add A1 (hW.cmul 16).up) (hQ.cmul 3).up) 18
  exact Big.add T1.up (Big.mul A2 (Big.kap B hMs)).up

theorem big_shortCost (B a : ℕ) (hq : 2 ≤ q) (N0 : ℕ) (hρn : ∀ n, N0 ≤ n → (parameters q t n).ρ ≤ n) :
    Big (fun n => EncS.shortCost B q t (parameters q t n).ρ a) (4 * t) (4 * t + 7) := by
  unfold EncS.shortCost EncS.shortM
  have hρ := big_ρ q t N0 hρn hq
  have hqρ := big_qρ q t N0 hρn hq
  have hv : Big (fun n => EncS.visBound q t (parameters q t n).ρ) 0 (2 * t) :=
    (Big.geom q (2 * t) (2 * t) (by omega) hρ).up
  have hM : Big (fun n => 2 * a + 4 * ((parameters q t n).ρ + 2 * t + q) + 4 * q ^ (parameters q t n).ρ + 20)
      (4 * t) (3 + 2 * t) :=
    Big.addc (Big.add (Big.add (Big.const' (2 * a) _ _) (Big.cmul 4 ((hρ.addc (2 * t)).addc q)).up)
      (hqρ.cmul 4)) 20
  exact Big.up (Big.mul (Big.mul (Big.mul (hqρ.addc 1) (Big.add (Big.const' 1 0 (2 * t)) hv))
    (Big.cmul (200 * (q + 1)) (((hρ.addc (2 * t)).addc 2).pow 2))) (Big.kap B hM.bitsOf))

end Leaves

end EditMulticoloring.Dev.Ram.Top
end

section
-- module Solutions.EditMulticoloring.RamTop3
/-!
# Part A (q379), file 3: the encoder's cost is `O(n ^ (6 t + 2) (log n) ^ (4 t + 8))`
-/

set_option autoImplicit false

namespace EditMulticoloring.Dev.Ram.Top

open EditMulticoloring.Code

section Enc

variable (q t : ℕ)

theorem big_encM_bits (hq : 2 ≤ q) (N0 : ℕ) (hρn : ∀ n, N0 ≤ n → (parameters q t n).ρ ≤ n) : Big (fun n => RAM.bits (encM q t n)) 1 1 := by
  unfold encM
  have hρ := big_ρ q t N0 hρn hq
  exact Big.bitsCmul 4 (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP
    (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP
    (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP (Big.bitsPow q (big_k q t hq))
      (big_qh q t hq)) (big_qρ q t N0 hρn hq)) ((big_Q q t).pow 2)) (big_PW q t)) (big_PB q t))
      (big_vis_m q t hq)) (big_h q t hq)) (big_k q t hq)) (big_L q t)) (big_K q t)) Big.nat)
      (Big.const q)) (Big.const t)) (Big.const 400))

theorem big_encMb_bits (hq : 2 ≤ q) : Big (fun n => RAM.bits (encMb q t n)) 1 1 := by
  unfold encMb encVb encPW
  exact Big.bitsAddP (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP
    (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP (Big.up (Big.bitsPow q (big_m q t)))
      (Big.const (2 * q))) (Big.const (6 * t))) (Big.const 44)) ((big_m q t).cmul 2)) (big_Q q t))
      (Big.mul ((big_vis_m q t hq).addc 1) (big_K q t))) (big_vis_m q t hq))
      ((big_PW q t).cmul 2)) (Big.const 2)

theorem big_encMs (hq : 2 ≤ q) : Big (fun n => encMs q t n) (6 * t + 3) 0 := by
  unfold encMs encPW encVb
  exact Big.add (Big.add (Big.addc (Big.mul ((big_Q1 q t).addc 6) (big_PW q t)).up 5)
    (Big.up (Big.mul ((big_vis_m q t hq).addc 2) (big_K q t)))) (big_vis_m q t hq).up

theorem big_costC (B : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t) (N0 : ℕ)
    (hρn : ∀ n, N0 ≤ n → (parameters q t n).ρ ≤ n) :
    Big (fun n => costC B q t n) (6 * t + 2) 3 := by
  unfold costC
  have hMb := big_encMb_bits q t hq
  have hC := big_colorOf q t B encCfg2 ht (Lf := fun n => (parameters q t n).m)
    (Kf := fun n => (parameters q t n).K) (Qf := fun n => (parameters q t n).Q)
    (Wf := fun n => ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1)
    (Vb := fun n => encVb q t n) (Ms := fun n => encMs q t n) (Mb := fun n => encMb q t n)
    (big_m q t) (big_K q t) (big_Q q t) ((big_b q t).addc 1) (big_vis_m q t hq)
    (big_encMs q t hq).bitsOf hMb
  have I : Big (fun n => colorOfCost B q t (parameters q t n).m (parameters q t n).K (parameters q t n).Q
      (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1) (encVb q t n) (encMs q t n)
      (encMb q t n) encCfg2 + (19 * (parameters q t n).m + 40) * kappa B (RAM.bits (encMb q t n)) +
      (encCfg1 t).enumE B q (parameters q t n).m (2 * t)) (4 * t + 2) 3 :=
    Big.add (Big.add hC (Big.mul (((big_m q t).cmul 19).addc 40) (Big.kap B hMb)).up)
      (big_enumE q B (encCfg1 t) (2 * t) (big_m q t)).up
  exact Big.add (Big.mul ((big_vis_m q t hq).addc 1) I).up
    (Big.cmul 6 (Big.kap B (big_encM_bits q t hq N0 hρn))).up

theorem big_costA (B : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t) :
    Big (fun n => costA B q t n) (4 * t + 2) 6 := by
  unfold costA modM
  exact Big.add (Big.add (Big.const' _ _ _)
    (Big.mul (big_paramsCost q t hq ht) (Big.kap B (big_paramsBound_bits q t hq ht))).up)
    (big_modulus q t B).up

/-- **The encoder's cost bound.** -/
theorem big_encCost (B : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t) (N0 : ℕ)
    (hρn : ∀ n, N0 ≤ n → (parameters q t n).ρ ≤ n) :
    Big (fun n => encCost q t n B) (6 * t + 2) (4 * t + 8) := by
  unfold encCost
  have κM := Big.kap B (big_encM_bits q t hq N0 hρn)
  have κM8 := Big.kap B (Big.bitsAddP (Big.bitsCmul 8 (big_encM_bits q t hq N0 hρn)) (Big.const 8))
  have hm := big_m q t
  have hk := big_k q t hq
  have hkm : Big (fun n => (parameters q t n).k - (parameters q t n).m) 1 1 :=
    Big.of_le 0 (fun _ _ => Nat.sub_le _ _) hk
  have hL := big_L q t
  have hρ := big_ρ q t N0 hρn hq
  have T2 : Big (fun n => (11 * (parameters q t n).k + 7 * (parameters q t n).m +
      7 * ((parameters q t n).k - (parameters q t n).m) + 40) * kappa B (RAM.bits (encM q t n))) 3 3 :=
    Big.mul (Big.addc (Big.add (Big.add (hk.cmul 11) (hm.cmul 7).up) (hkm.cmul 7)) 40) κM
  have T4 : Big (fun n => (3 * ((parameters q t n).L + 1) + (parameters q t n).L * (10 * encVb q t n + 16) + 3) *
      kappa B (RAM.bits (8 * encM q t n + 8))) (4 * t + 2) 3 :=
    Big.up (Big.mul (Big.addc (Big.add ((hL.addc 1).cmul 3).up
      (Big.mul hL (((big_vis_m q t hq).cmul 10).addc 16))) 3) κM8)
  have T5 : Big (fun n => (2 * (parameters q t n).h + 13) * kappa B (RAM.bits (encM q t n))) 2 3 :=
    Big.up (Big.mul (((big_h q t hq).cmul 2).addc 13) κM)
  have T6 : Big (fun n => 2 * kappa B (RAM.bits (encM q t n)) +
      EncS.shortCost B q t (parameters q t n).ρ (14 + 4 * t)) (4 * t) (4 * t + 7) :=
    Big.add (κM.cmul 2).up (big_shortCost q t B (14 + 4 * t) hq N0 hρn)
  have T7 : Big (fun n => (6 * (parameters q t n).m + 13 * (parameters q t n).ρ + 30) *
      kappa B (RAM.bits (encM q t n))) 3 3 :=
    Big.up (Big.mul (Big.addc (Big.add (a := 1) (d := 1) (hm.cmul 6).up (hρ.cmul 13).up) 30) κM)
  exact Big.add (Big.add (Big.add (Big.add (Big.add (Big.add (big_costA q t B hq ht).up T2.up)
    (big_costC q t B hq ht N0 hρn).up) T4.up) T5.up) T6.up) T7.up

end Enc
end EditMulticoloring.Dev.Ram.Top
end

section
-- module Solutions.EditMulticoloring.RamTop4
/-!
# Part A (q379), file 4: the decoder's cost is `O(n ^ (7 t + 2) (log n) ^ (4 t + 8))`
-/

set_option autoImplicit false

namespace EditMulticoloring.Dev.Ram.Top

open EditMulticoloring.Code

section Dec

variable (q t : ℕ)

theorem big_DM_bits (hq : 2 ≤ q) :
    Big (fun n => RAM.bits (DM q t n)) 1 1 := by
  unfold DM dTW dW dVb
  exact Big.bitsAddP (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP
    (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP
      (Big.up (Big.bitsCmul 4 (Big.bitsPow q Big.nat)))
      ((big_qh q t hq).cmul 2)) (Big.cmul 2 (Big.mul (big_Q q t) (big_Q q t)))) ((big_Q1 q t).cmul 2))
      (big_PB q t)) (big_vis_m q t hq)) (big_L q t)) (Big.nat.cmul 4)) (big_k q t hq))
      (Big.const (2 * q))) (Big.const (100 * t))) (Big.const 1000)

theorem big_dMs (hq : 2 ≤ q) : Big (fun n => dMs q t n) (6 * t + 3) 0 := by
  unfold dMs dTW dW dVb
  exact Big.add (Big.add (Big.addc (Big.add (Big.mul (big_Q1 q t) (big_PW q t)).up
    ((big_PW q t).cmul 6).up) 5)
    (Big.up (Big.mul ((big_vis_m q t hq).addc 2) (big_K q t)))) (big_vis_m q t hq).up

theorem big_dMb_bits (hq : 2 ≤ q) : Big (fun n => RAM.bits (dMb q t n)) 1 1 := by
  unfold dMb dVb dW
  exact Big.bitsAddP (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP
    (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP (Big.bitsAddP
    (Big.bitsAddP (Big.bitsAddP (Big.up (Big.bitsPow q (big_m q t)))
      (Big.const (2 * q))) (Big.const (2 * (12 + 2 * t)))) (Big.const (2 * t))) (Big.const 3))
      (Big.const 4)) (Big.const 5)) (Big.const 6)) ((big_m q t).cmul 2)) (big_Q q t))
      (Big.mul ((big_vis_m q t hq).addc 1) (big_K q t))) (big_vis_m q t hq))
      ((big_PW q t).cmul 2)) (Big.const 2)

theorem big_caCost (B : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t) :
    Big (fun n => caCost q t n B) (6 * t + 2) 3 := by
  unfold caCost
  have hMb := big_dMb_bits q t hq
  have hC := big_colorOf q t B dC2c ht (Lf := fun n => (parameters q t n).m)
    (Kf := fun n => (parameters q t n).K) (Qf := fun n => (parameters q t n).Q)
    (Wf := fun n => dW q t n)
    (Vb := fun n => dVb q t n) (Ms := fun n => dMs q t n) (Mb := fun n => dMb q t n)
    (big_m q t) (big_K q t) (big_Q q t) ((big_b q t).addc 1) (big_vis_m q t hq)
    (big_dMs q t hq).bitsOf hMb
  have I : Big (fun n => colorOfCost B q t (parameters q t n).m (parameters q t n).K (parameters q t n).Q
      (dW q t n) (dVb q t n) (dMs q t n) (dMb q t n) dC2c +
      (19 * (parameters q t n).m + 40) * kappa B (RAM.bits (dMb q t n)) +
      (dC1 t).enumE B q (parameters q t n).m (2 * t)) (4 * t + 2) 3 :=
    Big.add (Big.add hC (Big.mul (((big_m q t).cmul 19).addc 40) (Big.kap B hMb)).up)
      (big_enumE q B (dC1 t) (2 * t) (big_m q t)).up
  exact (Big.mul ((big_vis_m q t hq).addc 1) I).up

theorem big_dBodyCost (B : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t) :
    Big (fun n => dBodyCost q t n B) (6 * t + 2) 3 := by
  unfold dBodyCost
  have κD := Big.kap B (big_DM_bits q t hq)
  have hV : Big (fun n => dVb q t n) (2 * t) 0 := big_vis_m q t hq
  have X : Big (fun n => (11 * dVb q t n + 11) * (parameters q t n).L + 21 * n + 7 * (parameters q t n).k +
      11 * dVb q t n + 110) (4 * t) 1 :=
    Big.addc (Big.add (Big.add (Big.add (Big.up (Big.mul ((hV.cmul 11).addc 11) (big_L q t)))
      (Big.nat.cmul 21).up) ((big_k q t hq).cmul 7).up) (hV.cmul 11).up) 110
  exact Big.add (Big.mul X κD).up (big_caCost q t B hq ht)

theorem big_preCost (B : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t) (N0 : ℕ)
    (hρn : ∀ n, N0 ≤ n → (parameters q t n).ρ ≤ n) :
    Big (fun n => preCost q t n B) (4 * t + 2) (4 * t + 8) := by
  unfold preCost decB
  have κD := Big.kap B (big_DM_bits q t hq)
  have hh₂ : Big (fun n => (parameters q t n).h₂) 0 1 :=
    Big.of_le 0 (fun _ _ => Nat.le_add_left _ _) (big_h q t hq)
  exact Big.add (Big.add (Big.add
    (Big.mul (big_paramsCost q t hq ht) (Big.kap B (big_paramsBound_bits q t hq ht))).up
    (big_modulus q t B).up) (big_shortCost q t B (16 + 5 * t) hq N0 hρn).up)
    (Big.mul (Big.addc (Big.add (Big.add (a := 1) (d := 1) (Big.nat.cmul 11).up (hh₂.cmul 2).up)
      (Big.const' (11 * t) _ _)) 60) κD).up

/-- **The decoder's cost bound.** -/
theorem big_decCost (B : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t) (N0 : ℕ)
    (hρn : ∀ n, N0 ≤ n → (parameters q t n).ρ ≤ n) :
    Big (fun n => decCost q t n B) (7 * t + 2) (4 * t + 8) := by
  unfold decCost
  have κD := Big.kap B (big_DM_bits q t hq)
  have G : Big (fun n => ∑ i ∈ Finset.range (t + 1), (2 * q * (n + 2 * t + 1)) ^ i) t 0 :=
    (Big.geom q (2 * t) t (by omega) Big.nat).up
  have I : Big (fun n => dBodyCost q t n B + (dC0 t).enumE B q (n + t) t) (6 * t + 2) 3 :=
    Big.add (big_dBodyCost q t B hq ht) (big_enumE q B (dC0 t) t (Big.nat.addc t)).up
  exact Big.add (Big.add (big_preCost q t B hq ht N0 hρn).up (Big.mul G I).up)
    (Big.mul (((big_k q t hq).cmul 6).addc 20) κD).up

end Dec

end EditMulticoloring.Dev.Ram.Top
end

section
-- module Solutions.EditMulticoloring.RamTop
/-!
# Part A (q379): the RAM programs for `encode` and `decode` (`EditMulticoloring.Code.ram_programs`)

The encoder and decoder are the compiled `Cmd` programs `encProg q t` and `decProg q t`
(`toProgram_spec`), the modulus is `modSearch b` with `b = ceilLog 2 (r K + 1)`
(`modSearch_valid`); the cost bounds `encCost`, `decCost` are `O(n^(6t+2) (log n)^(4t+8))` and
`O(n^(7t+2) (log n)^(4t+8))` (`big_encCost`, `big_decCost`).
-/

set_option autoImplicit false

namespace EditMulticoloring.Dev.Ram.Top

open EditMulticoloring.Code

theorem bits_le_log (n : ℕ) (hn : 1 ≤ n) : (RAM.bits n : ℝ) ≤ 2 * (1 + Real.log n) := by
  rw [bits_eq]; push_cast
  have h1 : (Nat.log 2 n : ℝ) ≤ Real.logb 2 n := by exact_mod_cast Real.natLog_le_logb n 2
  have h2 : Real.logb 2 n = Real.log n / Real.log 2 := rfl
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have h3 : Real.log n / Real.log 2 ≤ 2 * Real.log n := by
    rw [div_le_iff₀ (Real.log_pos (by norm_num))]
    have := Real.log_two_gt_d9; nlinarith
  linarith

theorem Big.toReal {f : ℕ → ℕ} {a d : ℕ} (hf : Big f a d) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n, N ≤ n → (f n : ℝ) ≤ softBound C a d n := by
  obtain ⟨C, N, hC⟩ := hf
  refine ⟨(C : ℝ) * 2 ^ d + 1, by positivity, max N 1, fun n hn => ?_⟩
  have h1 : 1 ≤ n := le_of_max_le_right hn
  have e := hC n (le_of_max_le_left hn)
  have eR : (f n : ℝ) ≤ C * (n : ℝ) ^ a * (RAM.bits n : ℝ) ^ d := by exact_mod_cast e
  have hb := bits_le_log n h1
  have hb0 : (0 : ℝ) ≤ RAM.bits n := by positivity
  have hp : (RAM.bits n : ℝ) ^ d ≤ (2 * (1 + Real.log n)) ^ d := pow_le_pow_left₀ hb0 hb d
  have hl : 0 ≤ 1 + Real.log n := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast h1); linarith
  have hna : 0 ≤ (n : ℝ) ^ a := by positivity
  have hX := mul_nonneg hna (pow_nonneg hl d)
  have hC0 : (0 : ℝ) ≤ C := by positivity
  unfold softBound
  calc (f n : ℝ) ≤ C * (n : ℝ) ^ a * (RAM.bits n : ℝ) ^ d := eR
    _ ≤ C * (n : ℝ) ^ a * (2 * (1 + Real.log n)) ^ d :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg hC0 hna)
    _ = (C * 2 ^ d) * ((n : ℝ) ^ a * (1 + Real.log n) ^ d) := by rw [mul_pow]; ring
    _ ≤ (C * 2 ^ d + 1) * ((n : ℝ) ^ a * (1 + Real.log n) ^ d) :=
        mul_le_mul_of_nonneg_right (by linarith) hX
    _ = (C * 2 ^ d + 1) * (n : ℝ) ^ a * (1 + Real.log n) ^ d := by ring

theorem one_le_ceilLog {q X : ℕ} (_hq : 2 ≤ q) (hX : 2 ≤ X) : 1 ≤ ceilLog q X := by
  show 1 ≤ (if X ≤ q ^ Nat.log q X then Nat.log q X else Nat.log q X + 1)
  split_ifs with h
  · rcases Nat.eq_zero_or_pos (Nat.log q X) with h0 | h0
    · rw [h0] at h; simp at h; omega
    · exact h0
  · omega

theorem one_le_h (q t n : ℕ) (hq : 2 ≤ q) : 1 ≤ (parameters q t n).h := by
  have hL : 2 ≤ (parameters q t n).L := by
    rw [params_L_eq]
    have : 1 ≤ 2 * ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1 := by omega
    nlinarith
  have : 1 ≤ (parameters q t n).h₁ := one_le_ceilLog hq hL
  show 1 ≤ (parameters q t n).h₁ + (parameters q t n).h₂
  omega

theorem one_le_b (q t n : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) :
    1 ≤ ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) := by
  apply one_le_ceilLog (le_refl 2)
  have hr : 1 ≤ (parameters q t n).r := one_le_radiusBound (by omega) _ _
  have hc : 1 ≤ ceilLog 2 q := one_le_ceilLog (le_refl 2) hq
  have hK : 1 ≤ (parameters q t n).K := by
    show 1 ≤ n * ceilLog 2 q
    nlinarith
  nlinarith

end EditMulticoloring.Dev.Ram.Top

namespace EditMulticoloring.Code

open EditMulticoloring.Dev.Ram EditMulticoloring.Dev.Ram.Top

theorem chk_ram_programs (q t : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t) :
    ∃ (encoder decoder : RAM.Program) (modulus : ℕ → ℕ)
      (CE CD : ℝ) (dE dD n₀ : ℕ),
      0 < CE ∧ 0 < CD ∧ 3 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n →
        let P := parameters q t n
        let p := modulus n
        ValidModulus (ceilLog 2 (P.r * P.K + 1)) p ∧
        (∀ u : FixedWord q P.k,
          RAM.Executes encoder n (toWord u)
            (some ((encode t n p (toWord u)).map Fin.val))
            (softBound CE (6 * t + 2) dE n)) ∧
        (∀ y : Word q,
          RAM.Executes decoder n y ((decode t n p y).map (List.map Fin.val))
            (softBound CD (7 * t + 2) dD n)) := by
  obtain ⟨Pe, Be, Ke, hE⟩ := toProgram_spec (encProg q t) encFlag
  obtain ⟨Pd, Bd, Kd, hD⟩ := toProgram_spec (decProg q t) decFlag
  obtain ⟨_, _, n₁, hn₁3, hR⟩ := encoder_redundancy q t hq ht
  obtain ⟨_, _, hS⟩ := short_edit_code q t hq ht
  have hρn : ∀ n, n₁ ≤ n → (parameters q t n).ρ ≤ n := fun n hn => by
    obtain ⟨h1, h2, -⟩ := hR n hn; omega
  have bE : Big (fun n => RAM.bits n + Ke + encCost q t n Be + RAM.bits 1) (6 * t + 2) (4 * t + 8) :=
    Big.add (Big.add (Big.add Big.bits.up (Big.const' _ _ _)) (big_encCost q t Be hq ht n₁ hρn))
      (Big.const' _ _ _)
  have bD : Big (fun n => RAM.bits n + Kd + decCost q t n Bd + 1) (7 * t + 2) (4 * t + 8) :=
    Big.add (Big.add (Big.add Big.bits.up (Big.const' _ _ _)) (big_decCost q t Bd hq ht n₁ hρn))
      (Big.const' _ _ _)
  obtain ⟨CE, hCE, NE, hNE⟩ := bE.toReal
  obtain ⟨CD, hCD, ND, hND⟩ := bD.toReal
  refine ⟨Pe, Pd, fun n => modSearch (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1)),
    CE, CD, 4 * t + 8, 4 * t + 8, max (max n₁ NE) ND, hCE, hCD,
    le_max_of_le_left (le_max_of_le_left hn₁3), ?_⟩
  intro n hn
  have hn1 : n₁ ≤ n := le_of_max_le_left (le_of_max_le_left hn)
  have hnE : NE ≤ n := le_of_max_le_right (le_of_max_le_left hn)
  have hnD : ND ≤ n := le_of_max_le_right hn
  obtain ⟨hm1, hmρ, -⟩ := hR n hn1
  obtain ⟨hne, -⟩ := hS (parameters q t n).h (one_le_h q t n hq)
  have H1 : ∃ l ≤ n, rhoCond q t (parameters q t n).h l :=
    rho_witness hne (show (parameters q t n).ρ ≤ n by omega)
  have hb1 := one_le_b q t n hq (by omega)
  have hV := modSearch_valid _ hb1
  have H2 := And.intro hV.2.1 hV.2.2.1
  refine ⟨hV, ?_, ?_⟩
  · intro u
    obtain ⟨o1, o2, o3⟩ := encProg_spec q t n Be hq u H1 H2
    obtain ⟨fuel, s1, s2, s3⟩ := hE (toWord u) n
    refine ⟨fuel, ⟨?_, ?_⟩, ?_⟩
    · rw [s1, o2]; rfl
    · rw [s2, o1]
    · rw [o2] at s3
      have : RAM.bits n + Ke + encCost q t n Be + RAM.bits 1 ≥
          (RAM.run Pe (toWord u) fuel (RAM.initial n)).cost := by omega
      exact le_trans (by exact_mod_cast this) (hNE n hnE)
  · intro y
    obtain ⟨o1, o2, o3⟩ := decProg_spec Bd q t hq n y H1 H2 ⟨hm1, hmρ⟩
    obtain ⟨fuel, s1, s2, s3⟩ := hD y n
    refine ⟨fuel, ?_, ?_⟩
    · rw [← o1]
      split_ifs with hz
      · rw [s1, hz]; rfl
      · exact ⟨by rw [s1]; simp [hz], s2⟩
    · have hf : RAM.bits (((decProg q t).exec (RAM.inputAt y) (HS.init n)).regs decFlag) ≤ 1 :=
        (bits_mono o3).trans (le_of_eq rfl)
      have : RAM.bits n + Kd + decCost q t n Bd + 1 ≥
          (RAM.run Pd y fuel (RAM.initial n)).cost := by omega
      exact le_trans (by exact_mod_cast this) (hND n hnD)

end EditMulticoloring.Code
end

theorem solution : type_of% @EditMulticoloring.Code.chk_ram_programs := @EditMulticoloring.Code.chk_ram_programs
