-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.encG_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:47.059092+00:00
-- url     : https://prove2.me/submissions/5e85e24b-00e0-4554-ad6c-8a237b133f30

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_EncS_reprW_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_congr
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_lt
import Theorems.Thm_EditMulticoloring_Dev_Ram_exec_cur_of_reads
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le
import Theorems.Thm_EditMulticoloring_Dev_Ram_upd_eq
import Theorems.Thm_EditMulticoloring_Dev_Ram_upd_ne

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

/-! ## `exec` and `cost` of the constructors -/

section ExecCost
variable (inp : ℕ → ℕ) (B : ℕ)

theorem exec_loop (a : ℕ) (c : Cmd) (s : HS) :
    (Cmd.loop a c).exec inp s = (c.exec inp)^[s.regs a] s := rfl

end ExecCost

/-! ## Monotonicity of the charges -/

theorem kappa_mono {B B' W W' : ℕ} (hB : B ≤ B') (hW : W ≤ W') : kappa B W ≤ kappa B' W' := by
  unfold kappa
  have : (W + 2) ^ 2 ≤ (W' + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

theorem kappa_mono_right (B : ℕ) {W W' : ℕ} (hW : W ≤ W') : kappa B W ≤ kappa B W' :=
  kappa_mono le_rfl hW

theorem kappa_zero_le (B M : ℕ) : kappa B 0 ≤ kappa B (RAM.bits M) :=
  kappa_mono_right B (Nat.zero_le _)

/-! ## Syntactic frames -/

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

/-! ## Copying a block of cells -/

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

/-! ## `words` -/

/-! ## `greedy` -/

/-! ## Writing the digits of a number -/

end EditMulticoloring.Dev.Ram.EncS
end

section
-- module Solutions.EditMulticoloring.RamEncode
/-!
# The encoder program (q379, Part E), part 1: the program and its first phases

`encProg q t` (run from `HS.init n`, input `toWord u`):

* A: `paramsW` (registers `100 ..`, prime table in array `1`), `modulusW` (`p` in register `150`);
* B: read the `k` input symbols into array `2` (`readW`), copy `x = u.take m` into the input buffer
  of `colorsAll` (`copyW`), `j := value (u.drop m)` (`valueW`, register `2`);
* C: `colorsAll` (`Cx` in register `3`, `V` in register `4`, neighbour colours in array `6`);
* D: the good-index loop (`sel` in register `6`);
* E: `idx := (sel % q^h₁) * q^h₂ + (Cx % PR[sel]) % q^h₂` (register `22`);
* F: `shortW` (base register `310 + 12 t`, table array `14 + 4 t`);
* G: emit `x`, then the table word `T[idx]` (if `idx` is below the table length), flag `30 := 1`.

The short-table routines come from the namespace copy `RamEncodeS*` of `RamShort*` (the originals
clash with `RamColor` on two names).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## Layout and program -/

/-! ## Invariant kept from phase A on -/

/-! ## Phase A -/

section Phases
variable (inp : ℕ → ℕ) (B : ℕ)

/-! ## Phase B -/

theorem params_m_le_k (q t n : ℕ) : (parameters q t n).m ≤ (parameters q t n).k :=
  Nat.le_add_right _ _

/-! ## Phase C -/

end Phases

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamEncode3
/-!
# The encoder program (q379, Part E), part 3: phases E, F, G

* `value_serialize`: `value (serialize q P (a, b)) = (a % q^h₁) * q^h₂ + b % q^h₂`;
* `encE_spec`: register `22` holds `value (serialize q P (sel, Cx % primeAt sel))`;
* `encF_spec`: the short table (`shortW`);
* `encG_spec`: the output.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## `value` of `serialize` -/

section Phases
variable (inp : ℕ → ℕ) (B : ℕ)

theorem encM_eq (q t n : ℕ) : encM q t n = 4 * (q ^ (parameters q t n).k + q ^ (parameters q t n).h +
    q ^ (parameters q t n).ρ + (parameters q t n).Q ^ 2 + encPW q t n + primeBound (parameters q t n).L +
    visBound q t (parameters q t n).m + (parameters q t n).h + (parameters q t n).k + (parameters q t n).L +
    (parameters q t n).K + n + q + t + 400) := rfl

/-! ## Phase E -/

/-! ## Phase F -/

/-! ## Phase G -/

theorem encWord_spec (q t : ℕ) (hq : 2 ≤ q) (st : HS) (ρ v M : ℕ) (h113 : st.regs 113 = ρ)
    (h114 : st.regs 114 = q ^ ρ) (hv : st.arr (14 + 4 * t) (st.regs 22) = v) (hvρ : v < q ^ ρ)
    (hM : 20 + 4 * t + st.regs 22 + 2 * q ^ ρ + ρ + q + st.out.length ≤ M) :
    let st' := (encWord q t).exec inp st
    st'.out = st.out ++ (Code.repr q ρ v).map (fun a => a.val) ∧
    (∀ r, r < 26 → st'.regs r = st.regs r) ∧
    (encWord q t).cost inp B st ≤ (13 * ρ + 15) * kappa B (RAM.bits M) := by
  intro st'
  have hq0 : 0 < q := by omega
  set κ := kappa B (RAM.bits M) with hκ
  set s0 := (seqs [lit 26 (14 + 4 * t), ald 81 26 22, lit 80 7, cp 82 114, cp 83 113, lit 84 q]).exec inp st
    with hs0
  have r0 : ∀ r, r ≠ 26 → r ≠ 80 → r ≠ 81 → r ≠ 82 → r ≠ 83 → r ≠ 84 → s0.regs r = st.regs r := by
    intro r a b c d e f; simp [hs0, Function.update_apply, a, b, c, d, e, f]
  have e80 : s0.regs 80 = 7 := by simp [hs0]
  have e81 : s0.regs (80 + 1) = v := by simp [hs0, hv]
  have e82 : s0.regs (80 + 2) = q ^ ρ := by simp [hs0, h114]
  have e83 : s0.regs (80 + 3) = ρ := by simp [hs0, h113]
  have e84 : s0.regs (80 + 4) = q := by simp [hs0]
  have m0 : s0.mem = st.mem := by simp [hs0]
  have o0 : s0.out = st.out := by simp [hs0]
  have c0 : (seqs [lit 26 (14 + 4 * t), ald 81 26 22, lit 80 7, cp 82 114, cp 83 113, lit 84 q]).cost inp B st
      ≤ 6 * κ := by
    simp only [cost_seqs_cons, cost_seqs_nil, cost_lit, cost_ald, cost_cp, exec_seqs_cons, exec_lit,
      exec_ald, exec_cp, HS.setR_regs, HS.setR_arr]
    simp only [Function.update_apply, if_true, if_false, show (22 : ℕ) ≠ 26 by omega,
      show (114 : ℕ) ≠ 26 by omega, show (114 : ℕ) ≠ 81 by omega, show (114 : ℕ) ≠ 80 by omega,
      show (113 : ℕ) ≠ 26 by omega, show (113 : ℕ) ≠ 81 by omega, show (113 : ℕ) ≠ 80 by omega,
      show (113 : ℕ) ≠ 82 by omega, h113, h114, hv]
    have := kappa_bits_le B (a := 14 + 4 * t) (M := M) (by omega)
    have := kappa_bits_le B (a := 14 + 4 * t + st.regs 22 + v) (M := M) (by omega)
    have := kappa_bits_le B (a := 7) (M := M) (by omega)
    have := kappa_bits_le B (a := q ^ ρ) (M := M) (by omega)
    have := kappa_bits_le B (a := ρ) (M := M) (by
      have : ρ < q ^ ρ := Nat.lt_pow_self (by omega)
      omega)
    have := kappa_bits_le B (a := q) (M := M) (by omega)
    omega
  obtain ⟨p1, -, p3, p4, p5, p6⟩ := EncS.reprW_spec inp B 80 s0 M (by rw [e84]; omega)
    (by rw [e82, e84, e83]) (by rw [e80, e81, e83, e84]; omega)
  simp only [e80, e81, e83, e84] at p1 p6
  set s1 := (EncS.reprW 80).exec inp s0 with hs1
  have hw1 : WordAt s1 7 0 (Code.repr q ρ v) := by
    intro i hi
    rw [EncS.repr_length hq0] at hi
    rw [zero_add, p1 i hi, EncS.repr_getElem hq0]
  set s2 := (seqs [lit 90 7, lit 91 0, cp 92 113]).exec inp s1 with hs2
  have e113 : s1.regs 113 = ρ := by
    rw [p3 113 (by omega) (by omega) (by omega) (by omega),
      r0 113 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h113]
  have m1 : ∀ i, s1.arr 7 i = s1.arr 7 i := fun _ => rfl
  have r2 : ∀ r, r ≠ 90 → r ≠ 91 → r ≠ 92 → s2.regs r = s1.regs r := by
    intro r a b c; simp [hs2, Function.update_apply, a, b, c]
  have e90 : s2.regs 90 = 7 := by simp [hs2]
  have e91 : s2.regs (90 + 1) = 0 := by simp [hs2]
  have e92 : s2.regs (90 + 2) = ρ := by simp [hs2, e113]
  have ms2 : s2.mem = s1.mem := by simp [hs2]
  have os2 : s2.out = st.out := by simp [hs2, p5, o0]
  have hw2 : WordAt s2 (s2.regs 90) (s2.regs (90 + 1)) (Code.repr q ρ v) := by
    rw [e90, e91]; exact hw1.congr (fun i _ => by simp [HS.arr, ms2])
  have c2 : (seqs [lit 90 7, lit 91 0, cp 92 113]).cost inp B s1 ≤ 3 * κ := by
    simp only [cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp, exec_seqs_cons, exec_lit, HS.setR_regs]
    simp only [Function.update_apply, show (113 : ℕ) ≠ 91 by omega, show (113 : ℕ) ≠ 90 by omega,
      if_false, e113]
    have := kappa_bits_le B (a := 7) (M := M) (by omega)
    have := kappa_bits_le B (a := 0) (M := M) (by omega)
    have := kappa_bits_le B (a := ρ) (M := M) (by
      have : ρ < q ^ ρ := Nat.lt_pow_self (by omega)
      omega)
    omega
  have ew := emitW_word inp 90 s2 (Code.repr q ρ v) hw2 (by rw [e92, EncS.repr_length hq0])
  obtain ⟨-, w2, -, -, w5⟩ := emitW_spec inp B 90 s2 q M
    (fun i hi => (hw2.lt i (by rw [EncS.repr_length hq0]; rw [e92] at hi; exact hi)).le)
    (by rw [e90, e91, e92, os2]; omega)
  simp only [Nat.reduceAdd, e92] at w5 w2
  have hst' : st' = (emitW 90).exec inp s2 := rfl
  refine ⟨by rw [hst', ew, os2], ?_, ?_⟩
  · intro r hr
    rw [hst', w2 r (by omega), r2 r (by omega) (by omega) (by omega),
      p3 r (by omega) (by omega) (by omega) (by omega),
      r0 r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  · have hc : (encWord q t).cost inp B st =
        (seqs [lit 26 (14 + 4 * t), ald 81 26 22, lit 80 7, cp 82 114, cp 83 113, lit 84 q]).cost inp B st +
        ((EncS.reprW 80).cost inp B s0 + ((seqs [lit 90 7, lit 91 0, cp 92 113]).cost inp B s1 +
          ((emitW 90).cost inp B s2 + 0))) := rfl
    rw [hc]
    rw [← hκ] at p6 w5
    have : (13 * ρ + 15) * κ = 6 * κ + (7 * ρ + 3) * κ + 3 * κ + (6 * ρ + 3) * κ := by ring
    rw [this]
    omega

theorem encG_spec_oai (q t n p : ℕ) (hq : 2 ≤ q) (s : HS) (hs : EBase q t n p s) (w : Word q)
    (hw : WordAt s 2 0 w) (hmk : (parameters q t n).m ≤ w.length) (hout : s.out = [])
    (hidx : s.regs 22 < q ^ (parameters q t n).h) (hcnt : s.regs (312 + 12 * t) ≤ q ^ (parameters q t n).ρ)
    (hT : s.regs 22 < min (q ^ (parameters q t n).h) (s.regs (312 + 12 * t)) →
      s.arr (14 + 4 * t) (s.regs 22) < q ^ (parameters q t n).ρ) :
    let s' := (encG q t).exec inp s
    s'.out = (w.take (parameters q t n).m).map (fun a => a.val) ++
      (if s.regs 22 < min (q ^ (parameters q t n).h) (s.regs (312 + 12 * t)) then
        (Code.repr q (parameters q t n).ρ (s.arr (14 + 4 * t) (s.regs 22))).map (fun a => a.val) else []) ∧
    s'.regs 30 = 1 ∧
    (encG q t).cost inp B s ≤ (6 * (parameters q t n).m + 13 * (parameters q t n).ρ + 30) *
      kappa B (RAM.bits (encM q t n)) := by
  intro s'
  set P := parameters q t n with hP
  set M := encM q t n with hMd
  set κ := kappa B (RAM.bits M) with hκ
  have hMe := encM_eq q t n
  rw [← hP, ← hMd] at hMe
  have hK : ∀ v, v ≤ M → kappa B (RAM.bits v) ≤ κ := fun v hv => kappa_bits_le B hv
  have hmk' : P.m ≤ P.k := params_m_le_k q t n
  have hρq : P.ρ < q ^ P.ρ := Nat.lt_pow_self (by omega)
  obtain ⟨idx, hidx'⟩ : ∃ x, s.regs 22 = x := ⟨_, rfl⟩
  obtain ⟨cnt, hcnt'⟩ : ∃ x, s.regs (312 + 12 * t) = x := ⟨_, rfl⟩
  rw [hidx'] at hidx hT ⊢
  rw [hcnt'] at hcnt hT ⊢
  have pm : s.regs 115 = P.m := hs.par.hm
  have pqh : s.regs 112 = q ^ P.h := hs.par.hqh
  -- G0
  set s0 := (seqs [lit 70 2, lit 71 0, cp 72 115]).exec inp s with hs0
  have r0 : ∀ r, r ≠ 70 → r ≠ 71 → r ≠ 72 → s0.regs r = s.regs r := by
    intro r a b c; simp [hs0, Function.update_apply, a, b, c]
  have e70 : s0.regs 70 = 2 := by simp [hs0]
  have e71 : s0.regs (70 + 1) = 0 := by simp [hs0]
  have e72 : s0.regs (70 + 2) = P.m := by simp [hs0, pm]
  have m0 : s0.mem = s.mem := by simp [hs0]
  have o0 : s0.out = [] := by simp [hs0, hout]
  have c0 : (seqs [lit 70 2, lit 71 0, cp 72 115]).cost inp B s ≤ 3 * κ := by
    simp only [cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp, exec_seqs_cons, exec_lit, HS.setR_regs]
    simp only [Function.update_apply, show (115 : ℕ) ≠ 71 by omega, show (115 : ℕ) ≠ 70 by omega,
      if_false, pm]
    have := hK 2 (by omega); have := hK 0 (by omega); have := hK P.m (by omega)
    omega
  have hx0 : WordAt s0 (s0.regs 70) (s0.regs (70 + 1)) (w.take P.m) := by
    rw [e70, e71]
    intro i hi
    simp only [List.length_take] at hi
    have := hw i (by omega)
    simp only [HS.arr, m0] at this ⊢
    rw [this, List.getElem_take]
  have ew := emitW_word inp 70 s0 (w.take P.m) hx0 (by rw [e72, List.length_take]; omega)
  obtain ⟨-, f2, f3, -, f5⟩ := emitW_spec inp B 70 s0 q M
    (fun i hi => (hx0.lt i (by rw [List.length_take]; rw [e72] at hi; omega)).le)
    (by rw [e70, e71, e72, o0]; simp; omega)
  simp only [Nat.reduceAdd, e72] at f5 f2
  rw [o0, List.nil_append] at ew
  set s1 := (emitW 70).exec inp s0 with hs1
  have r1 : ∀ r, r < 70 ∨ 77 ≤ r → s1.regs r = s.regs r := by
    intro r hr; rw [f2 r (by omega), r0 r (by omega) (by omega) (by omega)]
  -- G2
  set s2 := (seqs [ar .lt 24 22 112, ar .lt 25 22 (312 + 12 * t), ar .mul 24 24 25]).exec inp s1 with hs2
  have r2 : ∀ r, r ≠ 24 → r ≠ 25 → s2.regs r = s1.regs r := by
    intro r a b; simp [hs2, Function.update_apply, a, b]
  have i22 : s1.regs 22 = idx := by rw [r1 22 (by omega), hidx']
  have i112 : s1.regs 112 = q ^ P.h := by rw [r1 112 (by omega), pqh]
  have i312 : s1.regs (312 + 12 * t) = cnt := by rw [r1 _ (by omega), hcnt']
  obtain ⟨b1, hb1⟩ : ∃ b, (if idx < q ^ P.h then 1 else 0) = b := ⟨_, rfl⟩
  obtain ⟨b2, hb2⟩ : ∃ b, (if idx < cnt then 1 else 0) = b := ⟨_, rfl⟩
  have b1le : b1 ≤ 1 := by rw [← hb1]; split_ifs <;> omega
  have b2le : b2 ≤ 1 := by rw [← hb2]; split_ifs <;> omega
  have e24 : s2.regs 24 = b1 * b2 := by
    simp [hs2, Function.update_apply, i22, i112, i312, hb1, hb2, show 312 + 12 * t ≠ 24 by omega]
  have c2 : (seqs [ar .lt 24 22 112, ar .lt 25 22 (312 + 12 * t), ar .mul 24 24 25]).cost inp B s1 ≤ 3 * κ := by
    simp [Function.update_apply, i22, i112, i312, hb1, hb2, show 312 + 12 * t ≠ 24 by omega]
    have := hK (idx + q ^ P.h) (by omega)
    have := hK (idx + cnt) (by omega)
    have := hK (b1 + b2) (by omega)
    omega
  have ms2 : s2.mem = s1.mem := by simp [hs2]
  have os2 : s2.out = s1.out := by simp [hs2]
  have hcond : s2.regs 24 = 0 ↔ ¬ idx < min (q ^ P.h) cnt := by
    rw [e24, ← hb1, ← hb2]; constructor
    · intro h hc; rw [lt_min_iff] at hc; rw [if_pos hc.1, if_pos hc.2] at h; omega
    · intro h; rw [lt_min_iff] at h
      by_cases h1 : idx < q ^ P.h
      · rw [if_neg (fun h2 => h ⟨h1, h2⟩)]; simp
      · rw [if_neg h1]; simp
  -- G3 / G4
  set s3 := (Cmd.ifz 24 .skip (encWord q t)).exec inp s2 with hs3
  have hs' : s' = (lit 30 1).exec inp s3 := rfl
  have hc : (encG q t).cost inp B s = (seqs [lit 70 2, lit 71 0, cp 72 115]).cost inp B s +
      ((emitW 70).cost inp B s0 + ((seqs [ar .lt 24 22 112, ar .lt 25 22 (312 + 12 * t),
        ar .mul 24 24 25]).cost inp B s1 + ((Cmd.ifz 24 .skip (encWord q t)).cost inp B s2 +
        ((lit 30 1).cost inp B s3 + 0)))) := rfl
  have c4 : (lit 30 1).cost inp B s3 ≤ κ := hK 1 (by omega)
  have e24b : s2.regs 24 ≤ 1 := by rw [e24]; exact (Nat.mul_le_mul b1le b2le).trans (by norm_num)
  have k24 : kappa B (RAM.bits (s2.regs 24)) ≤ κ := hK _ (by omega)
  rw [← hκ] at f5
  by_cases hc' : idx < min (q ^ P.h) cnt
  · have hnz : s2.regs 24 ≠ 0 := fun h => (hcond.mp h) hc'
    have hs3' : s3 = (encWord q t).exec inp s2 := by rw [hs3]; simp [hnz]
    have v22 : s2.regs 22 = idx := by rw [r2 22 (by omega) (by omega), i22]
    have v113 : s2.regs 113 = P.ρ := by rw [r2 _ (by omega) (by omega), r1 _ (by omega)]; exact hs.par.hρ
    have v114 : s2.regs 114 = q ^ P.ρ := by
      rw [r2 _ (by omega) (by omega), r1 _ (by omega)]; exact hs.par.hqρ
    have va : s2.arr (14 + 4 * t) (s2.regs 22) = s.arr (14 + 4 * t) idx := by
      rw [v22]; simp [HS.arr, ms2, f3, m0]
    have hv := hT hc'
    have o2l : s2.out.length = P.m := by rw [os2, ew]; simp; omega
    obtain ⟨g1, -, g3⟩ := encWord_spec inp B q t hq s2 P.ρ (s.arr (14 + 4 * t) idx) M v113 v114 va hv
      (by rw [v22, o2l]; omega)
    rw [← hκ] at g3
    refine ⟨?_, by rw [hs']; simp, ?_⟩
    · rw [hs']; simp only [exec_lit, HS.setR_out]; rw [hs3', g1, os2, ew, if_pos hc']
    · rw [hc]
      have : Cmd.cost inp B (Cmd.ifz 24 .skip (encWord q t)) s2 = kappa B (RAM.bits (s2.regs 24)) +
          (encWord q t).cost inp B s2 := by simp [hnz]
      rw [this]
      have : (6 * P.m + 13 * P.ρ + 30) * κ = 3 * κ + (6 * P.m + 3) * κ + 3 * κ + κ + (13 * P.ρ + 15) * κ
          + 5 * κ := by ring
      rw [this]
      omega
  · have hz : s2.regs 24 = 0 := hcond.mpr hc'
    have hs3' : s3 = s2 := by rw [hs3]; simp [hz]
    refine ⟨?_, by rw [hs']; simp, ?_⟩
    · rw [hs']; simp only [exec_lit, HS.setR_out]; rw [hs3', os2, ew, if_neg hc', List.append_nil]
    · rw [hc]
      have : Cmd.cost inp B (Cmd.ifz 24 .skip (encWord q t)) s2 = kappa B (RAM.bits (s2.regs 24)) := by
        simp [hz]
      rw [this]
      have : (6 * P.m + 13 * P.ρ + 30) * κ = 3 * κ + (6 * P.m + 3) * κ + 3 * κ + κ + (13 * P.ρ + 20) * κ
          := by ring
      rw [this]
      have : κ ≤ (13 * P.ρ + 20) * κ := Nat.le_mul_of_pos_left κ (by omega)
      omega

end Phases

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.encG_spec_oai := @EditMulticoloring.Dev.Ram.encG_spec_oai
