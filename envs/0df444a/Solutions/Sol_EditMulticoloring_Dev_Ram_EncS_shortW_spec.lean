-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.EncS.shortW_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:33.674966+00:00
-- url     : https://prove2.me/submissions/e3ad23b0-1a03-4f92-92f0-a3ea5bc98ba1

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_EncS_mainBody_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le
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

/-- The sum identity used to turn per-iteration list costs into a list length. -/
theorem sum_range_flatMap_length {β : Type*} (G : ℕ → List β) (X D N : ℕ) :
    ∑ k ∈ Finset.range N, ((G k).length * X + D) =
      ((List.range N).flatMap G).length * X + N * D := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.flatMap_append]
    simp only [List.length_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    ring

/-- The for-loop lemma in list-fold form: iteration `k` folds `f` over the list `G k`, and
costs at most `(G k).length * X + D`.  The step may use that the current accumulator is the
fold over the earlier iterations. -/
theorem forLoop_fold {α β : Type*} (i n one : ℕ) (body : Cmd) (s : HS) (hni : n ≠ i)
    (hio : i ≠ one) (G : ℕ → List β) (f : α → β → α) (Q : α → HS → Prop) (X D : ℕ) (acc : α)
    (h0 : Q acc (s.setR i 0))
    (hstep : ∀ k < s.regs n, ∀ a st, Q a st →
      a = ((List.range k).flatMap G).foldl f acc → st.regs i = k →
      (body.exec inp st).regs i = k ∧
      Q ((G k).foldl f a) (((body.exec inp st).setR one 1).setR i (k + 1)) ∧
      body.cost inp B st ≤ (G k).length * X + D) :
    Q (((List.range (s.regs n)).flatMap G).foldl f acc) ((forLoop i n one body).exec inp s) ∧
    (forLoop i n one body).cost inp B s ≤
      ((List.range (s.regs n)).flatMap G).length * X + s.regs n * D +
        3 * (s.regs n + 1) * kappa B (RAM.bits (s.regs n)) := by
  have := forLoop_spec inp B i n one body s hni hio
    (fun k st => Q (((List.range k).flatMap G).foldl f acc) st) (fun k => (G k).length * X + D)
    (by simpa using h0) (by
      intro k hk st hQ hi
      obtain ⟨h1, h2, h3⟩ := hstep k hk _ st hQ rfl hi
      refine ⟨h1, ?_, h3⟩
      simp only [List.range_succ, List.flatMap_append, List.foldl_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      exact h2)
  rw [sum_range_flatMap_length] at this
  exact ⟨this.1, by linarith [this.2]⟩

end Loops

/-! ## Words stored in arrays -/

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

/-! ## Toy client (a): counting -/

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

theorem foldl_value_init {q : ℕ} (w : Word q) (c : ℕ) :
    w.foldl (fun a b => q * a + b.val) c = c * q ^ w.length + value w := by
  induction w generalizing c with
  | nil => simp [value]
  | cons b w ih =>
    simp only [List.foldl_cons, value, List.length_cons]
    rw [ih, ih (q * 0 + b.val)]
    simp only [mul_zero, zero_add, pow_succ]
    ring

theorem value_cons {q : ℕ} (a : Fin q) (w : Word q) :
    value (a :: w) = a.val * q ^ w.length + value w := by
  show (a :: w).foldl _ 0 = _
  rw [List.foldl_cons, foldl_value_init]
  simp

theorem value_lt {q : ℕ} (w : Word q) : value w < q ^ w.length := by
  induction w with
  | nil => simp [value]
  | cons a w ih =>
    rw [value_cons, List.length_cons, pow_succ]
    have ha : a.val + 1 ≤ q := a.isLt
    have : (a.val + 1) * q ^ w.length ≤ q * q ^ w.length := Nat.mul_le_mul_right _ ha
    nlinarith

theorem value_inj {q : ℕ} : ∀ (w w' : Word q), w.length = w'.length → value w = value w' → w = w'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: w, b :: w', hl, hv => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [value_cons, value_cons, hl] at hv
    have h1 := value_lt w
    have h2 := value_lt w'
    rw [hl] at h1
    have hP : 0 < q ^ w'.length := by omega
    have e1 : (a.val * q ^ w'.length + value w) / q ^ w'.length = a.val := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt h1, zero_add]
    have e2 : (b.val * q ^ w'.length + value w') / q ^ w'.length = b.val := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt h2, zero_add]
    have hab : a = b := Fin.ext (by rw [← e1, ← e2, hv])
    subst hab
    have : value w = value w' := by omega
    rw [value_inj w w' hl this]

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

theorem repr_value {q : ℕ} (w : Word q) (l : ℕ) (hl : w.length = l) : Code.repr q l (value w) = w := by
  rcases Nat.eq_zero_or_pos q with h | hq
  · subst h
    cases w with
    | nil => subst hl; rfl
    | cons a _ => exact a.elim0
  · exact value_inj _ _ (by rw [repr_length hq, hl]) (value_repr hq l _ (hl ▸ value_lt w))

/-! ## `words` -/

theorem length_of_mem_words {q : ℕ} : ∀ (l : ℕ) {w : Word q}, w ∈ words q l → w.length = l
  | 0, w, h => by simp [words] at h; subst h; rfl
  | l + 1, w, h => by
    simp only [words, List.mem_flatMap, List.mem_finRange, List.mem_map, true_and] at h
    obtain ⟨a, u, hu, rfl⟩ := h
    simp [length_of_mem_words l hu]

theorem range_mul_flatMap (q m : ℕ) :
    (List.range q).flatMap (fun a => (List.range m).map (fun v => a * m + v)) = List.range (q * m) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.range_succ, List.flatMap_append, ih, show (q + 1) * m = q * m + m by ring,
      List.range_add]
    simp

theorem words_map_value (q : ℕ) : ∀ l : ℕ, (words q l).map value = List.range (q ^ l)
  | 0 => by simp [words, value]
  | l + 1 => by
    simp only [words, List.map_flatMap, List.map_map]
    have e : ∀ a : Fin q, (words q l).map (value ∘ (a :: ·)) =
        (List.range (q ^ l)).map (fun v => a.val * q ^ l + v) := by
      intro a
      rw [← words_map_value q l, List.map_map]
      apply List.map_congr_left
      intro w hw
      simp [value_cons, length_of_mem_words l hw]
    rw [List.flatMap_congr (fun a _ => e a), finRange_flatMap, pow_succ, mul_comm (q ^ l) q,
      ← range_mul_flatMap]
    apply List.flatMap_congr
    intro a ha
    have ha' : a < q := List.mem_range.mp ha
    simp [finFlat, ha']

/-- The words of length `l`, in order, are the representations of `0, …, q^l - 1`. -/
theorem words_eq (q l : ℕ) : words q l = (List.range (q ^ l)).map (Code.repr q l) := by
  rw [← words_map_value q l, List.map_map]
  conv_lhs => rw [← List.map_id (words q l)]
  apply List.map_congr_left
  intro w hw
  simp [repr_value w l (length_of_mem_words l hw)]

/-! ## `greedy` -/

theorem greedy_eq_foldl {q : ℕ} (t : ℕ) (xs : List (Word q)) :
    greedy t xs = xs.foldl (greedyStep t) [] := rfl

/-! ## Writing the digits of a number -/

end EditMulticoloring.Dev.Ram.EncS
end

section
-- module Solutions.EditMulticoloring.RamEncodeS4
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# Short table, part 4: the program `shortW` and its specification (q379, Part S)

`shortW q t r a` (static `q`, `t`; register base `r`, array base `a`), inputs `regs r = ρ`,
`regs (r + 1) = q ^ ρ`:
1. `MARK[u] := 0`, `INV[u] := 0` for `u < q^ρ` (arrays `a + 1`, `a + 2`), `cnt := 0`;
2. for `v = 0 .. q^ρ - 1`: if `MARK[v] = 0` then `T[cnt] := v` (array `a`), `INV[v] := cnt + 1`,
   `cnt += 1`, and mark every length-`ρ` word of `ball (2t) (repr q ρ v)`.

`shortW_spec`: the final state satisfies `SInv` for `greedy t (words q ρ)`, with the cost bound
`shortCost`.  `shortW_table`: the corollaries for `shortTable q t h` (`ρ = shortLength q t h`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram.EncS

open EditMulticoloring.Code

theorem flatMap_singleton_eq_map {β γ : Type*} (f : β → γ) (L : List β) :
    L.flatMap (fun k => [f k]) = L.map f := by
  induction L with
  | nil => rfl
  | cons b L ih => simp [ih]

theorem mainD_le (B q t ρ a : ℕ) :
    11 * kappa B (RAM.bits (shortM q t ρ a)) + mainD B q t ρ a ≤
      (1 + visBound q t ρ) * (200 * (q + 1) * (ρ + 2 * t + 2) ^ 2) *
        kappa B (RAM.bits (shortM q t ρ a)) := by
  unfold mainD
  set κ := kappa B (RAM.bits (shortM q t ρ a)) with hκ
  set S := (q + 1) * (ρ + 2 * t + 2) ^ 2 with hS
  set V := visBound q t ρ
  have hE : (shortCfg 0 a).enumE B q ρ (2 * t) ≤ 100 * S * κ := by
    rw [EnumCfg.enumE_eq]
    have : kappa B (RAM.bits (2 * (shortCfg 0 a).a0 + 4 * (ρ + 2 * t + q) + 8)) ≤ κ :=
      kappa_bits_le B (by simp only [shortCfg, shortM]; omega)
    calc 100 * (q + 1) * (ρ + 2 * t + 2) ^ 2 *
          kappa B (RAM.bits (2 * (shortCfg 0 a).a0 + 4 * (ρ + 2 * t + q) + 8))
        ≤ 100 * (q + 1) * (ρ + 2 * t + 2) ^ 2 * κ := Nat.mul_le_mul_left _ this
      _ = 100 * S * κ := by rw [hS]; ring
  have hS1 : 4 * ρ + 4 ≤ S := by
    have h1 : (ρ + 2) ^ 2 ≤ (ρ + 2 * t + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : (ρ + 2 * t + 2) ^ 2 ≤ S := by rw [hS]; nlinarith
    nlinarith
  have hA : (7 * ρ + 20) * κ ≤ 100 * S * κ := Nat.mul_le_mul_right _ (by omega)
  have hB : 11 * κ + (7 * ρ + 20) * κ ≤ 200 * S * κ := by
    have : 11 * κ + (7 * ρ + 20) * κ = (7 * ρ + 31) * κ := by ring
    rw [this]; exact Nat.mul_le_mul_right _ (by omega)
  have hC : V * ((7 * ρ + 20) * κ + (shortCfg 0 a).enumE B q ρ (2 * t)) ≤ V * (200 * S * κ) :=
    Nat.mul_le_mul_left _ (by
      have : 100 * S * κ + 100 * S * κ = 200 * S * κ := by ring
      omega)
  have : (1 + V) * (200 * (q + 1) * (ρ + 2 * t + 2) ^ 2) * κ = 200 * S * κ + V * (200 * S * κ) := by
    rw [hS]; ring
  rw [this]
  omega

section Prog
variable (inp : ℕ → ℕ) (B : ℕ)

set_option maxHeartbeats 1000000 in
/-- **Specification of `shortW`.**  After the run, with `G = greedy t (words q ρ)`:
`regs (r + 2) = G.length`, `T[i] = value G[i]`, `MARK[u] = 1` iff `repr q ρ u` lies in a ball
of radius `2t` around a chosen word, `INV[u] = idxOf + 1` for chosen words and `0` otherwise
(all `u < q^ρ`); registers outside `[r, r + 49 + 6t)` and arrays outside `[a, a + 5 + 2t)` are
unchanged, as are the cursor and output. -/
theorem shortW_spec_oai {q : ℕ} (hq : 0 < q) (t r a ρ : ℕ) (st : HS)
    (hρ : st.regs r = ρ) (hN : st.regs (r + 1) = q ^ ρ) :
    SInv t r a ρ st (greedy t (words q ρ)) ((shortW q t r a).exec inp st) ∧
    (shortW q t r a).cost inp B st ≤ shortCost B q t ρ a := by
  set M := shortM q t ρ a with hMdef
  set κ := kappa B (RAM.bits M) with hκ
  set N := q ^ ρ with hNdef
  have hqρ : 1 ≤ N := Nat.one_le_pow _ _ hq
  have hKM : ∀ v, v ≤ M → kappa B (RAM.bits v) ≤ κ := fun v hv => kappa_bits_le B hv
  set s0 := (seqs [lit (r + 6) a, lit (r + 7) (a + 1), lit (r + 8) (a + 2), lit (r + 5) 0,
    lit (r + 2) 0]).exec inp st with hs0
  have r0 : ∀ r', r' ≠ r + 2 → r' ≠ r + 5 → r' ≠ r + 6 → r' ≠ r + 7 → r' ≠ r + 8 →
      s0.regs r' = st.regs r' := by
    intro r' h1 h2 h3 h4 h5; simp (disch := omega) [hs0, upd_ne]
  have m0 : s0.mem = st.mem := by simp [hs0]
  have c0 : s0.cur = st.cur := by simp [hs0]
  have o0 : s0.out = st.out := by simp [hs0]
  have w2 : s0.regs (r + 2) = 0 := by simp (disch := omega) [hs0, upd_ne]
  have w5 : s0.regs (r + 5) = 0 := by simp (disch := omega) [hs0, upd_ne]
  have w6 : s0.regs (r + 6) = a := by simp (disch := omega) [hs0, upd_ne]
  have w7 : s0.regs (r + 7) = a + 1 := by simp (disch := omega) [hs0, upd_ne]
  have w8 : s0.regs (r + 8) = a + 2 := by simp (disch := omega) [hs0, upd_ne]
  have w1 : s0.regs (r + 1) = N := by rw [r0 _ (by omega) (by omega) (by omega) (by omega) (by omega), hN]
  have cost0 : (seqs [lit (r + 6) a, lit (r + 7) (a + 1), lit (r + 8) (a + 2), lit (r + 5) 0,
      lit (r + 2) 0]).cost inp B st ≤ 5 * κ := by
    simp only [cost_seqs_cons, cost_seqs_nil, cost_lit, exec_seqs_cons]
    have := hKM a (by rw [hMdef, shortM]; omega)
    have := hKM (a + 1) (by rw [hMdef, shortM]; omega)
    have := hKM (a + 2) (by rw [hMdef, shortM]; omega)
    have := hKM 0 (by omega)
    omega
  -- the clearing loop
  have I := forLoop_spec inp B (r + 3) (r + 1) (r + 4) (initBody r) s0 (by omega) (by omega)
    (fun k s' => (∀ r', r' ≠ r + 3 → r' ≠ r + 4 → s'.regs r' = s0.regs r') ∧
      (∀ u < k, s'.arr (a + 1) u = 0 ∧ s'.arr (a + 2) u = 0) ∧
      (∀ y i, (y ≠ a + 1 ∧ y ≠ a + 2) → s'.arr y i = s0.arr y i) ∧
      s'.cur = s0.cur ∧ s'.out = s0.out)
    (fun _ => 2 * κ)
    ⟨fun r' h _ => by simp [upd_ne h], fun u hu => absurd hu (Nat.not_lt_zero _),
      fun _ _ _ => rfl, rfl, rfl⟩
    (by
      intro k hk s' ⟨h1, h2, h3, h4, h5⟩ hj
      rw [w1] at hk
      have e5 : s'.regs (r + 5) = 0 := by rw [h1 _ (by omega) (by omega), w5]
      have e7 : s'.regs (r + 7) = a + 1 := by rw [h1 _ (by omega) (by omega), w7]
      have e8 : s'.regs (r + 8) = a + 2 := by rw [h1 _ (by omega) (by omega), w8]
      simp only [initBody, exec_seqs_cons, exec_seqs_nil, exec_ast, cost_seqs_cons, cost_seqs_nil,
        cost_ast, HS.store_regs, e5, e7, e8, hj]
      refine ⟨by trivial, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · intro r' a1 a2; simp (disch := omega) only [HS.setR_regs, upd_ne, HS.store_regs]; exact h1 r' a1 a2
      · intro u hu
        simp only [HS.setR_arr, HS.store_arr]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | rfl
        · obtain ⟨x1, x2⟩ := h2 u hu
          constructor <;> split_ifs <;> first | rfl | omega | assumption
        · simp
      · intro y i hy
        simp only [HS.setR_arr, HS.store_arr]
        rw [if_neg (by omega), if_neg (by omega)]; exact h3 y i hy
      · simp [h4]
      · simp [h5]
      · have := hKM (a + 1 + k + 0) (by rw [hMdef, shortM]; omega)
        have := hKM (a + 2 + k + 0) (by rw [hMdef, shortM]; omega)
        omega)
  rw [w1] at I
  obtain ⟨⟨i1, i2, i3, i4, i5⟩, icost⟩ := I
  set s1 := (forLoop (r + 3) (r + 1) (r + 4) (initBody r)).exec inp s0 with hs1
  have hs1N : s1.regs (r + 1) = N := by rw [i1 _ (by omega) (by omega), w1]
  -- the scan
  have F := forLoop_fold inp B (r + 3) (r + 1) (r + 4) (mainBody q t r a) s1 (by omega) (by omega)
    (fun k => [Code.repr q ρ k]) (greedyStep t) (SInv t r a ρ st) 0 (mainD B q t ρ a) []
    (by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp (disch := omega) only [HS.setR_regs, upd_ne]
        rw [i1 _ (by omega) (by omega), r0 _ (by omega) (by omega) (by omega) (by omega) (by omega), hρ]
      · simp (disch := omega) only [HS.setR_regs, upd_ne]; exact hs1N
      · simp (disch := omega) only [HS.setR_regs, upd_ne]; rw [i1 _ (by omega) (by omega), w2]; rfl
      · simp (disch := omega) only [HS.setR_regs, upd_ne]; rw [i1 _ (by omega) (by omega), w6]
      · simp (disch := omega) only [HS.setR_regs, upd_ne]; rw [i1 _ (by omega) (by omega), w7]
      · simp (disch := omega) only [HS.setR_regs, upd_ne]; rw [i1 _ (by omega) (by omega), w8]
      · intro i h; exact absurd h (Nat.not_lt_zero _)
      · intro u hu; simp only [HS.setR_arr]; rw [(i2 u hu).1]; simp
      · intro u hu; simp only [HS.setR_arr]; rw [(i2 u hu).2]; simp
      · intro r' h
        simp (disch := omega) only [HS.setR_regs, upd_ne]
        rw [i1 _ (by omega) (by omega), r0 _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      · intro y i h
        simp only [HS.setR_arr]
        rw [i3 y i (by omega)]; simp [HS.arr, m0]
      · simp [i4, c0]
      · simp [i5, o0])
    (by
      intro k hk chosen s' hS hch hj
      rw [hs1N] at hk
      rw [flatMap_singleton_eq_map] at hch
      obtain ⟨b1, b2, b3⟩ := mainBody_spec inp B hq t r a ρ st k hk chosen hch s' hS hj
      refine ⟨b1, by simpa using b2, ?_⟩
      simpa using b3)
  rw [hs1N, flatMap_singleton_eq_map,
    show (List.range N).map (Code.repr q ρ) = words q ρ from (words_eq q ρ).symm,
    ← greedy_eq_foldl] at F
  obtain ⟨F1, F2⟩ := F
  refine ⟨F1, ?_⟩
  have hc : (shortW q t r a).cost inp B st =
      (seqs [lit (r + 6) a, lit (r + 7) (a + 1), lit (r + 8) (a + 2), lit (r + 5) 0,
        lit (r + 2) 0]).cost inp B st +
      ((forLoop (r + 3) (r + 1) (r + 4) (initBody r)).cost inp B s0 +
        (forLoop (r + 3) (r + 1) (r + 4) (mainBody q t r a)).cost inp B s1) := rfl
  rw [hc]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_zero, zero_add] at icost F2
  have hKN : kappa B (RAM.bits N) ≤ κ := hKM N (by rw [hMdef, shortM]; omega)
  have hD := mainD_le B q t ρ a
  rw [← hMdef, ← hκ] at hD
  have e3 : 3 * (N + 1) * kappa B (RAM.bits N) ≤ 3 * (N + 1) * κ := Nat.mul_le_mul_left _ hKN
  have hfin : 5 * κ + (3 * (N + 1) * κ + N * (2 * κ)) + (N * mainD B q t ρ a + 3 * (N + 1) * κ) ≤
      (N + 1) * (11 * κ + mainD B q t ρ a) := by
    have : (N + 1) * (11 * κ + mainD B q t ρ a) = 11 * κ + mainD B q t ρ a +
        N * (11 * κ) + N * mainD B q t ρ a := by ring
    rw [this]
    have : 3 * (N + 1) * κ = 3 * κ + 3 * (N * κ) := by ring
    rw [this]
    have : N * (2 * κ) = 2 * (N * κ) := by ring
    rw [this]
    have : N * (11 * κ) = 11 * (N * κ) := by ring
    rw [this]
    omega
  have hfin2 : (N + 1) * (11 * κ + mainD B q t ρ a) ≤ shortCost B q t ρ a := by
    unfold shortCost
    rw [← hMdef, ← hκ, ← hNdef]
    calc (N + 1) * (11 * κ + mainD B q t ρ a)
        ≤ (N + 1) * ((1 + visBound q t ρ) * (200 * (q + 1) * (ρ + 2 * t + 2) ^ 2) * κ) :=
          Nat.mul_le_mul_left _ hD
      _ = _ := by ring
  have e3' : 3 * (N + 1) * kappa B (RAM.bits (s0.regs (r + 1))) ≤ 3 * (N + 1) * κ := by
    rw [w1]; exact e3
  omega

end Prog

/-! ## Corollaries for `shortTable` -/

end EditMulticoloring.Dev.Ram.EncS
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.EncS.shortW_spec_oai := @EditMulticoloring.Dev.Ram.EncS.shortW_spec_oai
