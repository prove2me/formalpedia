-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.encE_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:36:58.663811+00:00
-- url     : https://prove2.me/submissions/f469d152-b6e7-4c4b-acab-d7956b7b55ba

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le
import Theorems.Thm_EditMulticoloring_Dev_Ram_powW_spec

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

theorem foldl_value_init {q : ℕ} (w : Word q) (c : ℕ) :
    w.foldl (fun a b => q * a + b.val) c = c * q ^ w.length + value w := by
  induction w generalizing c with
  | nil => simp [value]
  | cons b w ih =>
    simp only [List.foldl_cons, value, List.length_cons]
    rw [ih, ih (q * 0 + b.val)]
    simp only [mul_zero, zero_add, pow_succ]
    ring

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

end EditMulticoloring.Dev.Ram
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

theorem ParamsAt.congr {s s' : HS} {O q t n : ℕ} (h : ParamsAt s O q t n)
    (hr : ∀ r, O ≤ r → r < O + 17 → s'.regs r = s.regs r) : ParamsAt s' O q t n := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := h
  exact ⟨(hr _ (by omega) (by omega)).trans a0, (hr _ (by omega) (by omega)).trans a1,
    (hr _ (by omega) (by omega)).trans a2, (hr _ (by omega) (by omega)).trans a3,
    (hr _ (by omega) (by omega)).trans a4, (hr _ (by omega) (by omega)).trans a5,
    (hr _ (by omega) (by omega)).trans a6, (hr _ (by omega) (by omega)).trans a7,
    (hr _ (by omega) (by omega)).trans a8, (hr _ (by omega) (by omega)).trans a9,
    (hr _ (by omega) (by omega)).trans a10, (hr _ (by omega) (by omega)).trans a11,
    (hr _ (by omega) (by omega)).trans a12, (hr _ (by omega) (by omega)).trans a13,
    (hr _ (by omega) (by omega)).trans a14, (hr _ (by omega) (by omega)).trans a15,
    (hr _ (by omega) (by omega)).trans a16⟩

theorem EBase.congr {q t n p : ℕ} {s s' : HS} (h : EBase q t n p s)
    (hr : ∀ r, (r = 1 ∨ (100 ≤ r ∧ r < 117) ∨ r = 150) → s'.regs r = s.regs r)
    (ha : ∀ i, s'.arr 1 i = s.arr 1 i) : EBase q t n p s' :=
  ⟨h.par.congr (fun r h1 h2 => hr r (Or.inr (Or.inl ⟨h1, h2⟩))), (hr 1 (Or.inl rfl)).trans h.r1,
    (hr 150 (Or.inr (Or.inr rfl))).trans h.rp, fun i hi => (ha i).trans (h.pr i hi)⟩

/-- The common frame: registers below `100` other than `1`, or at least `176`, may change. -/
theorem EBase.congr' {q t n p : ℕ} {s s' : HS} (h : EBase q t n p s)
    (hr : ∀ r, 100 ≤ r → r < 176 → s'.regs r = s.regs r) (h1 : s'.regs 1 = s.regs 1)
    (ha : ∀ i, s'.arr 1 i = s.arr 1 i) : EBase q t n p s' :=
  h.congr (fun r hr' => by
    rcases hr' with rfl | hr' | rfl
    · exact h1
    · exact hr r hr'.1 (by omega)
    · exact hr _ (by omega) (by omega)) ha

/-! ## Phase A -/

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

theorem value_append' {q : ℕ} (a b : Word q) : value (a ++ b) = value a * q ^ b.length + value b := by
  show (a ++ b).foldl (fun a b => q * a + b.val) 0 = _
  rw [List.foldl_append, EncS.foldl_value_init]; rfl

theorem repr_mod {q : ℕ} (hq : 0 < q) (l N : ℕ) : Code.repr q l N = Code.repr q l (N % q ^ l) := by
  rw [EncS.repr_eq_map hq, EncS.repr_eq_map hq]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  apply Fin.ext
  simp only
  have hdvd : q ^ (l - 1 - i) * q ∣ q ^ l :=
    ⟨q ^ (l - (l - 1 - i + 1)), by rw [← pow_succ, ← pow_add]; congr 1; omega⟩
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self (N % q ^ l),
    Nat.mod_mod_of_dvd _ hdvd]

theorem value_repr_mod {q : ℕ} (hq : 0 < q) (l N : ℕ) : value (Code.repr q l N) = N % q ^ l := by
  rw [repr_mod hq, EncS.value_repr hq _ _ (Nat.mod_lt _ (by positivity))]

theorem value_serialize {q : ℕ} (hq : 0 < q) (P : Parameters) (a b : ℕ) :
    value (serialize q P (a, b)) = (a % q ^ P.h₁) * q ^ P.h₂ + b % q ^ P.h₂ := by
  unfold serialize
  rw [value_append', value_repr_mod hq, value_repr_mod hq, EncS.repr_length hq]

section Phases
variable (inp : ℕ → ℕ) (B : ℕ)

theorem encM_eq (q t n : ℕ) : encM q t n = 4 * (q ^ (parameters q t n).k + q ^ (parameters q t n).h +
    q ^ (parameters q t n).ρ + (parameters q t n).Q ^ 2 + encPW q t n + primeBound (parameters q t n).L +
    visBound q t (parameters q t n).m + (parameters q t n).h + (parameters q t n).k + (parameters q t n).L +
    (parameters q t n).K + n + q + t + 400) := rfl

/-! ## Phase E -/

theorem encE_spec_oai (q t n p : ℕ) (hq : 2 ≤ q) (s : HS) (hs : EBase q t n p s)
    (hsel : s.regs 6 ≤ (parameters q t n).L)
    (h3 : s.regs 3 ≤ (parameters q t n).Q ^ 2 + encPW q t n) :
    let s' := (encE q).exec inp s
    EBase q t n p s' ∧
    s'.regs 22 = value (serialize q (parameters q t n) (s.regs 6, s.regs 3 % primeAt (s.regs 6))) ∧
    s'.mem = s.mem ∧ s'.cur = s.cur ∧ s'.out = s.out ∧
    (encE q).cost inp B s ≤ (2 * (parameters q t n).h + 13) * kappa B (RAM.bits (encM q t n)) := by
  intro s'
  set P := parameters q t n with hP
  set M := encM q t n with hMd
  set κ := kappa B (RAM.bits M) with hκ
  have hMe := encM_eq q t n
  rw [← hP, ← hMd] at hMe
  have hK : ∀ v, v ≤ M → kappa B (RAM.bits v) ≤ κ := fun v hv => kappa_bits_le B hv
  obtain ⟨sel, hsel'⟩ : ∃ x, s.regs 6 = x := ⟨_, rfl⟩
  obtain ⟨Cx, hCx⟩ : ∃ x, s.regs 3 = x := ⟨_, rfl⟩
  obtain ⟨pr, hpr⟩ : ∃ x, primeAt sel = x := ⟨_, rfl⟩
  rw [hsel'] at hsel ⊢
  rw [hCx] at h3 ⊢
  have hprb : pr < primeBound P.L := hpr ▸ primeAt_lt_primeBound hsel
  have hh : P.h = P.h₁ + P.h₂ := rfl
  have q1 : q ^ P.h₁ ≤ q ^ P.h := Nat.pow_le_pow_right (by omega) (by omega)
  have q2 : q ^ P.h₂ ≤ q ^ P.h := Nat.pow_le_pow_right (by omega) (by omega)
  have q1p : 0 < q ^ P.h₁ := by positivity
  have q2p : 0 < q ^ P.h₂ := by positivity
  have hqh : q ^ P.h = q ^ P.h₁ * q ^ P.h₂ := by rw [hh, pow_add]
  have hprod : (sel % q ^ P.h₁) * q ^ P.h₂ + q ^ P.h₂ ≤ q ^ P.h := by
    have : sel % q ^ P.h₁ + 1 ≤ q ^ P.h₁ := Nat.mod_lt _ q1p
    rw [hqh]; nlinarith
  have hη : Cx % pr ≤ Cx := Nat.mod_le _ _
  -- prefix
  set s0 := (seqs [ald 12 1 6, ar .mod 18 3 12, lit 19 q]).exec inp s with hs0
  have hpr1 : s.arr 1 sel = pr := hpr ▸ hs.pr sel hsel
  have r0 : ∀ r, r ≠ 12 → r ≠ 18 → r ≠ 19 → s0.regs r = s.regs r := by
    intro r a b c; simp [hs0, Function.update_apply, a, b, c]
  have e18 : s0.regs 18 = Cx % pr := by simp [hs0, hs.r1, hpr1, hsel', hCx]
  have e19 : s0.regs 19 = q := by simp [hs0]
  have m0 : s0.mem = s.mem := by simp [hs0]
  have c0 : (seqs [ald 12 1 6, ar .mod 18 3 12, lit 19 q]).cost inp B s ≤ 3 * κ := by
    simp only [cost_seqs_cons, cost_seqs_nil, cost_ald, cost_ar, cost_lit, exec_seqs_cons, exec_ald,
      exec_ar, HS.setR_regs, HS.setR_arr, hs.r1, hsel', hpr1]
    simp only [Function.update_apply, show (3 : ℕ) ≠ 12 by omega, if_false, if_true, hCx, hsel', hpr1]
    have e1 := hK (1 + sel + pr) (by omega)
    have e2 := hK (Cx + pr) (by omega)
    have e3 := hK q (by omega)
    omega
  have p109 : s0.regs 109 = P.h₁ := by rw [r0 109 (by omega) (by omega) (by omega)]; exact hs.par.hh₁
  have p110 : s0.regs 110 = P.h₂ := by rw [r0 110 (by omega) (by omega) (by omega)]; exact hs.par.hh₂
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := powW_spec inp B 19 109 20 s0 M (by omega) (by omega)
    (by rw [e19]; omega) (by rw [e19, p109]; omega)
  simp only [e19, p109] at w1 w6
  set s1 := (powW 19 109 20).exec inp s0 with hs1
  have f110 : s1.regs 110 = P.h₂ := by rw [w2 110 (by omega), p110]
  have f19 : s1.regs 19 = q := by rw [w2 19 (by omega), e19]
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := powW_spec inp B 19 110 21 s1 M (by omega) (by omega)
    (by rw [f19]; omega) (by rw [f19, f110]; omega)
  simp only [f19, f110] at v1 v6
  set s2 := (powW 19 110 21).exec inp s1 with hs2
  have g6 : s2.regs 6 = sel := by
    rw [v2 6 (by omega), w2 6 (by omega), r0 6 (by omega) (by omega) (by omega), hsel']
  have g20 : s2.regs 20 = q ^ P.h₁ := by rw [v2 20 (by omega), w1]
  have g18 : s2.regs 18 = Cx % pr := by rw [v2 18 (by omega), w2 18 (by omega), e18]
  have hs' : s' = (seqs [ar .mod 22 6 20, ar .mul 22 22 21, ar .mod 23 18 21, ar .add 22 22 23]).exec inp s2 :=
    rfl
  have rs' : ∀ r, r ≠ 22 → r ≠ 23 → s'.regs r = s2.regs r := by
    intro r a b; rw [hs']; simp [Function.update_apply, a, b]
  have ms' : s'.mem = s2.mem := by rw [hs']; simp
  have r2 : ∀ r, r ≠ 12 → r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 → r ≠ 22 → r ≠ 23 → s'.regs r = s.regs r := by
    intro r a b c d e f g
    rw [rs' r f g, v2 r e, w2 r d, r0 r a b c]
  refine ⟨hs.congr' (fun r h1 h2 => r2 r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)) (r2 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
      (fun i => by simp [HS.arr, ms', v3, w3, m0]), ?_, ?_, ?_, ?_, ?_⟩
  · rw [value_serialize (by omega), hs', hpr]
    simp [Function.update_apply, g6, g20, v1, g18]
  · rw [ms', v3, w3, m0]
  · rw [hs']; simp [v4, w4, hs0]
  · rw [hs']; simp [v5, w5, hs0]
  · have hc : (encE q).cost inp B s = (seqs [ald 12 1 6, ar .mod 18 3 12, lit 19 q]).cost inp B s +
        ((powW 19 109 20).cost inp B s0 + ((powW 19 110 21).cost inp B s1 +
        ((seqs [ar .mod 22 6 20, ar .mul 22 22 21, ar .mod 23 18 21, ar .add 22 22 23]).cost inp B s2 + 0))) :=
      rfl
    have c3 : (seqs [ar .mod 22 6 20, ar .mul 22 22 21, ar .mod 23 18 21, ar .add 22 22 23]).cost inp B s2
        ≤ 4 * κ := by
      simp only [cost_seqs_cons, cost_seqs_nil, cost_ar, exec_seqs_cons, exec_ar, HS.setR_regs,
        arith_mod, arith_mul]
      simp only [Function.update_apply, if_true, if_false, show (6 : ℕ) ≠ 22 by omega,
        show (21 : ℕ) ≠ 22 by omega, show (18 : ℕ) ≠ 22 by omega, show (21 : ℕ) ≠ 23 by omega,
        show (22 : ℕ) ≠ 23 by omega, show (23 : ℕ) ≠ 22 by omega, g6, g20, g18, v1]
      have e1 := hK (sel + q ^ P.h₁) (by omega)
      have e2 := hK (sel % q ^ P.h₁ + q ^ P.h₂) (by have := Nat.mod_lt sel q1p; omega)
      have e3 := hK (Cx % pr + q ^ P.h₂) (by omega)
      have e4 := hK (sel % q ^ P.h₁ * q ^ P.h₂ + Cx % pr % q ^ P.h₂) (by
        have := Nat.mod_lt (Cx % pr) q2p; omega)
      omega
    rw [hc]
    rw [← hκ] at w6 v6
    have : (2 * P.h + 13) * κ = 3 * κ + (2 * P.h₁ + 3) * κ + (2 * P.h₂ + 3) * κ + 4 * κ := by
      rw [hh]; ring
    rw [this]
    omega

/-! ## Phase F -/

/-! ## Phase G -/

end Phases

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.encE_spec_oai := @EditMulticoloring.Dev.Ram.encE_spec_oai
