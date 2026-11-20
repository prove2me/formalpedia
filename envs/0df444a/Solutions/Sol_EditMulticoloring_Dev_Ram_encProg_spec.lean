-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.encProg_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:36:59.810226+00:00
-- url     : https://prove2.me/submissions/ec533ac9-adab-417f-9131-8ef26abd2ecc

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_congr
import Theorems.Thm_EditMulticoloring_Dev_Ram_colorsAll_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_encB_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_encD_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_encE_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_encF_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_encG_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le
import Theorems.Thm_EditMulticoloring_Dev_Ram_localColor_lt
import Theorems.Thm_EditMulticoloring_Dev_Ram_modulusW_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_paramsW_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_visits_le_visBound

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

theorem nbrList_length_le {q : ℕ} (t : ℕ) (x : Word q) :
    (nbrList t x).length ≤ (visits (2 * t) x).length := List.length_filter_le _ _

/-! ## Initialisation: field context, a copy of `x`, the digits of `value x` -/

/-! ## Enumeration: digits of every neighbour -/

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

/-- The `.all` over the confusion neighbourhood, as a test over the indices of `nbrList`. -/
theorem confusionNeighbors_all_range {q : ℕ} (t : ℕ) (x : Word q) (f : Word q → Bool) :
    (confusionNeighbors t x).all f =
      (List.range (nbrList t x).length).all (fun j => f ((nbrList t x).getD j [])) := by
  rw [confusionNeighbors_all, all_range_getD]

/-! ## The program -/

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

section Phases
variable (inp : ℕ → ℕ) (B : ℕ)

theorem encA_spec (q t n : ℕ) (hq : 2 ≤ q)
    (hw : ∃ l ≤ n, rhoCond q t (parameters q t n).h l) :
    let s := (encA q t).exec inp (HS.init n)
    EBase q t n (modSearch (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1))) s ∧
    s.cur = 0 ∧ s.out = [] ∧ (encA q t).cost inp B (HS.init n) ≤ costA B q t n := by
  intro s
  set s0 := (lit 1 1).exec inp (HS.init n) with hs0
  have e0 : s0.regs 0 = n := by simp [hs0, HS.init]
  have e1 : s0.regs 1 = 1 := by simp [hs0]
  obtain ⟨p1, p2, -, p4, p5, p6, p7⟩ := paramsW_spec inp B q t 0 1 100 s0
    (paramsBound q t n 1) hq (by omega) (by omega) (by rw [e0]; exact hw) (by rw [e0, e1])
  rw [e0] at p1 p2 p7
  rw [e1] at p2
  set s1 := (paramsW q t 0 1 100).exec inp s0 with hs1
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := modulusW_spec inp B 102 150 s1
    (modM (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1))) (by omega)
    (by rw [p1.hb]; rfl)
  rw [p1.hb] at m1 m6
  have hs : s = (modulusW 102 150).exec inp s1 := rfl
  rw [← hs] at m1 m2 m3 m4 m5
  refine ⟨⟨p1.congr (fun r h1 h2 => m2 r (by omega)), ?_, m1, ?_⟩, ?_, ?_, ?_⟩
  · rw [m2 _ (by omega), p4 _ (by omega), e1]
  · intro i hi
    simp only [HS.arr, m3]; exact p2 i hi
  · rw [m4, p5]; simp [hs0, HS.init]
  · rw [m5, p6]; simp [hs0, HS.init]
  · have hc : (encA q t).cost inp B (HS.init n) = kappa B (RAM.bits 1) +
        ((paramsW q t 0 1 100).cost inp B s0 + ((modulusW 102 150).cost inp B s1 + 0)) := rfl
    rw [hc]
    unfold costA
    omega

/-! ## Phase B -/

theorem params_m_le_k (q t n : ℕ) : (parameters q t n).m ≤ (parameters q t n).k :=
  Nat.le_add_right _ _

/-! ## Phase C -/

theorem encPW_eq (q t n : ℕ) :
    encPW q t n = 2 ^ (2 * (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1)) := rfl

theorem pow_succ_le_encPW (q t n : ℕ) :
    2 ^ (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1) ≤ encPW q t n := by
  rw [encPW_eq]; exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem encCfg1_lenR (t : ℕ) : (encCfg1 t).lenR (2 * t) = 307 + 12 * t := by
  simp only [encCfg1, EnumCfg.lenR]; omega

theorem encCfg1_buf (t : ℕ) : (encCfg1 t).buf (2 * t) = 13 + 4 * t := by
  simp only [encCfg1, EnumCfg.buf]; omega

set_option maxHeartbeats 1600000 in
theorem encC_spec (q t n p : ℕ) (w : Word q) (s : HS) (hs : EBase q t n p s)
    (hp1 : 2 ^ ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) ≤ p)
    (hp2 : p < 2 ^ (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1))
    (hmk : (parameters q t n).m ≤ w.length)
    (hw : WordAt s 2 0 w) (hx : WordAt s (13 + 4 * t) 0 (w.take (parameters q t n).m))
    (hlen : s.regs (307 + 12 * t) = (parameters q t n).m) :
    let s' := (encC q t).exec inp s
    let x := w.take (parameters q t n).m
    EBase q t n p s' ∧ WordAt s' 2 0 w ∧ s'.regs 2 = s.regs 2 ∧
    s'.regs 3 = localColor t (parameters q t n) p x ∧ s'.regs 4 = (nbrList t x).length ∧
    (∀ l (hl : l < (nbrList t x).length), s'.arr 6 l = localColor t (parameters q t n) p (nbrList t x)[l]) ∧
    s'.cur = s.cur ∧ s'.out = s.out ∧ (encC q t).cost inp B s ≤ costC B q t n := by
  intro s' x
  set P := parameters q t n with hP
  set b := ceilLog 2 (P.r * P.K + 1) with hb
  set M := encM q t n with hMd
  set κ := kappa B (RAM.bits M) with hκ
  have hK : ∀ v, v ≤ M → kappa B (RAM.bits v) ≤ κ := fun v hv => kappa_bits_le B hv
  have hMe : M = 4 * (q ^ P.k + q ^ P.h + q ^ P.ρ + P.Q ^ 2 + encPW q t n + primeBound P.L +
      visBound q t P.m + P.h + P.k + P.L + P.K + n + q + t + 400) := rfl
  have hxl : x.length = P.m := by
    show (w.take P.m).length = P.m
    rw [List.length_take]; omega
  have hpw : 2 ^ (b + 1) ≤ encPW q t n := pow_succ_le_encPW q t n
  have hQ : P.Q = 2 ^ b := rfl
  have hQ2 : 2 ^ b ≤ 2 ^ (b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb2 : b + 1 < 2 ^ (b + 1) := Nat.lt_two_pow_self
  -- C0
  set s0 := (seqs [cp 200 150, cp 203 106, cp 218 101, cp 224 103]).exec inp s with hs0
  have f0 : ∀ r, r ≠ 200 → r ≠ 203 → r ≠ 218 → r ≠ 224 → s0.regs r = s.regs r := by
    intro r h1 h2 h3 h4; simp [hs0, Function.update_apply, h1, h2, h3, h4]
  have m0 : s0.mem = s.mem := by simp [hs0]
  have pW : s.regs 106 = b + 1 := hs.par.hW
  have pK : s.regs 101 = P.K := hs.par.hK
  have pQ : s.regs 103 = P.Q := hs.par.hQ
  have e200 : s0.regs 200 = p := by simp [hs0, hs.rp]
  have e203 : s0.regs 203 = b + 1 := by simp [hs0, pW]
  have e218 : s0.regs 218 = P.K := by simp [hs0, pK]
  have e224 : s0.regs 224 = P.Q := by simp [hs0, pQ]
  have c0 : (seqs [cp 200 150, cp 203 106, cp 218 101, cp 224 103]).cost inp B s ≤ 4 * κ := by
    simp only [cost_seqs_cons, cost_seqs_nil, cost_cp, exec_seqs_cons, exec_cp, HS.setR_regs]
    simp only [Function.update_apply, show (106 : ℕ) ≠ 200 by omega, show (101 : ℕ) ≠ 200 by omega,
      show (101 : ℕ) ≠ 203 by omega, show (103 : ℕ) ≠ 200 by omega, show (103 : ℕ) ≠ 203 by omega,
      show (103 : ℕ) ≠ 218 by omega, if_false, hs.rp, pW, pK, pQ]
    have := hK p (by omega); have := hK (b + 1) (by omega); have := hK P.K (by omega)
    have := hK P.Q (by rw [hQ]; omega)
    omega
  -- colorsAll
  have hpl : CAPlace t (encCfg1 t) encCfg2 200 3 4 5 6 := by
    constructor <;> simp [encCfg1, encCfg2] <;> omega
  have hx0 : WordAt s0 ((encCfg1 t).buf (2 * t)) 0 x := by
    rw [encCfg1_buf]; exact hx.congr (fun i _ => by simp [HS.arr, m0])
  have hl0 : s0.regs ((encCfg1 t).lenR (2 * t)) = x.length := by
    rw [encCfg1_lenR, f0 _ (by omega) (by omega) (by omega) (by omega), hlen, hxl]
  have hVb : visBound q t x.length ≤ encVb q t n := by rw [hxl]; rfl
  have hMs : p * 2 ^ (2 * (b + 1)) + 6 * 2 ^ (2 * (b + 1)) + 5 + (encVb q t n + 2) * P.K +
      encVb q t n ≤ encMs q t n := by
    have : encMs q t n = (2 ^ (b + 1) + 6) * encPW q t n + 5 + (encVb q t n + 2) * P.K + encVb q t n := rfl
    rw [this, ← encPW_eq]
    have : p * encPW q t n ≤ 2 ^ (b + 1) * encPW q t n := Nat.mul_le_mul_right _ hp2.le
    nlinarith
  have hMb : q ^ x.length + 2 * q + 2 * (encCfg1 t).a0 + 2 * t + 3 + 4 + 5 + 6 + 2 * x.length + P.Q +
      (encVb q t n + 1) * P.K + encVb q t n + 2 * 2 ^ (2 * (b + 1)) + 2 ≤ encMb q t n := by
    have : encMb q t n = q ^ P.m + 2 * q + 6 * t + 44 + 2 * P.m + P.Q + (encVb q t n + 1) * P.K +
      encVb q t n + 2 * encPW q t n + 2 := rfl
    rw [this, ← encPW_eq, hxl]
    simp only [encCfg1]
    omega
  obtain ⟨a1, a2, a3, a4, a5, -, -, a8, a9, a10⟩ := colorsAll_spec inp B t (encCfg1 t) encCfg2 200 3 4 5 6 x s0
    p (b + 1) P.Q P.K (encVb q t n) (encMs q t n) (encMb q t n) hpl e200 e203 e218 e224 hl0 hx0
    (by omega) hp2 (by rw [hQ]; positivity) (by rw [hQ]; exact hQ2) hVb hMs hMb
  set s1 := (colorsAll q t (encCfg1 t) encCfg2 200 3 4 5 6).exec inp s0 with hs1
  have hs' : s' = (seqs [cp 3 251, cp 4 252]).exec inp s1 := rfl
  have f' : ∀ r, r ≠ 3 → r ≠ 4 → s'.regs r = s1.regs r := by
    intro r h1 h2; rw [hs']; simp [Function.update_apply, h1, h2]
  have m' : s'.mem = s1.mem := by rw [hs']; simp
  have nR : ∀ r, r < 201 → ¬ (encCfg1 t).ownsReg (2 * t) r := by
    intro r hr h; simp only [EnumCfg.ownsReg, encCfg1] at h; omega
  have nA : ∀ y, y < 3 → ¬ encCfg2.ownsArr (2 * t) y ∧ ¬ (encCfg1 t).ownsArr (2 * t) y := by
    intro y hy; simp only [EnumCfg.ownsArr, encCfg1, encCfg2]; omega
  have fr : ∀ r, r < 200 → s1.regs r = s.regs r := by
    intro r hr
    rw [a4 r (by omega) (nR r (by omega))]
    exact f0 _ (by omega) (by omega) (by omega) (by omega)
  have ar : ∀ y i, y < 3 → s1.arr y i = s.arr y i := by
    intro y i hy
    rw [a5 y i (by omega) (by omega) (by omega) (by omega) (nA y hy).1 (nA y hy).2]
    simp [HS.arr, m0]
  have e3 : s'.regs 3 = s1.regs 251 := by rw [hs']; simp
  have e4 : s'.regs 4 = s1.regs 252 := by rw [hs']; simp
  have hc : (encC q t).cost inp B s = (seqs [cp 200 150, cp 203 106, cp 218 101, cp 224 103]).cost inp B s +
      ((colorsAll q t (encCfg1 t) encCfg2 200 3 4 5 6).cost inp B s0 +
        ((seqs [cp 3 251, cp 4 252]).cost inp B s1 + 0)) := rfl
  have hCx := a1 P rfl rfl
  have hCxl := localColor_lt t P p (b + 1) x (by omega) hp2 (by rw [hQ]; positivity) (by rw [hQ]; exact hQ2)
  have hVx : (nbrList t x).length ≤ encVb q t n := by
    have := nbrList_length_le t x
    have := visits_le_visBound t x
    rw [hxl] at this
    show _ ≤ visBound q t P.m; omega
  have c2 : (seqs [cp 3 251, cp 4 252]).cost inp B s1 ≤ 2 * κ := by
    simp only [cost_seqs_cons, cost_seqs_nil, cost_cp, exec_seqs_cons, exec_cp, HS.setR_regs]
    simp only [Function.update_apply, show (252 : ℕ) ≠ 3 by omega, if_false, hCx, a2]
    have : 2 ^ (b + 1) ≤ encPW q t n := hpw
    have hQQ : P.Q * P.Q = P.Q ^ 2 := by ring
    rw [hQQ] at hCxl
    have := hK (localColor t P p x) (by omega)
    have hVe : encVb q t n = visBound q t P.m := rfl
    have := hK (nbrList t x).length (by omega)
    omega
  refine ⟨hs.congr' (fun r h1 h2 => by rw [f' r (by omega) (by omega), fr r (by omega)])
      (by rw [f' 1 (by omega) (by omega), fr 1 (by omega)]) (fun i => by
        simp only [HS.arr, m']; exact ar 1 i (by omega)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hw.congr (fun i _ => by simp only [HS.arr, m']; exact ar 2 _ (by omega))
  · rw [f' 2 (by omega) (by omega), fr 2 (by omega)]
  · rw [e3, hCx]
  · rw [e4, a2]
  · intro l hl; simp only [HS.arr, m']; exact a3 l hl P rfl rfl
  · rw [hs']; simp [a8, hs0]
  · rw [hs']; simp [a9, hs0]
  · rw [hc]
    have hcC : costC B q t n = (encVb q t n + 1) * (colorOfCost B q t P.m P.K P.Q (b + 1) (encVb q t n)
        (encMs q t n) (encMb q t n) encCfg2 + (19 * P.m + 40) * kappa B (RAM.bits (encMb q t n)) +
        (encCfg1 t).enumE B q P.m (2 * t)) + 6 * κ := rfl
    rw [hcC]
    rw [hxl] at a10
    omega

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

end Phases

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamEncode4
/-!
# The encoder program (q379, Part E), part 4: the main theorem

`encProg_spec`: for `2 ≤ q`, every `n` and `u : FixedWord q (parameters q t n).k`, with
`p = modSearch b` (`b = ceilLog 2 (r K + 1)`), under (H1) `∃ l ≤ n, rhoCond q t h l` and
(H2) `2^b ≤ p < 2^(b+1)`, the run of `encProg q t` from `HS.init n` on input `toWord u`
outputs `(encode t n p (toWord u)).map Fin.val`, leaves `1` in `encFlag`, and costs at most
`encCost q t n B`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

theorem localGood_eq_goodTest {q : ℕ} (t : ℕ) (P : Parameters) (p : ℕ) (x : Word q) :
    localGood t P p x = goodTest (localColor t P p x) (nbrList t x).length
      (fun l => localColor t P p ((nbrList t x).getD l [])) := by
  funext i
  unfold localGood goodTest
  rw [confusionNeighbors_all_range]

theorem filter_range_getD_le (G : ℕ → Bool) (L j : ℕ) :
    (((List.range L).filter G)[j]?).getD L ≤ L := by
  rcases h : ((List.range L).filter G)[j]? with _ | i
  · simp
  · simp only [Option.getD_some]
    have := List.mem_of_getElem? h
    simp only [List.mem_filter, List.mem_range] at this
    omega

set_option maxRecDepth 10000 in
theorem encProg_spec_oai (q t n B : ℕ) (hq : 2 ≤ q) (u : FixedWord q (parameters q t n).k)
    (H1 : ∃ l ≤ n, rhoCond q t (parameters q t n).h l)
    (H2 : 2 ^ ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) ≤
        modSearch (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1)) ∧
      modSearch (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1)) <
        2 ^ (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1)) :
    let p := modSearch (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1))
    let s := (encProg q t).exec (RAM.inputAt (toWord u)) (HS.init n)
    s.out = (encode t n p (toWord u)).map Fin.val ∧ s.regs encFlag = 1 ∧
    (encProg q t).cost (RAM.inputAt (toWord u)) B (HS.init n) ≤ encCost q t n B := by
  intro p s
  set w := toWord u with hwd
  set inp := RAM.inputAt w with hinp
  have hq0 : 0 < q := by omega
  have hwl : w.length = (parameters q t n).k := by rw [hwd]; unfold toWord; rw [List.length_ofFn]
  have hmk : (parameters q t n).m ≤ w.length := by rw [hwl]; exact params_m_le_k q t n
  have hMe := encM_eq q t n
  -- A
  obtain ⟨a1, a2, a3, a4⟩ := encA_spec inp B q t n hq H1
  set sA := (encA q t).exec inp (HS.init n) with hsA
  -- B
  obtain ⟨b1, b2, b3, b4, b5, -, b7, b8⟩ := encB_spec B q t n p hq w hwl sA a1 a2
  set sB := (encB t q).exec inp sA with hsB
  -- C
  obtain ⟨c1, c2, c3, c4, c5, c6, -, c8, c9⟩ :=
    encC_spec inp B q t n p w sB b1 H2.1 H2.2 hmk b2 b3 b4
  set sC := (encC q t).exec inp sB with hsC
  set x := w.take (parameters q t n).m with hx
  set cl := fun l => localColor t (parameters q t n) p ((nbrList t x).getD l []) with hcl
  have hclC : ∀ l < sC.regs 4, sC.arr 6 l = cl l := by
    intro l hl; rw [c5] at hl
    rw [c6 l hl]; simp only [hcl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl,
      Option.getD_some]
  have hQ : (parameters q t n).Q = 2 ^ ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) := rfl
  have hpw : 2 ^ (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1) ≤ encPW q t n :=
    pow_succ_le_encPW q t n
  have hp1 : 2 ^ ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) ≤ p := H2.1
  have hp2 : p < 2 ^ (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1) := H2.2
  have hp0 : p ≠ 0 := by
    have h := hp1
    have : 0 < 2 ^ ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) := Nat.two_pow_pos _
    omega
  have hcolor : ∀ y : Word q, localColor t (parameters q t n) p y ≤ (parameters q t n).Q ^ 2 + encPW q t n := by
    intro y
    have := localColor_lt t (parameters q t n) p (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1) y hp0
      hp2 (by rw [hQ]; positivity) (by rw [hQ]; exact Nat.pow_le_pow_right (by norm_num) (by omega))
    have hQQ : (parameters q t n).Q * (parameters q t n).Q = (parameters q t n).Q ^ 2 := by ring
    rw [hQQ] at this
    omega
  have hcM : ∀ y : Word q, localColor t (parameters q t n) p y ≤ encM q t n := by
    intro y; have := hcolor y; omega
  have hVx : (nbrList t x).length ≤ visBound q t (parameters q t n).m := by
    have := nbrList_length_le t x
    have := visits_le_visBound t x
    have hxl : x.length = (parameters q t n).m := by simp [hx, List.length_take]; omega
    rw [hxl] at this; omega
  have hj : value (w.drop (parameters q t n).m) < q ^ (parameters q t n).k := by
    have := EncS.value_lt (w.drop (parameters q t n).m)
    rw [List.length_drop, hwl] at this
    exact lt_of_lt_of_le this (Nat.pow_le_pow_right hq0 (by omega))
  -- D
  obtain ⟨d1, d2, -, d4, d5, -, d7, d8⟩ := encD_spec inp B q t n p sC c1 cl (encM q t n) hclC
    (fun l _ => hcM _)
    (by rw [c4]; exact hcM x) (by rw [c5]; omega) (by rw [c3, b5]; omega) (by omega)
    (by omega)
  set sD := encD.exec inp sC with hsD
  have hgood : goodTest (sC.regs 3) (sC.regs 4) cl = localGood t (parameters q t n) p x := by
    rw [c4, c5, localGood_eq_goodTest]
  rw [hgood, c3, b5] at d2
  set j := value (w.drop (parameters q t n).m) with hjd
  have hsel : sD.regs 6 = (localPair t (parameters q t n) p x j).1 := by rw [d2]; rfl
  have hselL : sD.regs 6 ≤ (parameters q t n).L := by rw [d2]; exact filter_range_getD_le _ _ _
  have hCxD : sD.regs 3 = localColor t (parameters q t n) p x := by rw [d4, c4]
  -- E
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := encE_spec inp B q t n p hq sD d1 hselL
    (by rw [hCxD]; exact hcolor x)
  set sE := (encE q).exec inp sD with hsE
  have hidx : sE.regs 22 = value (serialize q (parameters q t n) (localPair t (parameters q t n) p x j)) := by
    rw [e2, hsel, hCxD]; rfl
  -- F
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, -, f10, f11⟩ := encF_spec inp B q t n p hq sE e1
  set sF := (encF q t).exec inp sE with hsF
  set T := shortTable q t (parameters q t n).h with hT
  set idx := value (serialize q (parameters q t n) (localPair t (parameters q t n) p x j)) with hidxd
  have hidxF : sF.regs 22 = idx := by rw [f2 22 (by omega), hidx]
  have hidxh : idx < q ^ (parameters q t n).h := by
    have := EncS.value_lt (serialize q (parameters q t n) (localPair t (parameters q t n) p x j))
    have hl : (serialize q (parameters q t n) (localPair t (parameters q t n) p x j)).length = (parameters q t n).h := by
      simp only [serialize, List.length_append, EncS.repr_length hq0]; rfl
    rw [hl] at this; exact this
  have hwF : WordAt sF 2 0 w := by
    have hwE : WordAt sE 2 0 w := by
      have hwD : WordAt sD 2 0 w := c2.congr (fun i _ => by simp [HS.arr, d5])
      exact hwD.congr (fun i _ => by simp [HS.arr, e3])
    exact hwE.congr (fun i _ => f3 2 _ (by omega))
  have hoF : sF.out = [] := by rw [f10, e5, d7, c8, b7, a3]
  -- G
  obtain ⟨g1, g2, g3⟩ := encG_spec inp B q t n p hq sF f1 w hwF hmk hoF (by rw [hidxF]; exact hidxh)
    f8 (fun h => by rw [hidxF]; rw [hidxF, ← f6] at h; exact f5 idx h)
  have hs : s = (encG q t).exec inp sF := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hs, g1, hidxF, ← f6]
    have henc : encode t n p w = x ++ shortEncode t (parameters q t n).h (serialize q (parameters q t n) (localPair t (parameters q t n) p x j)) := rfl
    rw [henc, List.map_append]
    rw [← hx]
    refine congrArg₂ (· ++ ·) rfl ?_
    unfold shortEncode
    rw [← hidxd]
    by_cases hc : idx < T.length
    · rw [if_pos hc, List.getElem?_eq_getElem hc, Option.getD_some, f4 idx hc]
    · rw [if_neg hc, List.getElem?_eq_none (Nat.le_of_not_lt hc)]; rfl
  · rw [hs]; exact g2
  · have hc : (encProg q t).cost inp B (HS.init n) = (encA q t).cost inp B (HS.init n) +
        ((encB t q).cost inp B sA + ((encC q t).cost inp B sB + (encD.cost inp B sC +
        ((encE q).cost inp B sD + ((encF q t).cost inp B sE + ((encG q t).cost inp B sF + 0)))))) := rfl
    rw [hc]
    have hVb : sC.regs 4 ≤ encVb q t n := by rw [c5]; exact hVx
    have : (3 * ((parameters q t n).L + 1) + (parameters q t n).L * (10 * sC.regs 4 + 16) + 3) * kappa B (RAM.bits (8 * encM q t n + 8)) ≤
        (3 * ((parameters q t n).L + 1) + (parameters q t n).L * (10 * encVb q t n + 16) + 3) * kappa B (RAM.bits (8 * encM q t n + 8)) :=
      Nat.mul_le_mul_right _ (by
        have := Nat.mul_le_mul_left (parameters q t n).L
          (show 10 * sC.regs 4 + 16 ≤ 10 * encVb q t n + 16 by omega)
        omega)
    have b8' : (encB t q).cost inp B sA ≤ (11 * (parameters q t n).k + 7 * (parameters q t n).m +
        7 * ((parameters q t n).k - (parameters q t n).m) + 40) * kappa B (RAM.bits (encM q t n)) := b8
    unfold encCost
    omega

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.encProg_spec_oai := @EditMulticoloring.Dev.Ram.encProg_spec_oai
