-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.colorOf_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:35:20.446+00:00
-- url     : https://prove2.me/submissions/dfa5b1ca-365e-4adb-9b6a-b7d0297d7e53

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_congr
import Theorems.Thm_EditMulticoloring_Dev_Ram_colorInit_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_colorOut_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_colorSearch_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_enBody_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_enumScripts_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_foldl_listF
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le
import Theorems.Thm_EditMulticoloring_Dev_Ram_length_le_of_mem_visits
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

theorem exec_out_of_emits (c : Cmd) (h : c.emits = false) (s : HS) :
    (c.exec inp s).out = s.out := by
  induction c generalizing s with
  | prim p => cases p <;> simp_all [Cmd.emits, Cmd.exec, Prim.exec]
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [Cmd.emits, Bool.or_eq_false_iff] at h
    simp [ih₁ h.1, ih₂ h.2]
  | ifz a c₁ c₂ ih₁ ih₂ =>
    simp only [Cmd.emits, Bool.or_eq_false_iff] at h
    simp only [exec_ifz]; split_ifs
    · exact ih₁ h.1 s
    · exact ih₂ h.2 s
  | loop a c ih =>
    simp only [Cmd.emits] at h
    rw [exec_loop]
    exact iterate_induct (fun t => t.out = s.out) (fun t ht => (ih h t).trans ht) _ _ rfl
  | skip => rfl

end Frames

/-! ## Loops -/

/-! ## Words stored in arrays -/

/-! ## Copying a block of cells -/

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

/-! ## `gfMul` -/

section Prog
variable (inp : ℕ → ℕ) (B : ℕ)


/-! ## The field context and `fieldMul` -/

theorem GFCtx.congr {s s' : HS} {g p W : ℕ} (h : GFCtx s g p W)
    (h' : ∀ r, g ≤ r → r < g + 6 → s'.regs r = s.regs r) : GFCtx s' g p W := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  exact ⟨(h' _ le_rfl (by omega)).trans h0, (h' _ (by omega) (by omega)).trans h1,
    (h' _ (by omega) (by omega)).trans h2, (h' _ (by omega) (by omega)).trans h3,
    (h' _ (by omega) (by omega)).trans h4, (h' _ (by omega) (by omega)).trans h5⟩


/-! ## `bitEval` on a digit array -/

end Prog

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

theorem nbrList_length_le {q : ℕ} (t : ℕ) (x : Word q) :
    (nbrList t x).length ≤ (visits (2 * t) x).length := List.length_filter_le _ _

/-! ## Initialisation: field context, a copy of `x`, the digits of `value x` -/

/-! ## Enumeration: digits of every neighbour -/

section Enum
variable (inp : ℕ → ℕ) (B : ℕ)

theorem EnInv.stable {q : ℕ} {s : ℕ} {cfg : EnumCfg} {g DG K Q : ℕ} {x : Word q} {st0 : HS}
    (hr0 : g + 51 ≤ cfg.r0) (hDG : DG < cfg.a0)
    {l : List (Word q)} {st st' : HS} (h : EnInv s cfg g DG K Q x st0 l st) (hA : cfg.Agree s st st') :
    EnInv s cfg g DG K Q x st0 l st' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have nR : ∀ r, r < cfg.r0 → ¬ cfg.ownsReg s r := fun r hr h => by
    simp only [EnumCfg.ownsReg] at h; omega
  have nA : ¬ cfg.ownsArr s DG := fun h => by simp only [EnumCfg.ownsArr] at h; omega
  refine ⟨(hA.1 _ (nR _ (by omega))).trans h1, h2, fun m hm i hi => (hA.2.1 _ _ nA).trans (h3 m hm i hi),
    fun r hr => (hA.1 _ (nR _ (by omega))).trans (h4 r hr), fun r hr hn => (hA.1 _ hn).trans (h5 r hr hn),
    fun y i hy hn => (hA.2.1 _ _ hn).trans (h6 y i hy hn), fun i hi => (hA.2.1 _ _ nA).trans (h7 i hi),
    hA.2.2.1.trans h8, hA.2.2.2.trans h9⟩

theorem colorEnum_spec {q : ℕ} (t : ℕ) (cfg : EnumCfg) (g XA DG K Q Mb : ℕ) (x : Word q) (st : HS)
    (hr0 : g + 51 ≤ cfg.r0) (hXA : XA < cfg.a0) (hDG : DG < cfg.a0) (hXD : XA ≠ DG)
    (e18 : st.regs (g + 18) = K) (e24 : st.regs (g + 24) = Q) (e25 : st.regs (g + 25) = x.length)
    (hX0 : WordAt st XA 0 x)
    (hlen : st.regs (cfg.lenR (2 * t)) = x.length) (hx : WordAt st (cfg.buf (2 * t)) 0 x)
    (hMb : q ^ x.length + 2 * q + cfg.a0 + 2 * t + XA + DG + 2 * x.length + Q +
      ((visits (2 * t) x).length + 1) * K + (visits (2 * t) x).length + 2 ≤ Mb) :
    let st' := (colorEnum q (2 * t) cfg g XA DG).exec inp st
    EnInv (2 * t) cfg g DG K Q x (st.setR (g + 26) 0) (nbrList t x) st' ∧
    st'.regs (cfg.lenR (2 * t)) = x.length ∧ WordAt st' (cfg.buf (2 * t)) 0 x ∧
    (colorEnum q (2 * t) cfg g XA DG).cost inp B st ≤ kappa B (RAM.bits 0) +
      (visits (2 * t) x).length * ((19 * x.length + 7 * K + 40) * kappa B (RAM.bits Mb) +
        cfg.enumE B q x.length (2 * t)) := by
  intro st'
  set s := 2 * t with hs
  set V := (visits s x).length with hV
  set s1 := st.setR (g + 26) 0 with hs1
  have hlenR : cfg.lenR s = cfg.r0 + (18 + 3 * s) := rfl
  have E := enumScripts_spec s cfg (enBody q cfg g XA DG) inp B (EnInv s cfg g DG K Q x s1)
    (listF x) ((19 * x.length + 7 * K + 40) * kappa B (RAM.bits Mb)) x []
    (fun a st st' h hA => EnInv.stable hr0 hDG h hA)
    (by
      intro l st2 w j hj hw hl hI hVL hvis
      have hwmem : w ∈ visits s x := hw ▸ List.getElem_mem hj
      have hwl := length_le_of_mem_visits s x hwmem
      have hlj : l.length + 1 ≤ V := by
        rw [hl, foldl_listF]
        have := List.length_filter_le (fun w => decide (w.length = x.length ∧ w ≠ x))
          ((visits s x).take j)
        simp only [List.nil_append, List.length_take] at this ⊢; omega
      exact enBody_spec inp B s cfg g XA DG K Q V Mb x s1 hr0 hXA hDG hXD
        (by simp (disch := omega) [hs1, upd_ne, e18]) (by simp (disch := omega) [hs1, upd_ne, e24])
        (by simp (disch := omega) [hs1, upd_ne, e25]) (hX0.congr (fun _ _ => rfl)) hMb
        l st2 w hI hVL hvis hwl hlj)
    s1 (by rw [hs1, HS.setR_regs, upd_ne (by simp only [EnumCfg.lenR]; omega)]; exact hlen)
    (hx.congr (fun _ _ => rfl))
    ⟨by simp [hs1], by simp, fun m hm => absurd hm (Nat.not_lt_zero _), fun _ _ => rfl,
      fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
  obtain ⟨E1, E2, E3, E4⟩ := E
  have hex : st' = (enumScripts q s cfg (enBody q cfg g XA DG)).exec inp s1 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hex]
    have : nbrList t x = (visits s x).foldl (listF x) [] := by
      rw [foldl_listF]; rfl
    rw [this]; exact E1
  · rw [hex]; exact E2
  · rw [hex]; exact E3
  · show kappa B (RAM.bits 0) + (enumScripts q s cfg (enBody q cfg g XA DG)).cost inp B s1 ≤ _
    exact Nat.add_le_add_left E4 _

end Enum

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

section Out
variable (inp : ℕ → ℕ) (B : ℕ)


/-- **`colorOf`**: input `x` in `cfg.buf (2t)` (offset 0) with `|x|` in `cfg.lenR (2t)`;
registers `g = p`, `g+3 = W`, `g+18 = K`, `g+24 = Q`.  Output `g+36 = localColor t P p x` for
every `P` with `P.Q = Q`, `P.K = K`.  `Vb` is any bound on the number of visited words. -/
theorem colorOf_spec_oai {q : ℕ} (t : ℕ) (cfg : EnumCfg) (g XA DG : ℕ) (x : Word q) (st : HS)
    (p W Q K Vb Ms Mb : ℕ)
    (hr0 : g + 51 ≤ cfg.r0) (hXA : XA < cfg.a0) (hDG : DG < cfg.a0) (hXD : XA ≠ DG)
    (h0 : st.regs g = p) (h3 : st.regs (g + 3) = W) (h18 : st.regs (g + 18) = K)
    (h24 : st.regs (g + 24) = Q)
    (hlen : st.regs (cfg.lenR (2 * t)) = x.length) (hx : WordAt st (cfg.buf (2 * t)) 0 x)
    (hp : p ≠ 0) (hpW : p < 2 ^ W) (hQ0 : 0 < Q) (hQW : Q ≤ 2 ^ W)
    (hV : (visits (2 * t) x).length ≤ Vb)
    (hMs : p * 2 ^ (2 * W) + 6 * 2 ^ (2 * W) + DG + (Vb + 2) * K + Vb ≤ Ms)
    (hMb : q ^ x.length + 2 * q + cfg.a0 + 2 * t + XA + DG + 2 * x.length + Q + (Vb + 1) * K + Vb + 2
      ≤ Mb) :
    let st' := (colorOf q t cfg g XA DG).exec inp st
    (∀ P : Parameters, P.Q = Q → P.K = K → st'.regs (g + 36) = localColor t P p x) ∧
    (∀ r, (r < g + 1 ∨ r = g + 3 ∨ r = g + 18 ∨ r = g + 24 ∨ g + 51 ≤ r) →
      ¬ cfg.ownsReg (2 * t) r → st'.regs r = st.regs r) ∧
    (∀ y i, y ≠ XA → y ≠ DG → ¬ cfg.ownsArr (2 * t) y → st'.arr y i = st.arr y i) ∧
    st'.regs (cfg.lenR (2 * t)) = x.length ∧ WordAt st' (cfg.buf (2 * t)) 0 x ∧
    st'.cur = st.cur ∧ st'.out = st.out ∧
    (colorOf q t cfg g XA DG).cost inp B st ≤
      (Vb + 1) * ((19 * x.length + 7 * K + 40) * kappa B (RAM.bits Mb) +
        cfg.enumE B q x.length (2 * t)) +
      ((Q + 1) * (Vb + 1) * (K * (36 * W + 24) + 15) + 16 * W + 3 * Q + 18) * kappa B (RAM.bits Ms) := by
  intro st'
  have hnR : ∀ r, r < cfg.r0 → ¬ cfg.ownsReg (2 * t) r := fun r hr h => by
    simp only [EnumCfg.ownsReg] at h; omega
  have hnA : ∀ y, y < cfg.a0 → ¬ cfg.ownsArr (2 * t) y := fun y hy h => by
    simp only [EnumCfg.ownsArr] at h; omega
  have hbuf : cfg.buf (2 * t) = cfg.a0 + 1 + 2 * t := rfl
  have hlenR : cfg.lenR (2 * t) = cfg.r0 + (18 + 3 * (2 * t)) := rfl
  -- init
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11⟩ := colorInit_spec inp B (2 * t) cfg g XA DG x st
    p W Q K Ms Mb hr0 hXA hDG hXD h0 h3 h18 h24 hlen hx hp hpW (by omega) (by
      have : K ≤ (Vb + 1) * K := Nat.le_mul_of_pos_left _ (by omega)
      omega)
  set s1 := (colorInit q (2 * t) cfg g XA DG).exec inp st with hs1
  have l1 : s1.regs (cfg.lenR (2 * t)) = x.length := by rw [i7 _ (by omega), hlen]
  have x1 : WordAt s1 (cfg.buf (2 * t)) 0 x :=
    hx.congr (fun i _ => i8 _ _ (by omega) (by omega))
  -- enumeration
  obtain ⟨e1, e2, e3, e4⟩ := colorEnum_spec inp B t cfg g XA DG K Q Mb x s1 hr0 hXA hDG hXD i2 i3 i4 i5
    l1 x1 (by
      have : ((visits (2 * t) x).length + 1) * K ≤ (Vb + 1) * K := Nat.mul_le_mul_right _ (by omega)
      omega)
  set s2 := (colorEnum q (2 * t) cfg g XA DG).exec inp s1 with hs2
  obtain ⟨E26, -, Erows, Elow, Ehigh, Earr, Erow0, Ecur, Eout⟩ := e1
  set N := nbrList t x with hN
  set J := N.length with hJ
  have hJV : J ≤ Vb := (nbrList_length_le t x).trans hV
  have lowE : ∀ r, r < g + 26 → s2.regs r = s1.regs r := fun r h => by
    rw [Elow r h]; simp (disch := omega) [upd_ne]
  -- lit DG
  set s3 := (lit (g + 16) DG).exec inp s2 with hs3
  have r3 : ∀ r, r ≠ g + 16 → s3.regs r = s2.regs r := fun r h => by
    simp (disch := omega) [hs3, upd_ne]
  have m3 : s3.mem = s2.mem := rfl
  have hctx3 : GFCtx s3 g p W := i1.congr (fun r h1 h2 => by
    rw [r3 r (by omega), lowE r (by omega)])
  have hrows : Rows s3 DG K Q J (rowIds t x) := by
    intro m hm i hi
    rcases m with _ | m
    · simp only [Nat.zero_mul, Nat.zero_add, rowIds]
      show s2.arr DG i = _
      rw [Erow0 i hi]
      show s1.arr DG i = _
      exact i6 i hi
    · show s2.arr DG ((m + 1) * K + i) = _
      rw [Erows m (by omega) i hi]
      simp only [rowIds]
      have hm' : m < N.length := by omega
      rw [List.getD_eq_getElem _ _ hm']
  -- search
  obtain ⟨c1, c2, c3, c4⟩ := colorSearch_spec inp B g s3 p W Q K J DG Ms (rowIds t x) hctx3 hp hpW
    hQ0 hQW (by simp [hs3]) (by rw [r3 _ (by omega), lowE _ (by omega), i2])
    (by rw [r3 _ (by omega), lowE _ (by omega), i3]) (by rw [r3 _ (by omega), E26]) hrows (by
      have : (J + 2) * K ≤ (Vb + 2) * K := Nat.mul_le_mul_right _ (by omega)
      omega)
  set s4 := (colorSearch g).exec inp s3 with hs4
  set α := ((List.range Q).find? (okAt Q p K (rowIds t x) J)).getD 0 with hα
  have hαQ : α < Q := by
    rcases hf : (List.range Q).find? (okAt Q p K (rowIds t x) J) with _ | v
    · rw [hα, hf]; exact hQ0
    · rw [hα, hf]; exact find_range_lt _ _ _ hf
  have k4 : ∀ r, KeepS g r → s4.regs r = s3.regs r := c2
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := colorOut_spec inp B g s4 p W Q K DG α (value x) Ms
    (hctx3.congr (fun r h1 h2 => k4 r (by unfold KeepS; omega))) hp hpW hQ0 hQW
    (by rw [k4 _ (by unfold KeepS; omega)]; simp [hs3])
    (by rw [k4 _ (by unfold KeepS; omega), r3 _ (by omega), lowE _ (by omega), i2])
    (by rw [k4 _ (by unfold KeepS; omega), r3 _ (by omega), lowE _ (by omega), i3]) c1 hαQ
    (fun i hi => by
      rw [show s4.arr DG i = s3.arr DG (0 * K + i) by simp [HS.arr, c3]]
      exact hrows 0 (by omega) i hi)
    (by have : 2 * K ≤ (Vb + 2) * K := Nat.mul_le_mul_right _ (by omega)
        omega)
  have hex : st' = (colorOut g).exec inp s4 := rfl
  have hcur4 : s4.cur = s3.cur := exec_cur_of_reads inp _ rfl s3
  have hout4 : s4.out = s3.out := exec_out_of_emits inp _ rfl s3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P hPQ hPK
    rw [hex, o1, localColor_eq, hPQ, hPK]
  · intro r hr hn
    rw [hex, o2 r (by unfold KeepS; omega), k4 r (by unfold KeepS; omega), r3 r (by omega)]
    rcases hr with hr | hr | hr | hr | hr
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
      · rw [lowE r (by omega), i7 r (by omega)]
      · rw [lowE _ (by omega), i1.1, h0]
    · subst hr; rw [lowE _ (by omega), i1.2.2.2.1, h3]
    · subst hr; rw [lowE _ (by omega), i2, h18]
    · subst hr; rw [lowE _ (by omega), i3, h24]
    · rw [Ehigh r hr hn]; simp (disch := omega) [upd_ne]; exact i7 r (by omega)
  · intro y i h1 h2 h3'
    rw [hex]
    show ((colorOut g).exec inp s4).arr y i = _
    simp only [HS.arr, o3, c3, m3]
    show s2.arr y i = _
    rw [Earr y i h2 h3']
    exact i8 y i h1 h2
  · rw [hex, o2 _ (by unfold KeepS; simp only [EnumCfg.lenR]; omega),
      k4 _ (by unfold KeepS; simp only [EnumCfg.lenR]; omega), r3 _ (by simp only [EnumCfg.lenR]; omega)]
    exact e2
  · rw [hex]
    exact e3.congr (fun i _ => by simp only [HS.arr, o3, c3, m3])
  · rw [hex, o4, hcur4]
    show s2.cur = _
    rw [Ecur]; exact i9
  · rw [hex, o5, hout4]
    show s2.out = _
    rw [Eout]; exact i10
  · have hc : (colorOf q t cfg g XA DG).cost inp B st = (colorInit q (2 * t) cfg g XA DG).cost inp B st +
        ((colorEnum q (2 * t) cfg g XA DG).cost inp B s1 + (kappa B (RAM.bits DG) +
        ((colorSearch g).cost inp B s3 + ((colorOut g).cost inp B s4 + 0)))) := rfl
    rw [hc]
    set κs := kappa B (RAM.bits Ms) with hκs
    set κb := kappa B (RAM.bits Mb) with hκb
    set X := K * (36 * W + 24) with hX
    set Cb := (19 * x.length + 7 * K + 40) * κb with hCb
    set E := cfg.enumE B q x.length (2 * t) with hE
    have hDGk : kappa B (RAM.bits DG) ≤ κs := kappa_bits_le B (by omega)
    have h0k : kappa B (RAM.bits 0) ≤ κb := kappa_bits_le B (by omega)
    have hs : 16 * W + 12 + 1 + (Q * ((J + 1) * (X + 15)) + 3 * Q + 5) + (X + 8) ≤
        (Q + 1) * (Vb + 1) * (X + 15) + 16 * W + 3 * Q + 18 := by
      have a1 : Q * ((J + 1) * (X + 15)) ≤ Q * ((Vb + 1) * (X + 15)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      have a2 : X + 15 ≤ (Vb + 1) * (X + 15) := Nat.le_mul_of_pos_left _ (by omega)
      have a3 : (Q + 1) * (Vb + 1) * (X + 15) = Q * ((Vb + 1) * (X + 15)) + (Vb + 1) * (X + 15) := by
        ring
      omega
    have hsκ := Nat.mul_le_mul_right κs hs
    have e1 : (16 * W + 12 + 1 + (Q * ((J + 1) * (X + 15)) + 3 * Q + 5) + (X + 8)) * κs =
        (16 * W + 12) * κs + κs + (Q * ((J + 1) * (X + 15)) + 3 * Q + 5) * κs + (X + 8) * κs := by ring
    have e2 : ((Q + 1) * (Vb + 1) * (X + 15) + 16 * W + 3 * Q + 18) * κs =
        ((Q + 1) * (Vb + 1) * (K * (36 * W + 24) + 15) + 16 * W + 3 * Q + 18) * κs := by rw [hX]
    have hb1 : (14 * x.length + 7 * K + 26) * κb + κb ≤ Cb := by
      rw [hCb, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    have hb2 : (visits (2 * t) x).length * (Cb + E) ≤ Vb * (Cb + E) := Nat.mul_le_mul_right _ hV
    have e3 : (Vb + 1) * (Cb + E) = Vb * (Cb + E) + Cb + E := by ring
    rw [e3]
    omega

end Out

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.colorOf_spec_oai := @EditMulticoloring.Dev.Ram.colorOf_spec_oai
