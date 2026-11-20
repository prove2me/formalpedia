-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.enBody_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:36:35.202313+00:00
-- url     : https://prove2.me/submissions/cef2c7fb-34b5-41f3-ba59-5e29789a9169

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_congr
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_lt
import Theorems.Thm_EditMulticoloring_Dev_Ram_digitsW_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_eqW_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_one_le
import Theorems.Thm_EditMulticoloring_Dev_Ram_upd_eq
import Theorems.Thm_EditMulticoloring_Dev_Ram_upd_ne
import Theorems.Thm_EditMulticoloring_Dev_Ram_valueW_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_valueW_word
import Theorems.Thm_EditMulticoloring_Dev_Ram_words_eq_iff

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

theorem horner_lt (q : ℕ) (g : ℕ → ℕ) (N : ℕ) (hg : ∀ i < N, g i < q) :
    ∀ k ≤ N, horner q g k < q ^ k := by
  intro k hk
  induction k with
  | zero => simp [horner]
  | succ k ih =>
    have h1 := ih (by omega)
    have h2 := hg k (by omega)
    simp only [horner, pow_succ]
    have : horner q g k + 1 ≤ q ^ k := h1
    nlinarith

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

/-! ## Initialisation: field context, a copy of `x`, the digits of `value x` -/

section Init
variable (inp : ℕ → ℕ) (B : ℕ)

theorem value_lt {q : ℕ} (x : Word q) : value x < q ^ x.length ∨ x = [] := by
  rcases x with _ | ⟨a, x⟩
  · right; rfl
  · left
    have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le _) a.isLt
    have := horner_lt q (fun i => ((a :: x)[i]?.map Fin.val).getD 0) (a :: x).length (by
      intro i hi
      simp only [List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]
      exact (a :: x)[i].isLt) _ le_rfl
    rwa [horner_value (a :: x) _ (fun i h => by simp [List.getElem?_eq_getElem h])] at this

theorem value_le {q : ℕ} (x : Word q) : value x ≤ q ^ x.length := by
  rcases value_lt x with h | rfl
  · exact h.le
  · simp [value]

end Init

/-! ## Enumeration: digits of every neighbour -/

section Enum
variable (inp : ℕ → ℕ) (B : ℕ)

/-- A body run that changes only registers `g+26 .. g+50` (keeping `g+26`) and no memory. -/
theorem EnInv.keep {q : ℕ} {s : ℕ} {cfg : EnumCfg} {g DG K Q : ℕ} {x : Word q} {st0 : HS}
    {l : List (Word q)} {st sF : HS} (h : EnInv s cfg g DG K Q x st0 l st)
    (hR : ∀ r, (r ≤ g + 26 ∨ g + 51 ≤ r) → sF.regs r = st.regs r) (hM : sF.mem = st.mem)
    (hc : sF.cur = st.cur) (ho : sF.out = st.out) :
    EnInv s cfg g DG K Q x st0 l sF := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have hA : ∀ y i, sF.arr y i = st.arr y i := fun y i => by simp only [HS.arr, hM]
  refine ⟨(hR _ (by omega)).trans h1, h2, fun m hm i hi => (hA _ _).trans (h3 m hm i hi),
    fun r hr => (hR _ (by omega)).trans (h4 r hr), fun r hr hn => (hR _ (by omega)).trans (h5 r hr hn),
    fun y i hy hn => (hA _ _).trans (h6 y i hy hn), fun i hi => (hA _ _).trans (h7 i hi),
    hc.trans h8, ho.trans h9⟩

/-- A body run that appends `w`: row `|l| + 1` of `DG` written, `g+26` incremented. -/
theorem EnInv.app {q : ℕ} {s : ℕ} {cfg : EnumCfg} {g DG K Q : ℕ} {x : Word q} {st0 : HS}
    {l : List (Word q)} {st sF : HS} {w : Word q} (h : EnInv s cfg g DG K Q x st0 l st)
    (hR : ∀ r, (r < g + 26 ∨ g + 51 ≤ r) → sF.regs r = st.regs r)
    (h26 : sF.regs (g + 26) = l.length + 1)
    (hA : ∀ y i, ¬ (y = DG ∧ (l.length + 1) * K ≤ i ∧ i < (l.length + 1) * K + K) →
      sF.arr y i = st.arr y i)
    (hrow : ∀ i < K, sF.arr DG ((l.length + 1) * K + i) = (value w / Q ^ i) % Q)
    (hwl : w.length = x.length) (hc : sF.cur = st.cur) (ho : sF.out = st.out) :
    EnInv s cfg g DG K Q x st0 (l ++ [w]) sF := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨by rw [h26]; simp, fun v hv => ?_, fun m hm i hi => ?_,
    fun r hr => (hR _ (by omega)).trans (h4 r hr), fun r hr hn => (hR _ (by omega)).trans (h5 r hr hn),
    fun y i hy hn => (hA _ _ (fun h => hy h.1)).trans (h6 y i hy hn), fun i hi => ?_,
    hc.trans h8, ho.trans h9⟩
  · rcases List.mem_append.mp hv with hv | hv
    · exact h2 v hv
    · simp at hv; rw [hv, hwl]
  · simp only [List.length_append, List.length_singleton] at hm
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
    · rw [List.getElem_append_left hm]
      have : (m + 1) * K + K ≤ (l.length + 1) * K := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
      rw [hA _ _ (by omega)]; exact h3 m hm i hi
    · rw [List.getElem_append_right (by simp)]
      simp only [Nat.sub_self, List.getElem_cons_zero]
      exact hrow i hi
  · have : K ≤ (l.length + 1) * K := Nat.le_mul_of_pos_left _ (by omega)
    rw [hA _ _ (by omega)]; exact h7 i hi


set_option maxHeartbeats 1600000 in
theorem enBody_spec_oai {q : ℕ} (s : ℕ) (cfg : EnumCfg) (g XA DG K Q V Mb : ℕ) (x : Word q) (st0 : HS)
    (hr0 : g + 51 ≤ cfg.r0) (hXA : XA < cfg.a0) (hDG : DG < cfg.a0) (hXD : XA ≠ DG)
    (e18 : st0.regs (g + 18) = K) (e24 : st0.regs (g + 24) = Q) (e25 : st0.regs (g + 25) = x.length)
    (hX0 : WordAt st0 XA 0 x)
    (hMb : q ^ x.length + 2 * q + cfg.a0 + s + XA + DG + 2 * x.length + Q + (V + 1) * K + V + 2 ≤ Mb)
    (l : List (Word q)) (st : HS) (w : Word q) (hI : EnInv s cfg g DG K Q x st0 l st)
    (hVL : st.regs cfg.VL = w.length) (hvis : WordAt st cfg.vis 0 w)
    (hwl : w.length ≤ x.length + s) (hJ : l.length + 1 ≤ V) :
    EnInv s cfg g DG K Q x st0 (listF x l w) ((enBody q cfg g XA DG).exec inp st) ∧
    cfg.BodyFrame s st ((enBody q cfg g XA DG).exec inp st) ∧
    (enBody q cfg g XA DG).cost inp B st ≤ (19 * x.length + 7 * K + 40) * kappa B (RAM.bits Mb) := by
  set L := x.length with hL
  set κ := kappa B (RAM.bits Mb) with hκ
  obtain ⟨i26, -, -, i4, -, i6, -, -, -⟩ := id hI
  have f18 : st.regs (g + 18) = K := by rw [i4 _ (by omega), e18]
  have f24 : st.regs (g + 24) = Q := by rw [i4 _ (by omega), e24]
  have f25 : st.regs (g + 25) = L := by rw [i4 _ (by omega), e25]
  have nA : ∀ y, y < cfg.a0 → ¬ cfg.ownsArr s y := fun y hy h => by
    simp only [EnumCfg.ownsArr] at h; omega
  have hX : WordAt st XA 0 x := hX0.congr (fun i _ => i6 _ _ hXD (nA _ hXA))
  have hVL' : st.regs cfg.r0 = w.length := hVL
  have hbf : ∀ sF : HS, (∀ r, g + 51 ≤ r → sF.regs r = st.regs r) →
      (∀ y i, y ≠ DG → sF.arr y i = st.arr y i) → cfg.BodyFrame s st sF := by
    intro sF h1 h2
    refine ⟨fun r hr _ => h1 r (by simp only [EnumCfg.ownsReg] at hr; omega), fun y i hy _ => h2 y i ?_⟩
    rintro rfl; exact nA _ hDG hy
  set P1 := seqs [ar .sub (g + 38) cfg.VL (g + 25), ar .sub (g + 39) (g + 25) cfg.VL,
      ar .add (g + 38) (g + 38) (g + 39)] with hP1
  set s1 := P1.exec inp st with hs1
  have r1 : ∀ r, (r < g + 38 ∨ g + 40 ≤ r) → s1.regs r = st.regs r := by
    intro r hr; simp (disch := omega) [hs1, hP1, upd_ne]
  have m1 : s1.mem = st.mem := by simp [hs1, hP1]
  have d1 : s1.regs (g + 38) = (w.length - L) + (L - w.length) := by
    simp (disch := omega) [hs1, hP1, upd_ne, hVL', f25]
  have c1 : P1.cost inp B st ≤ 3 * κ := by
    simp (disch := omega) only [hP1, cost_seqs_cons, cost_seqs_nil, exec_seqs_cons, exec_ar,
      cost_ar, HS.setR_regs, upd_ne, upd_eq, hVL', f25, arith_sub, arith_add, EnumCfg.VL]
    have := kappa_bits_le B (a := w.length + L) (M := Mb) (by omega)
    have := kappa_bits_le B (a := L + w.length) (M := Mb) (by omega)
    have := kappa_bits_le B (a := w.length - L + (L - w.length)) (M := Mb) (by omega)
    omega
  have hcur1 : s1.cur = st.cur := by simp [hs1, hP1]
  have hout1 : s1.out = st.out := by simp [hs1, hP1]
  have K0 := kappa_bits_le B (a := 0) (M := Mb) (by omega)
  have K1 := kappa_bits_one_le B Mb
  by_cases hd : (w.length - L) + (L - w.length) = 0
  · have hwx : w.length = L := by omega
    set P2 := seqs [lit (g + 40) cfg.vis, lit (g + 41) 0, lit (g + 42) XA, lit (g + 43) 0,
      cp (g + 44) (g + 25)] with hP2
    set s2 := P2.exec inp s1 with hs2
    have r2 : ∀ r, (r < g + 40 ∨ g + 45 ≤ r) → s2.regs r = s1.regs r := by
      intro r hr; simp (disch := omega) [hs2, hP2, upd_ne]
    have m2 : s2.mem = st.mem := by simp [hs2, hP2, m1]
    have v40 : s2.regs (g + 40) = cfg.a0 := by simp [hs2, hP2]
    have v41 : s2.regs (g + 41) = 0 := by simp (disch := omega) [hs2, hP2, upd_ne]
    have v42 : s2.regs (g + 42) = XA := by simp (disch := omega) [hs2, hP2, upd_ne]
    have v43 : s2.regs (g + 43) = 0 := by simp (disch := omega) [hs2, hP2, upd_ne]
    have v44 : s2.regs (g + 44) = L := by
      simp (disch := omega) [hs2, hP2, upd_ne]; rw [r1 _ (by omega), f25]
    have hw2 : WordAt s2 cfg.a0 0 w := hvis.congr (fun i _ => by simp [HS.arr, m2])
    have hX2 : WordAt s2 XA 0 x := hX.congr (fun i _ => by simp [HS.arr, m2])
    obtain ⟨q1, q2, q3, q4, q5, q6⟩ := eqW_spec inp B (g + 40) s2 q Mb
      (fun i hi => by
        rw [v40, v41, v42, v43]; rw [v44] at hi
        exact ⟨(hw2.lt i (by omega)).le, (hX2.lt i (by omega)).le⟩)
      (by rw [v40, v41, v42, v43, v44]; omega)
    set s3 := (eqW (g + 40)).exec inp s2 with hs3
    have r3 : ∀ r, (r < g + 45 ∨ g + 51 ≤ r) → s3.regs r = s2.regs r := q2
    have m3 : s3.mem = st.mem := by rw [q3, m2]
    have hflag : s3.regs (g + 45) = if w = x then 1 else 0 := by
      rw [q1, v40, v41, v42, v43, v44]
      have := words_eq_iff s2 cfg.a0 0 XA 0 w x hw2 hX2 (by omega)
      rw [← hwx]
      by_cases hwx' : w = x
      · rw [if_pos (this.mpr hwx'), if_pos hwx']
      · rw [if_neg (fun h => hwx' (this.mp h)), if_neg hwx']
    have hc3 : P2.cost inp B s1 + (eqW (g + 40)).cost inp B s2 ≤ (12 * L + 9) * κ := by
      have c2 : P2.cost inp B s1 ≤ 5 * κ := by
        simp (disch := omega) only [hP2, cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp,
          exec_seqs_cons, exec_lit, HS.setR_regs, upd_ne, EnumCfg.vis]
        rw [r1 _ (by omega), f25]
        have := kappa_bits_le B (a := cfg.a0) (M := Mb) (by omega)
        have := kappa_bits_le B (a := XA) (M := Mb) (by omega)
        have := kappa_bits_le B (a := L) (M := Mb) (by omega)
        omega
      rw [v44, ← hκ] at q6
      have : (12 * L + 9) * κ = 5 * κ + (12 * L + 4) * κ := by ring
      omega
    have hcI : (enBody q cfg g XA DG).cost inp B st = P1.cost inp B st + (kappa B (RAM.bits (s1.regs (g + 38))) +
        (P2.cost inp B s1 + ((eqW (g + 40)).cost inp B s2 +
          (Cmd.ifz (g + 45) (enApp q cfg g DG) .skip).cost inp B s3))) := by
      show P1.cost inp B st + (Cmd.ifz (g + 38) (enInner q cfg g XA DG) .skip).cost inp B s1 = _
      rw [cost_ifz, if_pos (by rw [d1]; exact hd)]; rfl
    have hxI : (enBody q cfg g XA DG).exec inp st =
        (Cmd.ifz (g + 45) (enApp q cfg g DG) .skip).exec inp s3 := by
      show (Cmd.ifz (g + 38) (enInner q cfg g XA DG) .skip).exec inp s1 = _
      rw [exec_ifz, if_pos (by rw [d1]; exact hd)]; rfl
    have hcur3 : s3.cur = st.cur := by rw [q4]; simp [hs2, hP2, hcur1]
    have hout3 : s3.out = st.out := by rw [q5]; simp [hs2, hP2, hout1]
    have r3' : ∀ r, (r < g + 38 ∨ g + 51 ≤ r) → s3.regs r = st.regs r := by
      intro r hr; rw [r3 r (by omega), r2 r (by omega), r1 r (by omega)]
    by_cases hwx' : w = x
    · have hfl : listF x l w = l := by unfold listF; rw [if_neg (fun h => h.2 hwx')]
      have hex : (enBody q cfg g XA DG).exec inp st = s3 := by
        rw [hxI, exec_ifz, if_neg (by rw [hflag, if_pos hwx']; omega)]; rfl
      rw [hex, hfl]
      refine ⟨EnInv.keep hI
        (fun r hr => r3' r (by omega)) m3 hcur3 hout3,
        hbf s3 (fun r hr => r3' r (by omega)) (fun y i _ => by simp [HS.arr, m3]), ?_⟩
      rw [hcI, d1, hd, cost_ifz, hflag, if_pos hwx', if_neg (by omega)]
      simp only [cost_skip]
      have : (19 * L + 7 * K + 40) * κ = 3 * κ + κ + (12 * L + 9) * κ + κ +
        (7 * L + 7 * K + 26) * κ := by ring
      have := kappa_bits_le B (a := 1) (M := Mb) (by omega)
      omega
    · have hfl : listF x l w = l ++ [w] := by unfold listF; rw [if_pos ⟨hwx, hwx'⟩]
      have hex : (enBody q cfg g XA DG).exec inp st = (enApp q cfg g DG).exec inp s3 := by
        rw [hxI, exec_ifz, if_pos (by rw [hflag, if_neg hwx'])]
      have e3_25 : s3.regs (g + 25) = L := by rw [r3' _ (by omega), f25]
      have e3_24 : s3.regs (g + 24) = Q := by rw [r3' _ (by omega), f24]
      have e3_18 : s3.regs (g + 18) = K := by rw [r3' _ (by omega), f18]
      have e3_26 : s3.regs (g + 26) = l.length := by rw [r3' _ (by omega), i26]
      set P4 := seqs [lit (g + 40) cfg.vis, lit (g + 41) 0, cp (g + 42) (g + 25), lit (g + 43) q]
        with hP4
      set s4 := P4.exec inp s3 with hs4
      have r4 : ∀ r, (r < g + 40 ∨ g + 44 ≤ r) → s4.regs r = s3.regs r := by
        intro r hr; simp (disch := omega) [hs4, hP4, upd_ne]
      have m4 : s4.mem = st.mem := by simp [hs4, hP4, m3]
      have w40 : s4.regs (g + 40) = cfg.a0 := by simp [hs4, hP4]
      have w41 : s4.regs (g + 41) = 0 := by simp (disch := omega) [hs4, hP4, upd_ne]
      have w42 : s4.regs (g + 42) = L := by simp (disch := omega) [hs4, hP4, upd_ne, e3_25]
      have w43 : s4.regs (g + 43) = q := by simp (disch := omega) [hs4, hP4, upd_ne]
      have c4 : P4.cost inp B s3 ≤ 4 * κ := by
        simp (disch := omega) only [hP4, cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp,
          exec_seqs_cons, exec_lit, HS.setR_regs, upd_ne, EnumCfg.vis, e3_25]
        have := kappa_bits_le B (a := cfg.a0) (M := Mb) (by omega)
        have := kappa_bits_le B (a := q) (M := Mb) (by omega)
        have := kappa_bits_le B (a := L) (M := Mb) (by omega)
        omega
      have hw4 : WordAt s4 cfg.a0 0 w := hvis.congr (fun i _ => by simp [HS.arr, m4])
      have hval := valueW_word inp (g + 40) s4 w (by rw [w40, w41]; exact hw4) (by rw [w42, hwx])
        w43
      have hvw : value w ≤ q ^ L := by rw [← hwx]; exact value_le w
      obtain ⟨d1', d2, d3, d4, d5, d6⟩ := valueW_spec inp B (g + 40) s4 Mb
        (fun i hi => by rw [w40, w41, w43]; rw [w42] at hi; exact hw4.lt i (by omega))
        (by rw [w40, w41, w42, w43]; omega)
      rw [w42, ← hκ] at d6
      set s5 := (valueW (g + 40)).exec inp s4 with hs5
      have low5 : ∀ r, (r < g + 40 ∨ g + 51 ≤ r) → s5.regs r = s3.regs r := fun r h => by
        rw [d2 r (by omega), r4 r (by omega)]
      set P6 := seqs [cp (g + 40) (g + 44), cp (g + 41) (g + 24), cp (g + 42) (g + 18),
        lit (g + 43) DG, lit (g + 34) 1, ar .add (g + 34) (g + 26) (g + 34),
        ar .mul (g + 44) (g + 34) (g + 18)] with hP6
      set s6 := P6.exec inp s5 with hs6
      have r6 : ∀ r, (r ≠ g + 34 ∧ (r < g + 40 ∨ g + 45 ≤ r)) → s6.regs r = s5.regs r := by
        intro r hr; simp (disch := omega) [hs6, hP6, upd_ne]
      have m6 : s6.mem = st.mem := by simp [hs6, hP6, d3, m4]
      have J5 : s5.regs (g + 26) = l.length := by rw [low5 _ (by omega), e3_26]
      have K5 : s5.regs (g + 18) = K := by rw [low5 _ (by omega), e3_18]
      have Q5 : s5.regs (g + 24) = Q := by rw [low5 _ (by omega), e3_24]
      have x40 : s6.regs (g + 40) = value w := by
        simp (disch := omega) [hs6, hP6, upd_ne]; exact hval
      have x41 : s6.regs (g + 41) = Q := by simp (disch := omega) [hs6, hP6, upd_ne, Q5]
      have x42 : s6.regs (g + 42) = K := by simp (disch := omega) [hs6, hP6, upd_ne, K5]
      have x43 : s6.regs (g + 43) = DG := by simp (disch := omega) [hs6, hP6, upd_ne]
      have x44 : s6.regs (g + 44) = (l.length + 1) * K := by
        simp (disch := omega) [hs6, hP6, upd_ne, J5, K5]
      have hJK : (l.length + 1) * K ≤ (V + 1) * K := Nat.mul_le_mul_right _ (by omega)
      have c6 : P6.cost inp B s5 ≤ 7 * κ := by
        simp (disch := omega) only [hP6, cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp, cost_ar,
          exec_seqs_cons, exec_lit, exec_cp, exec_ar, arith_add, HS.setR_regs, upd_ne, upd_eq,
          J5, K5, Q5]
        rw [hval]
        have := kappa_bits_le B (a := value w) (M := Mb) (by omega)
        have := kappa_bits_le B (a := Q) (M := Mb) (by omega)
        have := kappa_bits_le B (a := K) (M := Mb) (by
          have : K ≤ (V + 1) * K := Nat.le_mul_of_pos_left _ (by omega)
          omega)
        have := kappa_bits_le B (a := DG) (M := Mb) (by omega)
        have := kappa_bits_le B (a := l.length + 1) (M := Mb) (by omega)
        have := kappa_bits_le B (a := l.length + 1 + K) (M := Mb) (by
          have : K ≤ (V + 1) * K := Nat.le_mul_of_pos_left _ (by omega)
          omega)
        rw [← hκ] at *
        omega
      have hJK' : (l.length + 1) * K + K ≤ (V + 1) * K := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
      obtain ⟨f1, f2, f3, f4, f5, f6⟩ := digitsW_spec inp B (g + 40) s6 Mb
        (by rw [x40, x41, x42, x43, x44]; omega)
      simp only [x40, x41, x42, x43, x44] at f1 f2
      rw [x42, ← hκ] at f6
      set s7 := (digitsW (g + 40)).exec inp s6 with hs7
      set P8 := seqs [lit (g + 34) 1, ar .add (g + 26) (g + 26) (g + 34)] with hP8
      set s8 := P8.exec inp s7 with hs8
      have J7 : s7.regs (g + 26) = l.length := by
        rw [f3 _ (by omega), r6 _ (by omega), J5]
      have r8 : ∀ r, (r ≠ g + 26 ∧ r ≠ g + 34) → s8.regs r = s7.regs r := by
        intro r hr; simp (disch := omega) [hs8, hP8, upd_ne]
      have J8 : s8.regs (g + 26) = l.length + 1 := by simp (disch := omega) [hs8, hP8, upd_ne, J7]
      have c8 : P8.cost inp B s7 ≤ 2 * κ := by
        simp (disch := omega) only [hP8, cost_seqs_cons, cost_seqs_nil, cost_lit, cost_ar,
          exec_seqs_cons, exec_lit, HS.setR_regs, upd_ne, upd_eq, J7]
        have := kappa_bits_le B (a := l.length + 1) (M := Mb) (by omega)
        omega
      have hex8 : (enApp q cfg g DG).exec inp s3 = s8 := rfl
      have hfr : ∀ r, (r < g + 26 ∨ g + 51 ≤ r) → s8.regs r = st.regs r := by
        intro r hr
        rw [r8 r (by omega), f3 r (by omega), r6 r (by omega), low5 r (by omega), r3' r (by omega)]
      have hmem8 : ∀ y i, ¬ (y = DG ∧ (l.length + 1) * K ≤ i ∧ i < (l.length + 1) * K + K) →
          s8.arr y i = st.arr y i := by
        intro y i h
        show s7.arr y i = _
        rw [f2 y i h]; simp [HS.arr, m6]
      have hcur8 : s8.cur = st.cur := by
        show s7.cur = _; rw [f4]; simp [hs6, hP6, d4, hs4, hP4, hcur3]
      have hout8 : s8.out = st.out := by
        show s7.out = _; rw [f5]; simp [hs6, hP6, d5, hs4, hP4, hout3]
      rw [hex, hex8, hfl]
      refine ⟨EnInv.app hI hfr J8 hmem8 (fun i hi => ?_) hwx hcur8 hout8,
        hbf s8 (fun r hr => hfr r (by omega)) (fun y i hy => hmem8 y i (fun h => hy h.1)), ?_⟩
      · show s7.arr DG ((l.length + 1) * K + i) = _
        exact f1 i hi
      · have hcA : (enApp q cfg g DG).cost inp B s3 = P4.cost inp B s3 +
            ((valueW (g + 40)).cost inp B s4 + (P6.cost inp B s5 + ((digitsW (g + 40)).cost inp B s6 +
            (P8.cost inp B s7 + 0)))) := rfl
        rw [hcI, d1, hd, cost_ifz, hflag, if_neg hwx', if_pos rfl, hcA]
        have := kappa_bits_le B (a := 0) (M := Mb) (by omega)
        have : (19 * L + 7 * K + 40) * κ = 3 * κ + κ + (12 * L + 9) * κ + κ + 4 * κ +
          (7 * L + 4) * κ + 7 * κ + (7 * K + 4) * κ + 2 * κ + 5 * κ := by ring
        omega
  · have hex : (enBody q cfg g XA DG).exec inp st = s1 := by
      show (Cmd.ifz (g + 38) _ .skip).exec inp s1 = _
      rw [exec_ifz, if_neg (by rw [d1]; exact hd)]; rfl
    have hfl : listF x l w = l := by unfold listF; rw [if_neg (fun h => hd (by omega))]
    rw [hex, hfl]
    refine ⟨EnInv.keep hI
        (fun r hr => r1 r (by omega)) m1 hcur1 hout1,
      hbf s1 (fun r hr => r1 r (by omega)) (fun y i _ => by simp [HS.arr, m1]), ?_⟩
    have hc : (enBody q cfg g XA DG).cost inp B st =
        P1.cost inp B st + (kappa B (RAM.bits (s1.regs (g + 38))) + 0) := by
      show _ + (Cmd.ifz (g + 38) _ .skip).cost inp B s1 = _
      rw [cost_ifz, if_neg (by rw [d1]; exact hd)]; rfl
    rw [hc, d1]
    have := kappa_bits_le B (a := w.length - L + (L - w.length)) (M := Mb) (by omega)
    have : (19 * L + 7 * K + 40) * κ = 4 * κ + (19 * L + 7 * K + 36) * κ := by ring
    omega


end Enum

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.enBody_spec_oai := @EditMulticoloring.Dev.Ram.enBody_spec_oai
