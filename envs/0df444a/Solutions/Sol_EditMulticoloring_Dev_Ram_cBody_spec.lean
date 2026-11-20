-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.cBody_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:36:11.325974+00:00
-- url     : https://prove2.me/submissions/bc1c2c57-3eb8-4164-8449-7c233c3c99c2

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_congr
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_lt
import Theorems.Thm_EditMulticoloring_Dev_Ram_colorOf_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_copyW_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_copyW_word
import Theorems.Thm_EditMulticoloring_Dev_Ram_eqW_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_one_le
import Theorems.Thm_EditMulticoloring_Dev_Ram_localColor_lt
import Theorems.Thm_EditMulticoloring_Dev_Ram_upd_eq
import Theorems.Thm_EditMulticoloring_Dev_Ram_upd_ne
import Theorems.Thm_EditMulticoloring_Dev_Ram_visits_le_visBound
import Theorems.Thm_EditMulticoloring_Dev_Ram_words_eq_iff

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

/-! ## The program -/


section Body
variable (inp : ℕ → ℕ) (B : ℕ)

set_option maxHeartbeats 1600000 in
theorem cBody_spec_oai {q : ℕ} (t : ℕ) (cfg1 cfg2 : EnumCfg) (g X2 XA DG CLA : ℕ) (x : Word q) (st0 : HS)
    (p W Q K Vb Ms Mb : ℕ) (hpl : CAPlace t cfg1 cfg2 g X2 XA DG CLA)
    (e0 : st0.regs g = p) (e3 : st0.regs (g + 3) = W) (e18 : st0.regs (g + 18) = K)
    (e24 : st0.regs (g + 24) = Q) (e53 : st0.regs (g + 53) = x.length) (hX0 : WordAt st0 X2 0 x)
    (hp : p ≠ 0) (hpW : p < 2 ^ W) (hQ0 : 0 < Q) (hQW : Q ≤ 2 ^ W)
    (hVb : visBound q t x.length ≤ Vb)
    (hMs : p * 2 ^ (2 * W) + 6 * 2 ^ (2 * W) + DG + (Vb + 2) * K + Vb ≤ Ms)
    (hMb : q ^ x.length + 2 * q + 2 * cfg1.a0 + 2 * t + X2 + XA + DG + CLA + 2 * x.length + Q +
      (Vb + 1) * K + Vb + 2 * 2 ^ (2 * W) + 2 ≤ Mb)
    (l : List (Word q)) (st : HS) (w : Word q) (hI : CAInv t cfg1 cfg2 g XA DG CLA p Q K x st0 l st)
    (hVL : st.regs cfg1.VL = w.length) (hvis : WordAt st cfg1.vis 0 w)
    (hwl : w.length ≤ x.length + 2 * t) (hJ : l.length ≤ Vb) :
    CAInv t cfg1 cfg2 g XA DG CLA p Q K x st0 (listF x l w)
      ((cBody q t cfg1 cfg2 g X2 XA DG CLA).exec inp st) ∧
    cfg1.BodyFrame (2 * t) st ((cBody q t cfg1 cfg2 g X2 XA DG CLA).exec inp st) ∧
    (cBody q t cfg1 cfg2 g X2 XA DG CLA).cost inp B st ≤
      colorOfCost B q t x.length K Q W Vb Ms Mb cfg2 + (19 * x.length + 40) * kappa B (RAM.bits Mb) := by
  obtain ⟨r2, r12, a12, hX2, hXA, hDG, hCL, d1, d2, d3, d4, d5, d6⟩ := hpl
  set L := x.length with hL
  obtain ⟨i52, -, -, i4, i5, -, -⟩ := id hI
  have nR1 : ∀ r, r < cfg1.r0 → ¬ cfg1.ownsReg (2 * t) r := fun r hr h => by
    simp only [EnumCfg.ownsReg] at h; omega
  have nA1 : ∀ y, y < cfg1.a0 → ¬ cfg1.ownsArr (2 * t) y := fun y hy h => by
    simp only [EnumCfg.ownsArr] at h; omega
  have nA2 : ∀ y, y < cfg2.a0 → ¬ cfg2.ownsArr (2 * t) y := fun y hy h => by
    simp only [EnumCfg.ownsArr] at h; omega
  have kp : ∀ r, (r < g + 1 ∨ r = g + 3 ∨ r = g + 18 ∨ r = g + 24 ∨ r = g + 51 ∨ r = g + 53) →
      st.regs r = st0.regs r := fun r h => i4 r (by omega) (nR1 r (by omega))
  have f53 : st.regs (g + 53) = L := by rw [kp _ (by omega), e53]
  have hX : WordAt st X2 0 x := hX0.congr (fun i _ => i5 _ _ d1 d2 d3 (nA2 _ hX2) (nA1 _ (by omega)))
  have hVL' : st.regs cfg1.r0 = w.length := hVL
  have hbf : ∀ sF : HS, (∀ r, cfg1.r0 ≤ r → sF.regs r = st.regs r) →
      (∀ y i, y < cfg1.a0 → sF.arr y i = st.arr y i ∨ True) →
      (∀ y i, cfg1.a0 ≤ y → sF.arr y i = st.arr y i) → cfg1.BodyFrame (2 * t) st sF := by
    intro sF h1 _ h2
    refine ⟨fun r hr _ => h1 r (by simp only [EnumCfg.ownsReg] at hr; omega), fun y i hy _ => h2 y i ?_⟩
    simp only [EnumCfg.ownsArr] at hy; omega
  set P1 := seqs [ar .sub (g + 65) cfg1.VL (g + 53), ar .sub (g + 66) (g + 53) cfg1.VL,
      ar .add (g + 65) (g + 65) (g + 66)] with hP1
  set s1 := P1.exec inp st with hs1
  have r1 : ∀ r, (r < g + 65 ∨ g + 67 ≤ r) → s1.regs r = st.regs r := by
    intro r hr; simp (disch := omega) [hs1, hP1, upd_ne]
  have m1 : s1.mem = st.mem := by simp [hs1, hP1]
  have dd1 : s1.regs (g + 65) = (w.length - L) + (L - w.length) := by
    simp (disch := omega) [hs1, hP1, upd_ne, hVL', f53]
  have c1 : P1.cost inp B st ≤ 3 * kappa B (RAM.bits Mb) := by
    simp (disch := omega) only [hP1, cost_seqs_cons, cost_seqs_nil, exec_seqs_cons, exec_ar,
      cost_ar, HS.setR_regs, upd_ne, upd_eq, hVL', f53, arith_sub, arith_add, EnumCfg.VL]
    have := kappa_bits_le B (a := w.length + L) (M := Mb) (by omega)
    have := kappa_bits_le B (a := L + w.length) (M := Mb) (by omega)
    have := kappa_bits_le B (a := w.length - L + (L - w.length)) (M := Mb) (by omega)
    omega
  have hcur1 : s1.cur = st.cur := by simp [hs1, hP1]
  have hout1 : s1.out = st.out := by simp [hs1, hP1]
  have K0 := kappa_bits_le B (a := 0) (M := Mb) (by omega)
  have K1 := kappa_bits_one_le B Mb
  have hCpos : 0 ≤ colorOfCost B q t L K Q W Vb Ms Mb cfg2 := Nat.zero_le _
  -- the frame-only cases
  have keepCase : ∀ sF : HS, (∀ r, (r < g + 54 ∨ g + 67 ≤ r) → sF.regs r = st.regs r) →
      sF.mem = st.mem → sF.cur = st.cur → sF.out = st.out →
      CAInv t cfg1 cfg2 g XA DG CLA p Q K x st0 l sF ∧ cfg1.BodyFrame (2 * t) st sF := by
    intro sF hR hM hc ho
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI
    have hA : ∀ y i, sF.arr y i = st.arr y i := fun y i => by simp only [HS.arr, hM]
    refine ⟨⟨(hR _ (by omega)).trans h1, h2, fun m hm P hP hK => (hA _ _).trans (h3 m hm P hP hK),
      fun r hr hn => (hR r (by
        rcases hr with hr | hr | hr | hr | hr | hr | hr <;> omega)).trans (h4 r hr hn),
      fun y i a b c d e => (hA _ _).trans (h5 y i a b c d e), hc.trans h6, ho.trans h7⟩,
      hbf sF (fun r hr => hR r (by omega)) (fun _ _ _ => Or.inr trivial) (fun y i _ => hA y i)⟩
  by_cases hd : (w.length - L) + (L - w.length) = 0
  · have hwx : w.length = L := by omega
    set P2 := seqs [lit (g + 54) cfg1.vis, lit (g + 55) 0, lit (g + 56) X2, lit (g + 57) 0,
      cp (g + 58) (g + 53)] with hP2
    set s2 := P2.exec inp s1 with hs2
    have r2 : ∀ r, (r < g + 54 ∨ g + 59 ≤ r) → s2.regs r = s1.regs r := by
      intro r hr; simp (disch := omega) [hs2, hP2, upd_ne]
    have m2 : s2.mem = st.mem := by simp [hs2, hP2, m1]
    have v54 : s2.regs (g + 54) = cfg1.a0 := by simp [hs2, hP2]
    have v55 : s2.regs (g + 55) = 0 := by simp (disch := omega) [hs2, hP2, upd_ne]
    have v56 : s2.regs (g + 56) = X2 := by simp (disch := omega) [hs2, hP2, upd_ne]
    have v57 : s2.regs (g + 57) = 0 := by simp (disch := omega) [hs2, hP2, upd_ne]
    have v58 : s2.regs (g + 58) = L := by
      simp (disch := omega) [hs2, hP2, upd_ne]; rw [r1 _ (by omega), f53]
    have hw2 : WordAt s2 cfg1.a0 0 w := hvis.congr (fun i _ => by simp [HS.arr, m2])
    have hX2' : WordAt s2 X2 0 x := hX.congr (fun i _ => by simp [HS.arr, m2])
    obtain ⟨q1, q2, q3, q4, q5, q6⟩ := eqW_spec inp B (g + 54) s2 q Mb
      (fun i hi => by
        rw [v54, v55, v56, v57]; rw [v58] at hi
        exact ⟨(hw2.lt i (by omega)).le, (hX2'.lt i (by omega)).le⟩)
      (by rw [v54, v55, v56, v57, v58]; omega)
    set s3 := (eqW (g + 54)).exec inp s2 with hs3
    have r3 : ∀ r, (r < g + 59 ∨ g + 65 ≤ r) → s3.regs r = s2.regs r := q2
    have m3 : s3.mem = st.mem := by rw [q3, m2]
    have hflag : s3.regs (g + 59) = if w = x then 1 else 0 := by
      rw [q1, v54, v55, v56, v57, v58]
      have := words_eq_iff s2 cfg1.a0 0 X2 0 w x hw2 hX2' (by omega)
      rw [← hwx]
      by_cases hwx' : w = x
      · rw [if_pos (this.mpr hwx'), if_pos hwx']
      · rw [if_neg (fun h => hwx' (this.mp h)), if_neg hwx']
    have hc3 : P2.cost inp B s1 + (eqW (g + 54)).cost inp B s2 ≤ (12 * L + 9) * kappa B (RAM.bits Mb) := by
      have c2 : P2.cost inp B s1 ≤ 5 * kappa B (RAM.bits Mb) := by
        simp (disch := omega) only [hP2, cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp,
          exec_seqs_cons, exec_lit, HS.setR_regs, upd_ne, EnumCfg.vis]
        rw [r1 _ (by omega), f53]
        have := kappa_bits_le B (a := cfg1.a0) (M := Mb) (by omega)
        have := kappa_bits_le B (a := X2) (M := Mb) (by omega)
        have := kappa_bits_le B (a := L) (M := Mb) (by omega)
        omega
      rw [v58] at q6
      have : (12 * L + 9) * kappa B (RAM.bits Mb) =
        5 * kappa B (RAM.bits Mb) + (12 * L + 4) * kappa B (RAM.bits Mb) := by ring
      omega
    have hcI : (cBody q t cfg1 cfg2 g X2 XA DG CLA).cost inp B st = P1.cost inp B st +
        (kappa B (RAM.bits (s1.regs (g + 65))) + (P2.cost inp B s1 + ((eqW (g + 54)).cost inp B s2 +
          (Cmd.ifz (g + 59) (cApp q t cfg1 cfg2 g XA DG CLA) .skip).cost inp B s3))) := by
      show P1.cost inp B st + (Cmd.ifz (g + 65) (cInner q t cfg1 cfg2 g X2 XA DG CLA) .skip).cost
        inp B s1 = _
      rw [cost_ifz, if_pos (by rw [dd1]; exact hd)]; rfl
    have hxI : (cBody q t cfg1 cfg2 g X2 XA DG CLA).exec inp st =
        (Cmd.ifz (g + 59) (cApp q t cfg1 cfg2 g XA DG CLA) .skip).exec inp s3 := by
      show (Cmd.ifz (g + 65) (cInner q t cfg1 cfg2 g X2 XA DG CLA) .skip).exec inp s1 = _
      rw [exec_ifz, if_pos (by rw [dd1]; exact hd)]; rfl
    have hcur3 : s3.cur = st.cur := by rw [q4]; simp [hs2, hP2, hcur1]
    have hout3 : s3.out = st.out := by rw [q5]; simp [hs2, hP2, hout1]
    have r3' : ∀ r, (r < g + 54 ∨ g + 67 ≤ r) → s3.regs r = st.regs r := by
      intro r hr; rw [r3 r (by omega), r2 r (by omega), r1 r (by omega)]
    by_cases hwx' : w = x
    · have hfl : listF x l w = l := by unfold listF; rw [if_neg (fun h => h.2 hwx')]
      have hex : (cBody q t cfg1 cfg2 g X2 XA DG CLA).exec inp st = s3 := by
        rw [hxI, exec_ifz, if_neg (by rw [hflag, if_pos hwx']; omega)]; rfl
      rw [hex, hfl]
      obtain ⟨k1, k2⟩ := keepCase s3 r3' m3 hcur3 hout3
      refine ⟨k1, k2, ?_⟩
      rw [hcI, dd1, hd, cost_ifz, hflag, if_pos hwx', if_neg (by omega)]
      simp only [cost_skip]
      have : (19 * L + 40) * kappa B (RAM.bits Mb) = 3 * kappa B (RAM.bits Mb) +
        kappa B (RAM.bits Mb) + (12 * L + 9) * kappa B (RAM.bits Mb) + kappa B (RAM.bits Mb) +
        (7 * L + 26) * kappa B (RAM.bits Mb) := by ring
      have := kappa_bits_le B (a := 1) (M := Mb) (by omega)
      omega
    · have hfl : listF x l w = l ++ [w] := by unfold listF; rw [if_pos ⟨hwx, hwx'⟩]
      have hex : (cBody q t cfg1 cfg2 g X2 XA DG CLA).exec inp st =
          (cApp q t cfg1 cfg2 g XA DG CLA).exec inp s3 := by
        rw [hxI, exec_ifz, if_pos (by rw [hflag, if_neg hwx'])]
      have g53 : s3.regs (g + 53) = L := by rw [r3' _ (by omega), f53]
      have g52 : s3.regs (g + 52) = l.length := by rw [r3' _ (by omega), i52]
      set P4 := seqs [lit (g + 54) cfg1.vis, lit (g + 55) 0, lit (g + 56) (cfg2.buf (2 * t)),
        lit (g + 57) 0, cp (g + 58) (g + 53)] with hP4
      set s4 := P4.exec inp s3 with hs4
      have r4 : ∀ r, (r < g + 54 ∨ g + 59 ≤ r) → s4.regs r = s3.regs r := by
        intro r hr; simp (disch := omega) [hs4, hP4, upd_ne]
      have m4 : s4.mem = st.mem := by simp [hs4, hP4, m3]
      have w54 : s4.regs (g + 54) = cfg1.a0 := by simp [hs4, hP4]
      have w55 : s4.regs (g + 55) = 0 := by simp (disch := omega) [hs4, hP4, upd_ne]
      have w56 : s4.regs (g + 56) = cfg2.buf (2 * t) := by simp (disch := omega) [hs4, hP4, upd_ne]
      have w57 : s4.regs (g + 57) = 0 := by simp (disch := omega) [hs4, hP4, upd_ne]
      have w58 : s4.regs (g + 58) = L := by simp (disch := omega) [hs4, hP4, upd_ne, g53]
      have hbuf2 : cfg2.buf (2 * t) = cfg2.a0 + 1 + 2 * t := rfl
      have c4 : P4.cost inp B s3 ≤ 5 * kappa B (RAM.bits Mb) := by
        simp (disch := omega) only [hP4, cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp,
          exec_seqs_cons, exec_lit, HS.setR_regs, upd_ne, EnumCfg.vis, g53]
        have := kappa_bits_le B (a := cfg1.a0) (M := Mb) (by omega)
        have := kappa_bits_le B (a := cfg2.buf (2 * t)) (M := Mb) (by omega)
        have := kappa_bits_le B (a := L) (M := Mb) (by omega)
        omega
      have hw4 : WordAt s4 cfg1.a0 0 w := hvis.congr (fun i _ => by simp [HS.arr, m4])
      have hnd : [g + 54, g + 55, g + 56, g + 57, g + 58, g + 59, g + 60, g + 61, g + 62].Nodup := by
        simp
      have hSD : s4.regs (g + 54) ≠ s4.regs (g + 56) := by rw [w54, w56, hbuf2]; omega
      obtain ⟨b1, b2, b3, b4, b5, b6⟩ := copyW_spec inp B (g + 54) (g + 55) (g + 56) (g + 57) (g + 58)
        (g + 59) (g + 60) (g + 61) (g + 62) s4 hnd hSD q Mb
        (fun i hi => by rw [w54, w55]; rw [w58] at hi; exact (hw4.lt i (by omega)).le)
        (by rw [w54, w55, w56, w57, w58, hbuf2]; omega)
      have hw5 := copyW_word inp (g + 54) (g + 55) (g + 56) (g + 57) (g + 58) (g + 59) (g + 60)
        (g + 61) (g + 62) s4 w hnd hSD (by rw [w54, w55]; exact hw4) (by rw [w58, hwx])
      rw [w56, w57] at hw5 b2
      rw [w58] at b6
      set s5 := (copyW (g + 54) (g + 55) (g + 56) (g + 57) (g + 58) (g + 59) (g + 60) (g + 61)
        (g + 62)).exec inp s4 with hs5
      have r5 : ∀ r, (r < g + 59 ∨ g + 63 ≤ r) → s5.regs r = s4.regs r := fun r h =>
        b3 r (by omega) (by omega) (by omega) (by omega)
      set s6 := (cp (cfg2.lenR (2 * t)) (g + 53)).exec inp s5 with hs6
      have hlenR2 : cfg2.lenR (2 * t) = cfg2.r0 + (18 + 3 * (2 * t)) := rfl
      have r6 : ∀ r, r ≠ cfg2.lenR (2 * t) → s6.regs r = s5.regs r := fun r h => by
        rw [hs6, exec_cp, HS.setR_regs, Function.update_of_ne h]
      have chain : ∀ r, (r < g + 54 ∨ g + 67 ≤ r) → r ≠ cfg2.lenR (2 * t) → s6.regs r = st.regs r := by
        intro r h1 h2; rw [r6 r h2, r5 r (by omega), r4 r (by omega), r3' r (by omega)]
      have z0 : s6.regs g = p := by rw [chain _ (by omega) (by omega), kp _ (by omega), e0]
      have z3 : s6.regs (g + 3) = W := by rw [chain _ (by omega) (by omega), kp _ (by omega), e3]
      have z18 : s6.regs (g + 18) = K := by rw [chain _ (by omega) (by omega), kp _ (by omega), e18]
      have z24 : s6.regs (g + 24) = Q := by rw [chain _ (by omega) (by omega), kp _ (by omega), e24]
      have zlen : s6.regs (cfg2.lenR (2 * t)) = w.length := by
        simp [hs6]; rw [r5 _ (by omega), r4 _ (by omega), g53, hwx]
      have zx : WordAt s6 (cfg2.buf (2 * t)) 0 w := hw5.congr (fun i _ => rfl)
      have hVw : (visits (2 * t) w).length ≤ Vb := by
        have := visits_le_visBound t w; rw [hwx] at this; omega
      obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := colorOf_spec inp B t cfg2 g XA DG w s6 p W Q K Vb Ms Mb
        (by omega) hXA hDG d4 z0 z3 z18 z24 zlen zx hp hpW hQ0 hQW hVw hMs (by rw [hwx]; omega)
      rw [hwx] at o8
      set s7 := (colorOf q t cfg2 g XA DG).exec inp s6 with hs7
      have nR2 : ∀ r, r < cfg2.r0 → ¬ cfg2.ownsReg (2 * t) r := fun r hr h => by
        simp only [EnumCfg.ownsReg] at h; omega
      have nR2' : ∀ r, cfg1.r0 ≤ r → ¬ cfg2.ownsReg (2 * t) r := fun r hr h => by
        simp only [EnumCfg.ownsReg] at h; omega
      have y52 : s7.regs (g + 52) = l.length := by
        rw [o2 _ (by omega) (nR2 _ (by omega)), chain _ (by omega) (by omega), i52]
      have hcol : ∀ P : Parameters, P.Q = Q → P.K = K → s7.regs (g + 36) = localColor t P p w := o1
      have hcolb : s7.regs (g + 36) < Q * Q + 2 ^ W := by
        rw [hcol (parQK Q K) rfl rfl]; exact localColor_lt t (parQK Q K) p W w hp hpW hQ0 hQW
      have hQQ : Q * Q ≤ 2 ^ (2 * W) := by
        calc Q * Q ≤ 2 ^ W * 2 ^ W := Nat.mul_le_mul hQW hQW
          _ = 2 ^ (2 * W) := by rw [← pow_add]; congr 1; omega
      have hWW : 2 ^ W ≤ 2 ^ (2 * W) := Nat.pow_le_pow_right (by norm_num) (by omega)
      set P8 := seqs [lit (g + 54) CLA, ast (g + 54) (g + 52) (g + 36), lit (g + 67) 1,
        ar .add (g + 52) (g + 52) (g + 67)] with hP8
      set s8 := P8.exec inp s7 with hs8
      have r8 : ∀ r, (r ≠ g + 54 ∧ r ≠ g + 67 ∧ r ≠ g + 52) → s8.regs r = s7.regs r := by
        intro r hr; simp (disch := omega) [hs8, hP8, upd_ne]
      have y8 : s8.regs (g + 52) = l.length + 1 := by simp (disch := omega) [hs8, hP8, upd_ne, y52]
      have a8 : ∀ y i, s8.arr y i = if y = CLA ∧ i = l.length then s7.regs (g + 36) else s7.arr y i := by
        intro y i
        simp (disch := omega) only [hs8, hP8, exec_seqs_cons, exec_seqs_nil, exec_lit, exec_ast,
          exec_ar, HS.setR_arr, HS.setR_regs, HS.store_arr, upd_ne, upd_eq, y52]
      have c8 : P8.cost inp B s7 ≤ 4 * kappa B (RAM.bits Mb) := by
        simp (disch := omega) only [hP8, cost_seqs_cons, cost_seqs_nil, cost_lit, cost_ast, cost_ar,
          exec_seqs_cons, exec_lit, exec_ast, HS.setR_regs, HS.store_regs, upd_ne, upd_eq, y52]
        clear_value s8 s7 s6 s5 s4 s3 s2 s1
        have := kappa_bits_le B (a := CLA) (M := Mb) (by omega)
        have := kappa_bits_le B (a := CLA + l.length + s7.regs (g + 36)) (M := Mb) (by omega)
        have := kappa_bits_le B (a := l.length + 1) (M := Mb) (by omega)
        omega
      have hcur8 : s8.cur = st.cur := by
        simp only [hs8, hP8, exec_seqs_cons, exec_seqs_nil, exec_lit, exec_ast, exec_ar, HS.setR_cur,
          HS.store_cur]
        rw [o6]; simp only [hs6, exec_cp, HS.setR_cur]; rw [b4]; simp [hs4, hP4, hcur3]
      have hout8 : s8.out = st.out := by
        simp only [hs8, hP8, exec_seqs_cons, exec_seqs_nil, exec_lit, exec_ast, exec_ar, HS.setR_out,
          HS.store_out]
        rw [o7]; simp only [hs6, exec_cp, HS.setR_out]; rw [b5]; simp [hs4, hP4, hout3]
      have arrChain : ∀ y i, y ≠ XA → y ≠ DG → ¬ cfg2.ownsArr (2 * t) y → s7.arr y i = st.arr y i := by
        intro y i h1 h2 h3
        rw [o3 y i h1 h2 h3]
        show s5.arr y i = _
        rw [b2 y i (by
          rintro ⟨rfl, -⟩; exact h3 ⟨by omega, by omega⟩)]
        simp [HS.arr, m4]
      have regChain : ∀ r, (r < g + 1 ∨ r = g + 3 ∨ r = g + 18 ∨ r = g + 24 ∨ r = g + 51 ∨
          r = g + 53 ∨ cfg1.r0 ≤ r) → s8.regs r = st.regs r := by
        intro r hr
        rw [r8 r (by omega), o2 r (by omega) (by
          rcases hr with hr | hr | hr | hr | hr | hr | hr
          all_goals first | exact nR2 r (by omega) | exact nR2' r hr),
          chain r (by omega) (by rw [hlenR2]; omega)]
      have hex8 : (cApp q t cfg1 cfg2 g XA DG CLA).exec inp s3 = s8 := rfl
      rw [hex, hex8, hfl]
      refine ⟨⟨by rw [y8]; simp, fun v hv => ?_, fun m hm P hP hK => ?_,
        fun r hr hn => (regChain r hr).trans (hI.2.2.2.1 r hr hn),
        fun y i a b c d e => ?_, hcur8.trans hI.2.2.2.2.2.1, hout8.trans hI.2.2.2.2.2.2⟩,
        ⟨fun r hr _ => regChain r (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (by simp only [EnumCfg.ownsReg] at hr; omega))))))), fun y i hy _ => ?_⟩, ?_⟩
      · rcases List.mem_append.mp hv with hv | hv
        · exact hI.2.1 v hv
        · simp at hv; rw [hv, hwx]
      · simp only [List.length_append, List.length_singleton] at hm
        rw [a8]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
        · rw [if_neg (by omega), List.getElem_append_left hm,
            arrChain _ _ (Ne.symm d5) (Ne.symm d6) (nA2 _ hCL)]
          exact hI.2.2.1 m hm P hP hK
        · rw [if_pos ⟨rfl, rfl⟩, List.getElem_append_right (by simp)]
          simp only [Nat.sub_self, List.getElem_cons_zero]
          exact hcol P hP hK
      · rw [a8, if_neg (fun h => c h.1), arrChain y i a b d]
        exact hI.2.2.2.2.1 y i a b c d e
      · simp only [EnumCfg.ownsArr] at hy
        rw [a8, if_neg (by omega), arrChain y i (by omega) (by omega) (fun h => by
          simp only [EnumCfg.ownsArr] at h; omega)]
      · have hcA : (cApp q t cfg1 cfg2 g XA DG CLA).cost inp B s3 = P4.cost inp B s3 +
            ((copyW (g + 54) (g + 55) (g + 56) (g + 57) (g + 58) (g + 59) (g + 60) (g + 61)
              (g + 62)).cost inp B s4 + ((cp (cfg2.lenR (2 * t)) (g + 53)).cost inp B s5 +
            ((colorOf q t cfg2 g XA DG).cost inp B s6 + (P8.cost inp B s7 + 0)))) := rfl
        rw [hcI, dd1, hd, cost_ifz, hflag, if_neg hwx', if_pos rfl, hcA, cost_cp,
          r5 _ (by omega), r4 _ (by omega), g53]
        have := kappa_bits_le B (a := L) (M := Mb) (by omega)
        have : (19 * L + 40) * kappa B (RAM.bits Mb) = 3 * kappa B (RAM.bits Mb) +
          kappa B (RAM.bits Mb) + (12 * L + 9) * kappa B (RAM.bits Mb) + kappa B (RAM.bits Mb) +
          5 * kappa B (RAM.bits Mb) + (7 * L + 3) * kappa B (RAM.bits Mb) + kappa B (RAM.bits Mb) +
          4 * kappa B (RAM.bits Mb) + 13 * kappa B (RAM.bits Mb) := by ring
        unfold colorOfCost
        omega
  · have hex : (cBody q t cfg1 cfg2 g X2 XA DG CLA).exec inp st = s1 := by
      show (Cmd.ifz (g + 65) _ .skip).exec inp s1 = _
      rw [exec_ifz, if_neg (by rw [dd1]; exact hd)]; rfl
    have hfl : listF x l w = l := by unfold listF; rw [if_neg (fun h => hd (by omega))]
    rw [hex, hfl]
    obtain ⟨k1, k2⟩ := keepCase s1 (fun r hr => r1 r (by omega)) m1 hcur1 hout1
    refine ⟨k1, k2, ?_⟩
    have hc : (cBody q t cfg1 cfg2 g X2 XA DG CLA).cost inp B st =
        P1.cost inp B st + (kappa B (RAM.bits (s1.regs (g + 65))) + 0) := by
      show _ + (Cmd.ifz (g + 65) _ .skip).cost inp B s1 = _
      rw [cost_ifz, if_neg (by rw [dd1]; exact hd)]; rfl
    rw [hc, dd1]
    have := kappa_bits_le B (a := w.length - L + (L - w.length)) (M := Mb) (by omega)
    have : (19 * L + 40) * kappa B (RAM.bits Mb) = 4 * kappa B (RAM.bits Mb) +
      (19 * L + 36) * kappa B (RAM.bits Mb) := by ring
    omega


end Body

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.cBody_spec_oai := @EditMulticoloring.Dev.Ram.cBody_spec_oai
