-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.colorsAll_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:36:33.751426+00:00
-- url     : https://prove2.me/submissions/b65a3e68-fc8a-40bc-9591-bcf939da4356

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_CAInv_stable
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_congr
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_lt
import Theorems.Thm_EditMulticoloring_Dev_Ram_cBody_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_colorOf_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_copyW_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_copyW_word
import Theorems.Thm_EditMulticoloring_Dev_Ram_enumScripts_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_foldl_listF
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le
import Theorems.Thm_EditMulticoloring_Dev_Ram_length_le_of_mem_visits
import Theorems.Thm_EditMulticoloring_Dev_Ram_localColor_lt
import Theorems.Thm_EditMulticoloring_Dev_Ram_upd_eq
import Theorems.Thm_EditMulticoloring_Dev_Ram_upd_ne
import Theorems.Thm_EditMulticoloring_Dev_Ram_visits_le_visBound

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
/-- **`colorsAll`**: input `x` in `cfg1.buf (2t)` with `|x|` in `cfg1.lenR (2t)`, registers
`g = p`, `g+3 = W`, `g+18 = K`, `g+24 = Q`.  Output: `g+51 = localColor t P p x`,
`g+52 = J = (nbrList t x).length` and `CLA[m] = localColor t P p (nbrList t x)[m]` for `m < J`
(for every `P` with `P.Q = Q`, `P.K = K`). -/
theorem colorsAll_spec_oai {q : ℕ} (t : ℕ) (cfg1 cfg2 : EnumCfg) (g X2 XA DG CLA : ℕ) (x : Word q)
    (st : HS) (p W Q K Vb Ms Mb : ℕ) (hpl : CAPlace t cfg1 cfg2 g X2 XA DG CLA)
    (h0 : st.regs g = p) (h3 : st.regs (g + 3) = W) (h18 : st.regs (g + 18) = K)
    (h24 : st.regs (g + 24) = Q)
    (hlen : st.regs (cfg1.lenR (2 * t)) = x.length) (hx : WordAt st (cfg1.buf (2 * t)) 0 x)
    (hp : p ≠ 0) (hpW : p < 2 ^ W) (hQ0 : 0 < Q) (hQW : Q ≤ 2 ^ W)
    (hVb : visBound q t x.length ≤ Vb)
    (hMs : p * 2 ^ (2 * W) + 6 * 2 ^ (2 * W) + DG + (Vb + 2) * K + Vb ≤ Ms)
    (hMb : q ^ x.length + 2 * q + 2 * cfg1.a0 + 2 * t + X2 + XA + DG + CLA + 2 * x.length + Q +
      (Vb + 1) * K + Vb + 2 * 2 ^ (2 * W) + 2 ≤ Mb) :
    let st' := (colorsAll q t cfg1 cfg2 g X2 XA DG CLA).exec inp st
    (∀ P : Parameters, P.Q = Q → P.K = K → st'.regs (g + 51) = localColor t P p x) ∧
    st'.regs (g + 52) = (nbrList t x).length ∧
    (∀ m (hm : m < (nbrList t x).length), ∀ P : Parameters, P.Q = Q → P.K = K →
      st'.arr CLA m = localColor t P p (nbrList t x)[m]) ∧
    (∀ r, (r < g + 1 ∨ r = g + 3 ∨ r = g + 18 ∨ r = g + 24 ∨ cfg1.r0 ≤ r) →
      ¬ cfg1.ownsReg (2 * t) r → st'.regs r = st.regs r) ∧
    (∀ y i, y ≠ X2 → y ≠ XA → y ≠ DG → y ≠ CLA → ¬ cfg2.ownsArr (2 * t) y →
      ¬ cfg1.ownsArr (2 * t) y → st'.arr y i = st.arr y i) ∧
    st'.regs (cfg1.lenR (2 * t)) = x.length ∧ WordAt st' (cfg1.buf (2 * t)) 0 x ∧
    st'.cur = st.cur ∧ st'.out = st.out ∧
    (colorsAll q t cfg1 cfg2 g X2 XA DG CLA).cost inp B st ≤
      (Vb + 1) * (colorOfCost B q t x.length K Q W Vb Ms Mb cfg2 +
        (19 * x.length + 40) * kappa B (RAM.bits Mb) + cfg1.enumE B q x.length (2 * t)) := by
  intro st'
  have hpl' := hpl
  obtain ⟨r2, r12, a12, hX2, hXA, hDG, hCL, d1, d2, d3, d4, d5, d6⟩ := hpl'
  set L := x.length with hL
  have hbuf1 : cfg1.buf (2 * t) = cfg1.a0 + 1 + 2 * t := rfl
  have hbuf2 : cfg2.buf (2 * t) = cfg2.a0 + 1 + 2 * t := rfl
  have hlen1 : cfg1.lenR (2 * t) = cfg1.r0 + (18 + 3 * (2 * t)) := rfl
  have hlen2 : cfg2.lenR (2 * t) = cfg2.r0 + (18 + 3 * (2 * t)) := rfl
  have nR2 : ∀ r, r < cfg2.r0 → ¬ cfg2.ownsReg (2 * t) r := fun r hr h => by
    simp only [EnumCfg.ownsReg] at h; omega
  have nR2' : ∀ r, cfg1.r0 ≤ r → ¬ cfg2.ownsReg (2 * t) r := fun r hr h => by
    simp only [EnumCfg.ownsReg] at h; omega
  have nA2 : ∀ y, y < cfg2.a0 → ¬ cfg2.ownsArr (2 * t) y := fun y hy h => by
    simp only [EnumCfg.ownsArr] at h; omega
  have nA2' : ∀ y, cfg1.a0 ≤ y → ¬ cfg2.ownsArr (2 * t) y := fun y hy h => by
    simp only [EnumCfg.ownsArr] at h; omega
  have hVx : (visits (2 * t) x).length ≤ Vb := (visits_le_visBound t x).trans hVb
  -- phase 0
  set P0 := seqs [lit (g + 54) (cfg1.buf (2 * t)), lit (g + 55) 0, lit (g + 56) X2, lit (g + 57) 0,
      cp (g + 58) (cfg1.lenR (2 * t)), cp (g + 53) (cfg1.lenR (2 * t))] with hP0
  set s0 := P0.exec inp st with hs0
  have r0 : ∀ r, (r < g + 53 ∨ g + 59 ≤ r) → s0.regs r = st.regs r := by
    intro r hr; simp (disch := omega) [hs0, hP0, upd_ne]
  have m0 : s0.mem = st.mem := by simp [hs0, hP0]
  have v54 : s0.regs (g + 54) = cfg1.buf (2 * t) := by simp (disch := omega) [hs0, hP0, upd_ne]
  have v55 : s0.regs (g + 55) = 0 := by simp (disch := omega) [hs0, hP0, upd_ne]
  have v56 : s0.regs (g + 56) = X2 := by simp (disch := omega) [hs0, hP0, upd_ne]
  have v57 : s0.regs (g + 57) = 0 := by simp (disch := omega) [hs0, hP0, upd_ne]
  have v58 : s0.regs (g + 58) = L := by
    simp (disch := omega) [hs0, hP0, upd_ne]; rw [hlen1] at hlen; exact hlen
  have v53 : s0.regs (g + 53) = L := by
    simp (disch := omega) [hs0, hP0, upd_ne]; rw [hlen1] at hlen; exact hlen
  have c0 : P0.cost inp B st ≤ 6 * kappa B (RAM.bits Mb) := by
    rw [hlen1] at hlen
    simp (disch := omega) only [hP0, cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp,
      exec_seqs_cons, exec_lit, exec_cp, HS.setR_regs, upd_ne, EnumCfg.lenR, EnumCfg.buf, hlen]
    have := kappa_bits_le B (a := cfg1.a0 + 1 + 2 * t) (M := Mb) (by omega)
    have := kappa_bits_le B (a := 0) (M := Mb) (by omega)
    have := kappa_bits_le B (a := X2) (M := Mb) (by omega)
    have := kappa_bits_le B (a := L) (M := Mb) (by omega)
    omega
  have hnd : [g + 54, g + 55, g + 56, g + 57, g + 58, g + 59, g + 60, g + 61, g + 62].Nodup := by simp
  have hx0 : WordAt s0 (cfg1.buf (2 * t)) 0 x := hx.congr (fun i _ => by simp [HS.arr, m0])
  -- copy 1: x → X2
  have hSD1 : s0.regs (g + 54) ≠ s0.regs (g + 56) := by rw [v54, v56, hbuf1]; omega
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := copyW_spec inp B (g + 54) (g + 55) (g + 56) (g + 57) (g + 58)
    (g + 59) (g + 60) (g + 61) (g + 62) s0 hnd hSD1 q Mb
    (fun i hi => by rw [v54, v55]; rw [v58] at hi; exact (hx0.lt i (by omega)).le)
    (by rw [v54, v55, v56, v57, v58, hbuf1]; omega)
  have hw1 := copyW_word inp (g + 54) (g + 55) (g + 56) (g + 57) (g + 58) (g + 59) (g + 60)
    (g + 61) (g + 62) s0 x hnd hSD1 (by rw [v54, v55]; exact hx0) v58
  rw [v56, v57] at hw1 b2
  rw [v58] at b6
  set s1 := (copyW (g + 54) (g + 55) (g + 56) (g + 57) (g + 58) (g + 59) (g + 60) (g + 61)
    (g + 62)).exec inp s0 with hs1
  have r1 : ∀ r, (r < g + 59 ∨ g + 63 ≤ r) → s1.regs r = s0.regs r := fun r h =>
    b3 r (by omega) (by omega) (by omega) (by omega)
  -- phase 2
  set P2 := seqs [lit (g + 56) (cfg2.buf (2 * t)), cp (cfg2.lenR (2 * t)) (g + 53)] with hP2
  set s2 := P2.exec inp s1 with hs2
  have r2' : ∀ r, r ≠ g + 56 → r ≠ cfg2.lenR (2 * t) → s2.regs r = s1.regs r := by
    intro r h1 h2
    simp only [hs2, hP2, exec_seqs_cons, exec_seqs_nil, exec_lit, exec_cp, HS.setR_regs]
    rw [Function.update_of_ne h2, Function.update_of_ne h1]
  have m2 : s2.mem = s1.mem := by simp [hs2, hP2]
  have u53 : s1.regs (g + 53) = L := by rw [r1 _ (by omega), v53]
  have w56 : s2.regs (g + 56) = cfg2.buf (2 * t) := by
    simp only [hs2, hP2, exec_seqs_cons, exec_seqs_nil, exec_lit, exec_cp, HS.setR_regs]
    rw [Function.update_of_ne (by rw [hlen2]; omega), Function.update_self]
  have wlen : s2.regs (cfg2.lenR (2 * t)) = L := by
    simp only [hs2, hP2, exec_seqs_cons, exec_seqs_nil, exec_lit, exec_cp, HS.setR_regs,
      Function.update_self]
    rw [Function.update_of_ne (by omega), u53]
  have c2 : P2.cost inp B s1 ≤ 2 * kappa B (RAM.bits Mb) := by
    simp only [hP2, cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp, exec_seqs_cons, exec_lit,
      HS.setR_regs]
    rw [Function.update_of_ne (by omega), u53]
    have := kappa_bits_le B (a := cfg2.buf (2 * t)) (M := Mb) (by omega)
    have := kappa_bits_le B (a := L) (M := Mb) (by omega)
    omega
  have w54 : s2.regs (g + 54) = cfg1.buf (2 * t) := by
    rw [r2' _ (by omega) (by omega), r1 _ (by omega), v54]
  have w55 : s2.regs (g + 55) = 0 := by rw [r2' _ (by omega) (by omega), r1 _ (by omega), v55]
  have w57 : s2.regs (g + 57) = 0 := by rw [r2' _ (by omega) (by omega), r1 _ (by omega), v57]
  have w58 : s2.regs (g + 58) = L := by rw [r2' _ (by omega) (by omega), r1 _ (by omega), v58]
  have hx2 : WordAt s2 (cfg1.buf (2 * t)) 0 x := hx0.congr (fun i _ => by
    have e : s2.arr (cfg1.buf (2 * t)) (0 + i) = s1.arr (cfg1.buf (2 * t)) (0 + i) := by
      simp only [HS.arr, m2]
    rw [e, b2 _ _ (by rw [hbuf1]; omega)])
  -- copy 2: x → cfg2.buf
  have hSD2 : s2.regs (g + 54) ≠ s2.regs (g + 56) := by rw [w54, w56, hbuf1, hbuf2]; omega
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := copyW_spec inp B (g + 54) (g + 55) (g + 56) (g + 57) (g + 58)
    (g + 59) (g + 60) (g + 61) (g + 62) s2 hnd hSD2 q Mb
    (fun i hi => by rw [w54, w55]; rw [w58] at hi; exact (hx2.lt i (by omega)).le)
    (by rw [w54, w55, w56, w57, w58, hbuf1, hbuf2]; omega)
  have hw2 := copyW_word inp (g + 54) (g + 55) (g + 56) (g + 57) (g + 58) (g + 59) (g + 60)
    (g + 61) (g + 62) s2 x hnd hSD2 (by rw [w54, w55]; exact hx2) w58
  rw [w56, w57] at hw2 f2
  rw [w58] at f6
  set s3 := (copyW (g + 54) (g + 55) (g + 56) (g + 57) (g + 58) (g + 59) (g + 60) (g + 61)
    (g + 62)).exec inp s2 with hs3
  have r3 : ∀ r, (r < g + 59 ∨ g + 63 ≤ r) → s3.regs r = s2.regs r := fun r h =>
    f3 r (by omega) (by omega) (by omega) (by omega)
  have low3 : ∀ r, (r < g + 53 ∨ g + 63 ≤ r) → r ≠ cfg2.lenR (2 * t) → s3.regs r = st.regs r := by
    intro r h1 h2
    rw [r3 r (by omega), r2' r (by omega) h2, r1 r (by omega), r0 r (by omega)]
  -- colorOf on x
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := colorOf_spec inp B t cfg2 g XA DG x s3 p W Q K Vb Ms Mb
    (by omega) hXA hDG d4 (by rw [low3 _ (by omega) (by omega), h0])
    (by rw [low3 _ (by omega) (by omega), h3]) (by rw [low3 _ (by omega) (by omega), h18])
    (by rw [low3 _ (by omega) (by omega), h24]) (by rw [r3 _ (by omega), wlen]) hw2
    hp hpW hQ0 hQW hVx hMs (by rw [← hL]; omega)
  set s4 := (colorOf q t cfg2 g XA DG).exec inp s3 with hs4
  set P5 := seqs [cp (g + 51) (g + 36), lit (g + 52) 0] with hP5
  set s5 := P5.exec inp s4 with hs5
  have r5 : ∀ r, (r ≠ g + 51 ∧ r ≠ g + 52) → s5.regs r = s4.regs r := by
    intro r hr; simp (disch := omega) [hs5, hP5, upd_ne]
  have m5 : s5.mem = s4.mem := by simp [hs5, hP5]
  have c5 : P5.cost inp B s4 ≤ 2 * kappa B (RAM.bits Mb) := by
    clear_value s5 s4 s3 s2 s1 s0
    simp only [hP5, cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp]
    have hcb : s4.regs (g + 36) < Q * Q + 2 ^ W := by
      rw [o1 (parQK Q K) rfl rfl]; exact localColor_lt t (parQK Q K) p W x hp hpW hQ0 hQW
    have hQQ : Q * Q ≤ 2 ^ (2 * W) := by
      calc Q * Q ≤ 2 ^ W * 2 ^ W := Nat.mul_le_mul hQW hQW
        _ = 2 ^ (2 * W) := by rw [← pow_add]; congr 1; omega
    have hWW : 2 ^ W ≤ 2 ^ (2 * W) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := kappa_bits_le B (a := s4.regs (g + 36)) (M := Mb) (by omega)
    have := kappa_bits_le B (a := 0) (M := Mb) (by omega)
    omega
  -- the state at the start of the enumeration
  have k5 : ∀ r, (r < g + 1 ∨ r = g + 3 ∨ r = g + 18 ∨ r = g + 24 ∨ cfg1.r0 ≤ r) →
      s5.regs r = st.regs r := by
    intro r hr
    rw [r5 r (by omega), o2 r (by omega) (by
      rcases hr with hr | hr | hr | hr | hr
      all_goals first | exact nR2 r (by omega) | exact nR2' r hr),
      low3 r (by omega) (by rw [hlen2]; omega)]
  have y51 : ∀ P : Parameters, P.Q = Q → P.K = K → s5.regs (g + 51) = localColor t P p x := by
    intro P hP hK
    simp (disch := omega) only [hs5, hP5, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_lit,
      HS.setR_regs, upd_ne, upd_eq]
    exact o1 P hP hK
  have y52 : s5.regs (g + 52) = 0 := by simp (disch := omega) [hs5, hP5, upd_ne]
  have y53 : s5.regs (g + 53) = L := by
    rw [r5 _ (by omega), o2 _ (by omega) (nR2 _ (by omega)), r3 _ (by omega),
      r2' _ (by omega) (by rw [hlen2]; omega), u53]
  have arr5 : ∀ y i, y ≠ XA → y ≠ DG → ¬ cfg2.ownsArr (2 * t) y → s5.arr y i = s2.arr y i := by
    intro y i h1 h2 h3
    rw [show s5.arr y i = s4.arr y i by simp [HS.arr, m5], o3 y i h1 h2 h3]
    show s3.arr y i = _
    rw [f2 y i (by rintro ⟨rfl, -⟩; exact h3 ⟨by omega, by omega⟩)]
  have hX5 : WordAt s5 X2 0 x := hw1.congr (fun i _ => by
    rw [arr5 _ _ d1 d2 (nA2 _ hX2)]; simp [HS.arr, m2])
  have hlen5 : s5.regs (cfg1.lenR (2 * t)) = x.length := by
    rw [k5 _ (Or.inr (Or.inr (Or.inr (Or.inr (by rw [hlen1]; omega))))), hlen]
  have hx5 : WordAt s5 (cfg1.buf (2 * t)) 0 x := hx2.congr (fun i _ => by
    rw [arr5 _ _ (by rw [hbuf1]; omega) (by rw [hbuf1]; omega) (nA2' _ (by rw [hbuf1]; omega))])
  set cb := colorOfCost B q t x.length K Q W Vb Ms Mb cfg2 + (19 * x.length + 40) * kappa B (RAM.bits Mb)
    with hcb
  have E := enumScripts_spec (2 * t) cfg1 (cBody q t cfg1 cfg2 g X2 XA DG CLA) inp B
    (CAInv t cfg1 cfg2 g XA DG CLA p Q K x s5) (listF x) cb x []
    (fun a st st' h hA => CAInv.stable (by omega) (by omega) h hA)
    (by
      intro l st2 w j hj hw hl hI hVL hvis
      have hwmem : w ∈ visits (2 * t) x := hw ▸ List.getElem_mem hj
      have hwl := length_le_of_mem_visits (2 * t) x hwmem
      have hlj : l.length ≤ Vb := by
        rw [hl, foldl_listF]
        have := List.length_filter_le (fun w => decide (w.length = x.length ∧ w ≠ x))
          ((visits (2 * t) x).take j)
        simp only [List.nil_append, List.length_take] at this ⊢; omega
      exact cBody_spec inp B t cfg1 cfg2 g X2 XA DG CLA x s5 p W Q K Vb Ms Mb hpl
        (by rw [k5 _ (by omega), h0]) (by rw [k5 _ (by omega), h3]) (by rw [k5 _ (by omega), h18])
        (by rw [k5 _ (by omega), h24]) (by rw [y53]) hX5 hp hpW hQ0 hQW hVb hMs hMb
        l st2 w hI hVL hvis hwl hlj)
    s5 hlen5 hx5
    ⟨by rw [y52]; rfl, by simp, fun m hm => absurd hm (Nat.not_lt_zero _), fun _ _ _ => rfl,
      fun _ _ _ _ _ _ _ => rfl, rfl, rfl⟩
  obtain ⟨E1, E2, E3, E4⟩ := E
  have hfold : (visits (2 * t) x).foldl (listF x) [] = nbrList t x := by rw [foldl_listF]; rfl
  rw [hfold] at E1
  have hex : st' = (enumScripts q (2 * t) cfg1 (cBody q t cfg1 cfg2 g X2 XA DG CLA)).exec inp s5 := rfl
  rw [← hex] at E1 E2 E3
  obtain ⟨F52, -, Frows, Fregs, Farr, Fcur, Fout⟩ := E1
  have nR1 : ∀ r, r < cfg1.r0 → ¬ cfg1.ownsReg (2 * t) r := fun r hr h => by
    simp only [EnumCfg.ownsReg] at h; omega
  refine ⟨fun P hP hK => by rw [Fregs _ (by omega) (nR1 _ (by omega)), y51 P hP hK], F52, Frows,
    fun r hr hn => by rw [Fregs r (by omega) hn, k5 r hr], ?_, E2, E3, ?_, ?_, ?_⟩
  · intro y i a b c d e f
    rw [Farr y i b c d e f, arr5 y i b c e]
    show s1.arr y i = _
    rw [b2 y i (by omega)]; simp [HS.arr, m0]
  · rw [Fcur]
    simp only [hs5, hP5, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_lit, HS.setR_cur]
    rw [o6]; rw [f4]
    simp only [hs2, hP2, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_lit, HS.setR_cur]
    rw [b4]; simp [hs0, hP0]
  · rw [Fout]
    simp only [hs5, hP5, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_lit, HS.setR_out]
    rw [o7]; rw [f5]
    simp only [hs2, hP2, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_lit, HS.setR_out]
    rw [b5]; simp [hs0, hP0]
  · have hc : (colorsAll q t cfg1 cfg2 g X2 XA DG CLA).cost inp B st = P0.cost inp B st +
        ((copyW (g + 54) (g + 55) (g + 56) (g + 57) (g + 58) (g + 59) (g + 60) (g + 61)
          (g + 62)).cost inp B s0 + (P2.cost inp B s1 +
        ((copyW (g + 54) (g + 55) (g + 56) (g + 57) (g + 58) (g + 59) (g + 60) (g + 61)
          (g + 62)).cost inp B s2 + ((colorOf q t cfg2 g XA DG).cost inp B s3 +
        (P5.cost inp B s4 + ((enumScripts q (2 * t) cfg1
          (cBody q t cfg1 cfg2 g X2 XA DG CLA)).cost inp B s5 + 0)))))) := rfl
    rw [hc]
    have o8' : (colorOf q t cfg2 g XA DG).cost inp B s3 ≤
        colorOfCost B q t x.length K Q W Vb Ms Mb cfg2 := o8
    have hV1 : (visits (2 * t) x).length * (cb + cfg1.enumE B q x.length (2 * t)) ≤
        Vb * (cb + cfg1.enumE B q x.length (2 * t)) := Nat.mul_le_mul_right _ hVx
    have e : (Vb + 1) * (cb + cfg1.enumE B q x.length (2 * t)) =
        Vb * (cb + cfg1.enumE B q x.length (2 * t)) + cb + cfg1.enumE B q x.length (2 * t) := by ring
    rw [hcb] at e hV1 E4 ⊢
    rw [e]
    have : (19 * L + 40) * kappa B (RAM.bits Mb) = 6 * kappa B (RAM.bits Mb) +
      (7 * L + 3) * kappa B (RAM.bits Mb) + 2 * kappa B (RAM.bits Mb) +
      (7 * L + 3) * kappa B (RAM.bits Mb) + 2 * kappa B (RAM.bits Mb) + (5 * L + 24) * kappa B (RAM.bits Mb) := by
      ring
    simp only [← hL] at E4 o8' hV1 ⊢
    omega

end Body

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.colorsAll_spec_oai := @EditMulticoloring.Dev.Ram.colorsAll_spec_oai
