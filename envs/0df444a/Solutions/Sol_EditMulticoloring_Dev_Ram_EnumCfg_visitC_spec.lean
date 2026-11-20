-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.EnumCfg.visitC_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:38.673482+00:00
-- url     : https://prove2.me/submissions/bee7fab7-cadf-42f7-9796-24560551d3ed

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_lt
import Theorems.Thm_EditMulticoloring_Dev_Ram_copyW_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le
import Theorems.Thm_EditMulticoloring_Dev_Ram_upd_ne

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

/-! ## Configuration -/

/-! ## Specs of the pieces -/

namespace EnumCfg
variable (c : EnumCfg) (inp : ℕ → ℕ) (B : ℕ)

theorem cpy_run (st : HS) (vS vso vD vdo N V M : ℕ) (h1 : st.regs c.S = vS)
    (h2 : st.regs c.so = vso) (h3 : st.regs c.D = vD) (h4 : st.regs c.dO = vdo)
    (h5 : st.regs c.n = N) (hSD : vS ≠ vD) (hV : ∀ i < N, st.arr vS (vso + i) ≤ V)
    (hM : vS + vso + vD + vdo + N + V ≤ M) :
    (∀ i < N, (c.cpy.exec inp st).arr vD (vdo + i) = st.arr vS (vso + i)) ∧
    (∀ y i, ¬ (y = vD ∧ vdo ≤ i ∧ i < vdo + N) → (c.cpy.exec inp st).arr y i = st.arr y i) ∧
    (∀ r, (r < c.r0 ∨ c.r0 + 16 ≤ r ∨ r = c.S ∨ r = c.so ∨ r = c.D ∨ r = c.dO ∨ r = c.n ∨
        r = c.d ∨ r = c.e ∨ r = c.cnt ∨ r = c.VL) →
      (c.cpy.exec inp st).regs r = st.regs r) ∧
    (c.cpy.exec inp st).cur = st.cur ∧ (c.cpy.exec inp st).out = st.out ∧
    c.cpy.cost inp B st ≤ (7 * N + 3) * kappa B (RAM.bits M) := by
  have hreg : [c.S, c.so, c.D, c.dO, c.n, c.j, c.t, c.u, c.one].Nodup := by
    simp [List.nodup_cons]
  have := copyW_spec inp B c.S c.so c.D c.dO c.n c.j c.t c.u c.one st hreg
    (by rw [h1, h3]; exact hSD) V M (by rw [h1, h2, h5]; exact hV)
    (by rw [h1, h2, h3, h4, h5]; exact hM)
  rw [h1, h2, h3, h4, h5] at this
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := this
  refine ⟨a1, a2, fun r hr => a3 r ?_ ?_ ?_ ?_, a4, a5, a6⟩ <;>
    · simp only [S, so, D, dO, n, j, t, u, one, d, e, cnt, VL] at hr ⊢; omega

theorem visitC_spec_oai {q : ℕ} (k : ℕ) (x : Word q) (st : HS) (hlen : st.regs (c.lenR k) = x.length)
    (hx : WordAt st (c.buf k) 0 x) (M : ℕ) (hM : 2 * c.a0 + 2 * x.length + k + q + 1 ≤ M) :
    ((c.visitC k).exec inp st).regs c.VL = x.length ∧
    WordAt ((c.visitC k).exec inp st) c.vis 0 x ∧
    c.Fr c.VL c.vis st ((c.visitC k).exec inp st) ∧
    (c.visitC k).cost inp B st ≤ (7 * x.length + 10) * kappa B (RAM.bits M) := by
  have hlen' := hlen
  simp only [lenR] at hlen'
  set s1 := (seqs [lit c.S (c.buf k), lit c.so 0, lit c.D c.vis, lit c.dO 0,
    cp c.n (c.lenR k)]).exec inp st with hs1
  have e1 : ∀ r, (r < c.r0 ∨ c.r0 + 16 ≤ r) → s1.regs r = st.regs r := by
    intro r hr; simp (disch := omega) [hs1]
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := c.cpy_run inp B s1 (c.buf k) 0 c.vis 0 x.length q M
    (by simp [hs1]) (by simp [hs1]) (by simp [hs1]) (by simp [hs1])
    (by simp (disch := omega) [hs1, hlen']) (by simp <;> omega) (fun i hi => by
      rw [show s1.arr (c.buf k) (0 + i) = st.arr (c.buf k) (0 + i) from rfl]
      exact (hx.lt i hi).le) (by simp; omega)
  set s2 := c.cpy.exec inp s1
  have hex : (c.visitC k).exec inp st = s2.setR c.VL (s2.regs (c.lenR k)) := rfl
  have h2len : s2.regs (c.lenR k) = x.length := by
    rw [a3 _ (Or.inr (Or.inl (by simp <;> omega)))]; rw [e1 _ (Or.inr (by simp <;> omega))]
    exact hlen
  rw [hex]
  refine ⟨by simp only [HS.setR_regs, Function.update_self]; exact h2len, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i hi
    simp only [HS.setR_arr]
    rw [a1 i hi]; exact hx i hi
  · intro r hr hrw
    simp only [HS.setR_regs]
    rw [upd_ne (by simp; omega), a3 r (by omega), e1 r hr]
  · intro y i hy
    simp only [HS.setR_arr]
    rw [a2 y i (by simp at hy ⊢; omega)]; rfl
  · simp [a4, hs1]
  · simp [a5, hs1]
  · have hc : (c.visitC k).cost inp B st = (seqs [lit c.S (c.buf k), lit c.so 0, lit c.D c.vis,
        lit c.dO 0, cp c.n (c.lenR k)]).cost inp B st + c.cpy.cost inp B s1 +
        kappa B (RAM.bits (s2.regs (c.lenR k))) := by
      simp only [visitC, cost_seq, cost_cp]; ring
    rw [hc, h2len]
    have hpre : (seqs [lit c.S (c.buf k), lit c.so 0, lit c.D c.vis,
        lit c.dO 0, cp c.n (c.lenR k)]).cost inp B st ≤ 5 * kappa B (RAM.bits M) := by
      simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp, exec_seqs_cons,
        exec_lit, HS.setR_regs, upd_ne, lenR, S, so, D, dO, hlen']
      have := kappa_bits_le B (a := c.buf k) (M := M) (by simp; omega)
      have := kappa_bits_le B (a := c.vis) (M := M) (by simp; omega)
      have := kappa_bits_le B (a := x.length) (M := M) (by omega)
      have := kappa_bits_le B (a := 0) (M := M) (by omega)
      simp only [buf, vis] at *
      omega
    have := kappa_bits_le B (a := x.length) (M := M) (by omega)
    nlinarith

end EnumCfg

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.EnumCfg.visitC_spec_oai := @EditMulticoloring.Dev.Ram.EnumCfg.visitC_spec_oai
