-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.EnumCfg.delC_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:34.725079+00:00
-- url     : https://prove2.me/submissions/07b88df2-53c7-451b-a337-70072d6e52e2

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_lt
import Theorems.Thm_EditMulticoloring_Dev_Ram_copyW_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le
import Theorems.Thm_EditMulticoloring_Dev_Ram_upd_eq
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

theorem delW_length {q : ℕ} (x : Word q) (i : ℕ) (hi : i < x.length) :
    (delW x i).length = x.length - 1 := by
  simp [delW]; omega

theorem delW_get_lt {q : ℕ} (x : Word q) (i : ℕ) (hi : i < x.length) (j : ℕ) (hj : j < i)
    (h : j < (delW x i).length) : (delW x i)[j] = x[j]'(by simp [delW] at h; omega) := by
  simp only [delW]
  rw [List.getElem_append_left (by simp <;> omega)]
  simp
theorem delW_get_ge {q : ℕ} (x : Word q) (i : ℕ) (hi : i < x.length) (m : ℕ)
    (h : i + m < (delW x i).length) :
    (delW x i)[i + m] = x[i + 1 + m]'(by simp [delW] at h; omega) := by
  simp only [delW]
  rw [List.getElem_append_right (by simp <;> omega)]
  simp [Nat.min_eq_left hi.le, show i + m - i = m by omega]

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

theorem delC_spec_oai {q : ℕ} (k : ℕ) (x : Word q) (st : HS) (i : ℕ) (hi : i < x.length)
    (hlen : st.regs (c.lenR (k + 1)) = x.length) (hx : WordAt st (c.buf (k + 1)) 0 x)
    (hiR : st.regs (c.iR (k + 1)) = i)
    (M : ℕ) (hM : 2 * c.a0 + 2 * x.length + 2 * k + q + 4 ≤ M) :
    ((c.delC k).exec inp st).regs (c.lenR k) = (delW x i).length ∧
    WordAt ((c.delC k).exec inp st) (c.buf k) 0 (delW x i) ∧
    c.Fr (c.lenR k) (c.buf k) st ((c.delC k).exec inp st) ∧
    (c.delC k).cost inp B st ≤ (7 * x.length + 20) * kappa B (RAM.bits M) := by
  simp only [lenR, iR, aR] at hlen hiR
  have xlt := hx.lt
  have hx' : ∀ j (h : j < x.length), st.arr (c.buf (k + 1)) j = (x[j]).val := fun j h => by
    simpa using hx j h
  set s1 := (seqs [lit c.S (c.buf (k + 1)), lit c.so 0, lit c.D (c.buf k), lit c.dO 0,
    cp c.n (c.iR (k + 1))]).exec inp st with hs1
  have e1 : ∀ r, (r < c.r0 ∨ c.r0 + 16 ≤ r) → s1.regs r = st.regs r := by
    intro r hr; simp (disch := omega) [hs1]
  have m1 : ∀ y j, s1.arr y j = st.arr y j := by intro y j; simp [hs1]
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := c.cpy_run inp B s1 (c.buf (k + 1)) 0 (c.buf k) 0 i q M
    (by simp [hs1]) (by simp [hs1]) (by simp [hs1]) (by simp [hs1])
    (by simp (disch := omega) [hs1, hiR]) (by simp <;> omega)
    (fun j hj => by rw [m1]; exact (xlt j (by omega)).le) (by simp <;> omega)
  set s2 := c.cpy.exec inp s1 with hs2
  have r2 : ∀ r, (r < c.r0 ∨ c.r0 + 16 ≤ r) → s2.regs r = st.regs r := fun r hr =>
    (a3 r (hr.elim Or.inl (fun h => Or.inr (Or.inl h)))).trans (e1 r hr)
  have r2D : s2.regs (c.r0 + 5) = c.a0 + 1 + k := by
    rw [a3 _ (by simp)]; simp [hs1]
  have r2S : s2.regs (c.r0 + 3) = c.a0 + 1 + (k + 1) := by
    rw [a3 _ (by simp)]; simp [hs1]
  have a1' : ∀ j < i, s2.arr (c.buf k) j = s1.arr (c.buf (k + 1)) j := fun j h => by
    simpa using a1 j h
  set s3 := (seqs [lit c.one 1, cp c.dO (c.iR (k + 1)), ar .add c.so (c.iR (k + 1)) c.one,
    ar .sub c.n (c.lenR (k + 1)) c.so]).exec inp s2 with hs3
  have hiR2 : s2.regs (c.r0 + (16 + 3 * (k + 1))) = i := by rw [r2 _ (by omega)]; exact hiR
  have hlen2 : s2.regs (c.r0 + (18 + 3 * (k + 1))) = x.length := by rw [r2 _ (by omega)]; exact hlen
  have e3 : ∀ r, (r < c.r0 ∨ c.r0 + 16 ≤ r) → s3.regs r = s2.regs r := by
    intro r hr; simp (disch := omega) [hs3]
  have m3 : ∀ y j, s3.arr y j = s2.arr y j := by intro y j; simp [hs3]
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := c.cpy_run inp B s3 (c.buf (k + 1)) (i + 1) (c.buf k) i
    (x.length - (i + 1)) q M
    (by simp (disch := omega) [hs3, r2S])
    (by simp (disch := omega) [hs3, hiR2])
    (by simp (disch := omega) [hs3, r2D])
    (by simp (disch := omega) [hs3, hiR2])
    (by simp (disch := omega) [hs3, hiR2, hlen2]) (by simp <;> omega)
    (fun m hm => by
      rw [m3, a2 _ _ (by simp <;> omega), m1]
      have := xlt (i + 1 + m) (by omega); simp only [Nat.zero_add] at this ⊢; omega)
    (by simp <;> omega)
  set s4 := c.cpy.exec inp s3 with hs4
  have hex : (c.delC k).exec inp st =
      (seqs [lit c.one 1, ar .sub (c.lenR k) (c.lenR (k + 1)) c.one]).exec inp s4 := rfl
  have hlen4 : s4.regs (c.r0 + (18 + 3 * (k + 1))) = x.length := by
    rw [b3 _ (by omega), e3 _ (by omega), hlen2]
  have r4 : ∀ r, (r < c.r0 ∨ c.r0 + 16 ≤ r) → s4.regs r = st.regs r := fun r hr => by
    rw [b3 _ (by omega), e3 _ hr, r2 _ hr]
  rw [hex]
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simp (disch := omega) [hlen4, delW_length x i hi]
  · intro j hj
    rw [delW_length x i hi] at hj
    simp only [exec_seqs_cons, exec_seqs_nil, exec_lit, exec_ar, HS.setR_arr, Nat.zero_add]
    rcases Nat.lt_or_ge j i with hji | hji
    · rw [b2 _ _ (by simp <;> omega), m3, a1' j hji, m1,
        hx' j (by omega), delW_get_lt x i hi j hji]
    · obtain ⟨m, rfl⟩ : ∃ m, j = i + m := ⟨j - i, by omega⟩
      rw [b1 m (by omega), m3, a2 _ _ (by simp <;> omega), m1,
        hx' (i + 1 + m) (by omega), delW_get_ge x i hi m]
  · intro r hr hrw
    simp only [lenR] at hrw
    simp (disch := omega) only [exec_seqs_cons, exec_seqs_nil, exec_lit, exec_ar, HS.setR_regs,
      upd_ne, one, lenR]
    exact r4 r hr
  · intro y j hy
    simp only [exec_seqs_cons, exec_seqs_nil, exec_lit, exec_ar, HS.setR_arr]
    simp only [buf] at hy
    rw [b2 _ _ (by simp <;> omega), m3, a2 _ _ (by simp <;> omega), m1]
  · simp [b4, a4, hs3, hs1]
  · simp [b5, a5, hs3, hs1]
  · have hc : (c.delC k).cost inp B st =
        (seqs [lit c.S (c.buf (k + 1)), lit c.so 0, lit c.D (c.buf k), lit c.dO 0,
          cp c.n (c.iR (k + 1))]).cost inp B st + c.cpy.cost inp B s1 +
        (seqs [lit c.one 1, cp c.dO (c.iR (k + 1)), ar .add c.so (c.iR (k + 1)) c.one,
          ar .sub c.n (c.lenR (k + 1)) c.so]).cost inp B s2 +
        c.cpy.cost inp B s3 +
        (seqs [lit c.one 1, ar .sub (c.lenR k) (c.lenR (k + 1)) c.one]).cost inp B s4 := by
      simp only [delC, cost_seq]; ring
    rw [hc]
    have K0 := kappa_bits_le B (a := 0) (M := M) (by omega)
    have K1 := kappa_bits_le B (a := 1) (M := M) (by omega)
    have p1 : (seqs [lit c.S (c.buf (k + 1)), lit c.so 0, lit c.D (c.buf k), lit c.dO 0,
          cp c.n (c.iR (k + 1))]).cost inp B st ≤ 5 * kappa B (RAM.bits M) := by
      simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp, exec_seqs_cons,
        exec_lit, HS.setR_regs, upd_ne, iR, S, so, D, dO, hiR, buf]
      have := kappa_bits_le B (a := c.a0 + 1 + (k + 1)) (M := M) (by omega)
      have := kappa_bits_le B (a := c.a0 + 1 + k) (M := M) (by omega)
      have := kappa_bits_le B (a := i) (M := M) (by omega)
      omega
    have p2 : (seqs [lit c.one 1, cp c.dO (c.iR (k + 1)), ar .add c.so (c.iR (k + 1)) c.one,
          ar .sub c.n (c.lenR (k + 1)) c.so]).cost inp B s2 ≤
          4 * kappa B (RAM.bits M) := by
      simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp, cost_ar,
        exec_seqs_cons, exec_lit, exec_ar, exec_cp, HS.setR_regs,
        upd_ne, upd_eq, iR, aR, lenR, S, so, D, dO, one, n, hiR2, hlen2, arith_add]
      have := kappa_bits_le B (a := i + 1) (M := M) (by omega)
      have := kappa_bits_le B (a := i) (M := M) (by omega)
      have := kappa_bits_le B (a := x.length + (i + 1)) (M := M) (by omega)
      omega
    have p3 : (seqs [lit c.one 1, ar .sub (c.lenR k) (c.lenR (k + 1)) c.one]).cost inp B s4 ≤
        2 * kappa B (RAM.bits M) := by
      simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_lit, cost_ar, exec_seqs_cons,
        exec_lit, HS.setR_regs, upd_ne, upd_eq, lenR, one, hlen4]
      have := kappa_bits_le B (a := x.length + 1) (M := M) (by omega)
      omega
    have h7 : (7 * i + 3) * kappa B (RAM.bits M) +
        (7 * (x.length - (i + 1)) + 3) * kappa B (RAM.bits M)
        ≤ (7 * x.length + 6) * kappa B (RAM.bits M) := by
      rw [← add_mul]; apply Nat.mul_le_mul_right; omega
    have h8 : (7 * x.length + 20) * kappa B (RAM.bits M) =
        (7 * x.length + 6) * kappa B (RAM.bits M) + 14 * kappa B (RAM.bits M) := by ring
    omega

end EnumCfg

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.EnumCfg.delC_spec_oai := @EditMulticoloring.Dev.Ram.EnumCfg.delC_spec_oai
