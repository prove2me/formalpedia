-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.radW_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:37:29.406404+00:00
-- url     : https://prove2.me/submissions/8bb84d48-6c3f-4feb-a2db-afb540aa0e2e

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_exec_cur_of_reads
import Theorems.Thm_EditMulticoloring_Dev_Ram_exec_mem_of_stores
import Theorems.Thm_EditMulticoloring_Dev_Ram_exec_out_of_emits
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le
import Theorems.Thm_EditMulticoloring_Dev_Ram_powW_spec
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

/-! ## Syntactic frames -/

section Frames
variable (inp : ℕ → ℕ)

theorem iterate_induct {f : HS → HS} (P : HS → Prop) (h : ∀ s, P s → P (f s)) :
    ∀ (n : ℕ) (s : HS), P s → P (f^[n] s)
  | 0, _, hs => hs
  | n + 1, s, hs => by rw [Function.iterate_succ_apply]; exact iterate_induct P h n _ (h _ hs)

theorem exec_regs_of_not_mem (c : Cmd) {r : ℕ} (h : r ∉ c.wregs) (s : HS) :
    (c.exec inp s).regs r = s.regs r := by
  induction c generalizing s with
  | prim p =>
    cases p <;> simp_all [Cmd.wregs, Cmd.exec, Prim.exec]
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [Cmd.wregs, List.mem_append, not_or] at h
    simp [ih₁ h.1, ih₂ h.2]
  | ifz a c₁ c₂ ih₁ ih₂ =>
    simp only [Cmd.wregs, List.mem_append, not_or] at h
    simp only [exec_ifz]; split_ifs
    · exact ih₁ h.1 s
    · exact ih₂ h.2 s
  | loop a c ih =>
    simp only [Cmd.wregs] at h
    rw [exec_loop]
    exact iterate_induct (fun t => t.regs r = s.regs r) (fun t ht => (ih h t).trans ht) _ _ rfl
  | skip => rfl

end Frames

/-! ## Loops -/

/-! ## Words stored in arrays -/

/-! ## Copying a block of cells -/

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamParams
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# Part P (q379): logarithms and powers

Register convention: inputs in arbitrary registers below `S`; outputs at `S`, `S + 1`, …;
scratch above the outputs.  Each program's frame lemma lists the registers it may write.

* `floorLogW b N T S`: `S := Nat.log (regs b) (regs N)`, `S+1 := regs b ^ (regs S)`
  (needs `Nat.log … ≤ regs T`, loop count `regs T`); writes `S .. S+3`.
* `ceilLogW b N T S`: `S := ceilLog (regs b) (regs N)`, `S+1 := regs b ^ (regs S)`; `S .. S+3`.
* `powW a e S`: `S := regs a ^ regs e`; writes only `S`.
* `radW q t lR S`: `S := radiusBound q (2 t) (regs lR)`; writes `S .. S+2`.
* `rhoW q t nR hR qhR S`: `S := shortLength q t (regs hR)`; writes `S .. S+8`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

section Logs
variable (inp : ℕ → ℕ) (B : ℕ)

theorem radW_frame (q t lR S : ℕ) (s : HS) (r' : ℕ) (h : r' < S ∨ S + 3 ≤ r') :
    ((radW q t lR S).exec inp s).regs r' = s.regs r' := by
  apply exec_regs_of_not_mem
  simp only [radW, powW, seqs, Cmd.wregs, lit, ar, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, not_or, not_false_eq_true, and_true, true_and]
  omega

theorem radW_spec_oai (q t lR S : ℕ) (s : HS) (M : ℕ) (hl : lR < S) (hq : 1 ≤ q)
    (hM : radiusBound q (2 * t) (s.regs lR) + 2 * q * (s.regs lR + 2 * t + 1) + 2 * q + 2 * t + 2 ≤ M) :
    ((radW q t lR S).exec inp s).regs S = radiusBound q (2 * t) (s.regs lR) ∧
    (∀ r', (r' < S ∨ S + 3 ≤ r') → ((radW q t lR S).exec inp s).regs r' = s.regs r') ∧
    ((radW q t lR S).exec inp s).mem = s.mem ∧
    ((radW q t lR S).exec inp s).cur = s.cur ∧
    ((radW q t lR S).exec inp s).out = s.out ∧
    (radW q t lR S).cost inp B s ≤ (4 * t + 11) * kappa B (RAM.bits M) := by
  set l := s.regs lR with hl'
  set s1 := (seqs [lit S (2 * t + 1), ar .add S lR S, lit (S + 1) (2 * q), ar .mul S S (S + 1),
    lit (S + 1) (2 * t)]).exec inp s with hs1
  set base := (l + (2 * t + 1)) * (2 * q) with hbase
  have e0 : s1.regs S = base := by simp (disch := omega) [hs1, upd_ne, hbase, hl']
  have e1 : s1.regs (S + 1) = 2 * t := by simp (disch := omega) [hs1, upd_ne]
  have hb1 : 1 ≤ base := by rw [hbase]; nlinarith
  have hR : radiusBound q (2 * t) l = (2 * t + 1) * base ^ (2 * t) := by
    rw [radiusBound, hbase]; ring_nf
  have hbR : base ^ (2 * t) ≤ radiusBound q (2 * t) l := by rw [hR]; nlinarith
  have hbase' : base = 2 * q * (l + 2 * t + 1) := by rw [hbase]; ring
  obtain ⟨p1, p2, -, -, -, p6⟩ := powW_spec inp B S (S + 1) (S + 2) s1 M (by omega) (by omega)
    (by rw [e0]; exact hb1) (by rw [e0, e1]; omega)
  set s2 := (powW S (S + 1) (S + 2)).exec inp s1 with hs2
  have hex : (radW q t lR S).exec inp s = (seqs [lit (S + 1) (2 * t + 1),
    ar .mul S (S + 2) (S + 1)]).exec inp s2 := rfl
  have hco : (radW q t lR S).cost inp B s = (seqs [lit S (2 * t + 1), ar .add S lR S,
      lit (S + 1) (2 * q), ar .mul S S (S + 1), lit (S + 1) (2 * t)]).cost inp B s +
      ((powW S (S + 1) (S + 2)).cost inp B s1 + (seqs [lit (S + 1) (2 * t + 1),
    ar .mul S (S + 2) (S + 1)]).cost inp B s2) := rfl
  have f2 : s2.regs (S + 2) = base ^ (2 * t) := by rw [p1, e0, e1]
  refine ⟨?_, radW_frame inp q t lR S s, exec_mem_of_stores inp _ rfl s,
    exec_cur_of_reads inp _ rfl s, exec_out_of_emits inp _ rfl s, ?_⟩
  · rw [hex]; simp (disch := omega) only [exec_seqs_cons, exec_seqs_nil, exec_lit, exec_ar,
      HS.setR_regs, upd_ne, upd_eq, f2, arith_mul]
    rw [hR]; ring
  · rw [hco]
    rw [e1] at p6
    simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_ar, cost_lit, exec_seqs_cons,
      exec_ar, exec_lit, HS.setR_regs, upd_ne, upd_eq, f2, arith_add, arith_mul, hl']
    have hb2 : l + 2 * t + 1 ≤ 2 * q * (l + 2 * t + 1) := by nlinarith
    have k1 := kappa_bits_le B (a := 2 * t + 1) (M := M) (by omega)
    have k2 := kappa_bits_le B (a := l + (2 * t + 1)) (M := M) (by omega)
    have k3 := kappa_bits_le B (a := 2 * q) (M := M) (by omega)
    have k4 := kappa_bits_le B (a := l + (2 * t + 1) + 2 * q) (M := M) (by omega)
    have k5 := kappa_bits_le B (a := 2 * t) (M := M) (by omega)
    have k6 := kappa_bits_le B (a := base ^ (2 * t) + (2 * t + 1)) (M := M) (by omega)
    rw [← hl']
    have hy : (4 * t + 11) * kappa B (RAM.bits M) =
        (2 * (2 * t) + 3) * kappa B (RAM.bits M) + 8 * kappa B (RAM.bits M) := by ring
    omega

/-! ### The short length `ρ = shortLength q t h` -/

end Logs

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.radW_spec_oai := @EditMulticoloring.Dev.Ram.radW_spec_oai
