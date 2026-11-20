-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.pA_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:37:01.031601+00:00
-- url     : https://prove2.me/submissions/c6b7a7f5-e855-485f-8f5e-81a48dc59977

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_ceilLogW_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_exec_cur_of_reads
import Theorems.Thm_EditMulticoloring_Dev_Ram_exec_mem_of_stores
import Theorems.Thm_EditMulticoloring_Dev_Ram_exec_out_of_emits
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le
import Theorems.Thm_EditMulticoloring_Dev_Ram_log_le_of_pos
import Theorems.Thm_EditMulticoloring_Dev_Ram_radW_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_upd_eq
import Theorems.Thm_EditMulticoloring_Dev_Ram_upd_ne

section
-- module Solutions.EditMulticoloring.RamParams4
/-!
# Part P (q379): the parameters, part A (`r, K, b, Q, B, L, W`) and part F (`f, J, h₁`)

Output block `O`: `O+0 r, O+1 K, O+2 b, O+3 Q, O+4 B, O+5 L, O+6 W = b + 1,
O+7 f = floorLog q (L / 2), O+8 J, O+9 h₁, O+10 h₂, O+11 h, O+12 q^h, O+13 ρ, O+14 q^ρ,
O+15 m, O+16 k`; temporaries `O+17 .. O+22`; subroutine scratch from `O+23` (to `O+48`).
Here `b = ceilLog 2 (r * K + 1)` (so `Q = 2 ^ b`, `B = 2 b`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

section PartA
variable (inp : ℕ → ℕ) (B : ℕ)

theorem pA_spec_oai (q t nR O : ℕ) (s : HS) (M : ℕ) (hq : 2 ≤ q) (hn : nR < O)
    (hM : pABound q t (s.regs nR) ≤ M) :
    ((pA q t nR O).exec inp s).regs O = (parameters q t (s.regs nR)).r ∧
    ((pA q t nR O).exec inp s).regs (O + 1) = (parameters q t (s.regs nR)).K ∧
    ((pA q t nR O).exec inp s).regs (O + 2) =
      ceilLog 2 ((parameters q t (s.regs nR)).r * (parameters q t (s.regs nR)).K + 1) ∧
    ((pA q t nR O).exec inp s).regs (O + 3) = (parameters q t (s.regs nR)).Q ∧
    ((pA q t nR O).exec inp s).regs (O + 4) = (parameters q t (s.regs nR)).B ∧
    ((pA q t nR O).exec inp s).regs (O + 5) = (parameters q t (s.regs nR)).L ∧
    ((pA q t nR O).exec inp s).regs (O + 6) =
      ceilLog 2 ((parameters q t (s.regs nR)).r * (parameters q t (s.regs nR)).K + 1) + 1 ∧
    (∀ r', (r' < O ∨ (O + 7 ≤ r' ∧ r' < O + 17) ∨ O + 49 ≤ r') →
      ((pA q t nR O).exec inp s).regs r' = s.regs r') ∧
    ((pA q t nR O).exec inp s).mem = s.mem ∧
    ((pA q t nR O).exec inp s).cur = s.cur ∧
    ((pA q t nR O).exec inp s).out = s.out ∧
    (pA q t nR O).cost inp B s ≤
      (7 * ((parameters q t (s.regs nR)).r * (parameters q t (s.regs nR)).K + 1) + 4 * t + 40) *
        kappa B (RAM.bits M) := by
  set n := s.regs nR with hnd
  set P := parameters q t n with hP
  have hr : P.r = radiusBound q (2 * t) n := rfl
  have hK : P.K = n * ceilLog 2 q := rfl
  set X := P.r * P.K + 1 with hX
  set b := ceilLog 2 X with hb
  have hQ : P.Q = 2 ^ b := rfl
  have hB : P.B = 2 * b := rfl
  have hL : P.L = 4 * (P.r + 1) * (P.B + 1) := rfl
  unfold pABound at hM
  rw [← hP] at hM
  clear_value P X b
  have hL1 : P.r + 1 + (P.B + 1) ≤ P.L := by rw [hL]; nlinarith
  have hL2 : 4 + (P.r + 1) * (P.B + 1) ≤ P.L + 4 := by rw [hL]; nlinarith
  -- radW
  obtain ⟨a1, a2, -, -, -, a6⟩ := radW_spec inp B q t nR (O + 23) s M (by omega) (by omega)
    (by rw [← hnd]; omega)
  set s1 := (radW q t nR (O + 23)).exec inp s with hs1
  have e1n : s1.regs nR = n := a2 nR (by omega)
  rw [← hnd, ← hr] at a1
  -- first block
  set s2 := (seqs [cp O (O + 23), lit (O + 17) (ceilLog 2 q),
    ar .mul (O + 1) nR (O + 17), ar .mul (O + 18) O (O + 1), lit (O + 17) 1,
    ar .add (O + 18) (O + 18) (O + 17), lit (O + 17) 2]).exec inp s1 with hs2
  have b0 : s2.regs O = P.r := by simp (disch := omega) only [hs2, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_lit, exec_ar, HS.setR_regs, arith_add, arith_mul, upd_ne, upd_eq, a1]
  have b1 : s2.regs (O + 1) = P.K := by simp (disch := omega) only [hs2, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_lit, exec_ar, HS.setR_regs, arith_add, arith_mul, upd_ne, upd_eq, e1n, hK]
  have b18 : s2.regs (O + 18) = X := by simp (disch := omega) only [hs2, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_lit, exec_ar, HS.setR_regs, arith_add, arith_mul, upd_ne, upd_eq, e1n, hK, a1, hX]
  have b17 : s2.regs (O + 17) = 2 := by simp (disch := omega) only [hs2, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_lit, exec_ar, HS.setR_regs, arith_add, arith_mul, upd_ne, upd_eq]
  have bfr : ∀ r', (r' < O ∨ (O + 7 ≤ r' ∧ r' < O + 17) ∨ O + 49 ≤ r') → s2.regs r' = s.regs r' :=
    fun r' h => by
      simp (disch := omega) only [hs2, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_lit, exec_ar,
        HS.setR_regs, upd_ne]
      exact a2 r' (by omega)
  -- ceilLogW
  have hlogX : Nat.log 2 X ≤ X := log_le_of_pos (le_refl 2)
  obtain ⟨c1, c2, c3, -, -, -, c7⟩ := ceilLogW_spec inp B (O + 17) (O + 18) (O + 18) (O + 23) s2 M
    (by omega) (by omega) (by omega) (by rw [b17]) (by rw [b17, b18]; exact hlogX)
    (by rw [b17, b18]; omega)
  rw [b17, b18, ← hb] at c1 c2
  rw [b18] at c7
  set s3 := (ceilLogW (O + 17) (O + 18) (O + 18) (O + 23)).exec inp s2 with hs3
  have d0 : s3.regs O = P.r := by rw [c3 _ (by omega), b0]
  have hPQ : P.Q ≤ M := by omega
  have hBL : P.B + 1 ≤ P.L := by omega
  -- second block
  set s4 := (seqs [cp (O + 2) (O + 23), cp (O + 3) (O + 24), ar .add (O + 4) (O + 2) (O + 2),
    lit (O + 17) 1, ar .add (O + 6) (O + 2) (O + 17)]).exec inp s3 with hs4
  have u2 : s4.regs (O + 2) = b := by
    simp (disch := omega) only [hs4, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_lit, exec_ar,
      HS.setR_regs, arith_add, arith_mul, upd_ne, upd_eq, c1]
  have u3 : s4.regs (O + 3) = 2 ^ b := by
    simp (disch := omega) only [hs4, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_lit, exec_ar,
      HS.setR_regs, arith_add, arith_mul, upd_ne, upd_eq, c2]
  have u4 : s4.regs (O + 4) = b + b := by
    simp (disch := omega) only [hs4, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_lit, exec_ar,
      HS.setR_regs, arith_add, arith_mul, upd_ne, upd_eq, c1]
  have u17 : s4.regs (O + 17) = 1 := by
    simp (disch := omega) only [hs4, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_lit, exec_ar,
      HS.setR_regs, arith_add, arith_mul, upd_ne, upd_eq]
  have u6 : s4.regs (O + 6) = b + 1 := by
    simp (disch := omega) only [hs4, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_lit, exec_ar,
      HS.setR_regs, arith_add, arith_mul, upd_ne, upd_eq, c1]
  have ufr : ∀ r', r' ≠ O + 2 → r' ≠ O + 3 → r' ≠ O + 4 → r' ≠ O + 17 → r' ≠ O + 6 →
      s4.regs r' = s3.regs r' := fun r' a1 a2 a3 a4 a5 => by
    simp (disch := omega) only [hs4, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_lit, exec_ar,
      HS.setR_regs, arith_add, arith_mul, upd_ne]
  have u0 : s4.regs O = P.r := by rw [ufr _ (by omega) (by omega) (by omega) (by omega) (by omega), d0]
  set s5 := (seqs [ar .add (O + 18) O (O + 17), ar .add (O + 19) (O + 4) (O + 17),
    ar .mul (O + 18) (O + 18) (O + 19), lit (O + 17) 4, ar .mul (O + 5) (O + 17) (O + 18)]).exec inp s4 with hs5
  have v5 : s5.regs (O + 5) = P.L := by
    simp (disch := omega) only [hs5, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_lit, exec_ar,
      HS.setR_regs, arith_add, arith_mul, upd_ne, upd_eq, u0, u4, u17]
    rw [hL, hB]; ring
  have vfr : ∀ r', r' ≠ O + 18 → r' ≠ O + 19 → r' ≠ O + 17 → r' ≠ O + 5 →
      s5.regs r' = s4.regs r' := fun r' a1 a2 a3 a4 => by
    simp (disch := omega) only [hs5, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_lit, exec_ar,
      HS.setR_regs, arith_add, arith_mul, upd_ne]
  have hex : (pA q t nR O).exec inp s = s5 := rfl
  have hco : (pA q t nR O).cost inp B s = (radW q t nR (O + 23)).cost inp B s +
      ((seqs [cp O (O + 23), lit (O + 17) (ceilLog 2 q),
    ar .mul (O + 1) nR (O + 17), ar .mul (O + 18) O (O + 1), lit (O + 17) 1,
    ar .add (O + 18) (O + 18) (O + 17), lit (O + 17) 2]).cost inp B s1 +
      ((ceilLogW (O + 17) (O + 18) (O + 18) (O + 23)).cost inp B s2 +
      ((seqs [cp (O + 2) (O + 23), cp (O + 3) (O + 24), ar .add (O + 4) (O + 2) (O + 2),
    lit (O + 17) 1, ar .add (O + 6) (O + 2) (O + 17)]).cost inp B s3 + (seqs [ar .add (O + 18) O (O + 17), ar .add (O + 19) (O + 4) (O + 17),
    ar .mul (O + 18) (O + 18) (O + 19), lit (O + 17) 4, ar .mul (O + 5) (O + 17) (O + 18)]).cost inp B s4))) := rfl
  have k3 : (seqs [cp (O + 2) (O + 23), cp (O + 3) (O + 24), ar .add (O + 4) (O + 2) (O + 2),
    lit (O + 17) 1, ar .add (O + 6) (O + 2) (O + 17)]).cost inp B s3 ≤ 5 * kappa B (RAM.bits M) := by
    simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_cp, cost_lit, cost_ar,
      exec_cp, exec_lit, exec_ar, HS.setR_regs, upd_ne, upd_eq, c1, c2, arith_mul, arith_add]
    have := kappa_bits_le B (a := b) (M := M) (by omega)
    have := kappa_bits_le B (a := 2 ^ b) (M := M) (by rw [← hQ]; omega)
    have := kappa_bits_le B (a := b + b) (M := M) (by omega)
    have := kappa_bits_le B (a := 1) (M := M) (by omega)
    have := kappa_bits_le B (a := b + 1) (M := M) (by omega)
    omega
  have k4 : (seqs [ar .add (O + 18) O (O + 17), ar .add (O + 19) (O + 4) (O + 17),
    ar .mul (O + 18) (O + 18) (O + 19), lit (O + 17) 4, ar .mul (O + 5) (O + 17) (O + 18)]).cost inp B s4 ≤ 5 * kappa B (RAM.bits M) := by
    simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_cp, cost_lit, cost_ar,
      exec_cp, exec_lit, exec_ar, HS.setR_regs, upd_ne, upd_eq, u0, u4, u17, arith_mul, arith_add]
    have := kappa_bits_le B (a := P.r + 1) (M := M) (by omega)
    have := kappa_bits_le B (a := b + b + 1) (M := M) (by omega)
    have := kappa_bits_le B (a := P.r + 1 + (b + b + 1)) (M := M) (by omega)
    have := kappa_bits_le B (a := 4) (M := M) (by omega)
    have := kappa_bits_le B (a := 4 + (P.r + 1) * (b + b + 1)) (M := M)
      (by rw [show b + b = P.B by omega]; omega)
    omega
  have k1 : (seqs [cp O (O + 23), lit (O + 17) (ceilLog 2 q),
      ar .mul (O + 1) nR (O + 17), ar .mul (O + 18) O (O + 1), lit (O + 17) 1,
      ar .add (O + 18) (O + 18) (O + 17), lit (O + 17) 2]).cost inp B s1 ≤
      7 * kappa B (RAM.bits M) := by
    simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_cp, cost_lit, cost_ar,
      exec_cp, exec_lit, exec_ar, HS.setR_regs, upd_ne, upd_eq, a1, e1n, arith_mul, arith_add]
    have := kappa_bits_le B (a := P.r) (M := M) (by omega)
    have := kappa_bits_le B (a := ceilLog 2 q) (M := M) (by omega)
    have := kappa_bits_le B (a := n + ceilLog 2 q) (M := M) (by omega)
    have := kappa_bits_le B (a := P.r + n * ceilLog 2 q) (M := M) (by rw [← hK]; omega)
    have := kappa_bits_le B (a := 1) (M := M) (by omega)
    have := kappa_bits_le B (a := P.r * (n * ceilLog 2 q) + 1) (M := M) (by rw [← hK]; omega)
    have := kappa_bits_le B (a := 2) (M := M) (by omega)
    omega
  clear_value s1 s2 s3 s4 s5
  rw [hex]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vfr _ (by omega) (by omega) (by omega) (by omega), u0]
  · rw [vfr _ (by omega) (by omega) (by omega) (by omega),
      ufr _ (by omega) (by omega) (by omega) (by omega) (by omega), c3 _ (by omega), b1]
  · rw [vfr _ (by omega) (by omega) (by omega) (by omega), u2]
  · rw [vfr _ (by omega) (by omega) (by omega) (by omega), u3, hQ]
  · rw [vfr _ (by omega) (by omega) (by omega) (by omega), u4, hB]; ring
  · exact v5
  · rw [vfr _ (by omega) (by omega) (by omega) (by omega), u6]
  · intro r' h
    rw [vfr _ (by omega) (by omega) (by omega) (by omega),
      ufr _ (by omega) (by omega) (by omega) (by omega) (by omega), c3 _ (by omega)]
    exact bfr r' h
  · rw [← hex]; exact exec_mem_of_stores inp _ rfl s
  · rw [← hex]; exact exec_cur_of_reads inp _ rfl s
  · rw [← hex]; exact exec_out_of_emits inp _ rfl s
  · rw [hco]
    have hy : (7 * X + 4 * t + 40) * kappa B (RAM.bits M) = (4 * t + 11) * kappa B (RAM.bits M) +
      (7 * X + 9) * kappa B (RAM.bits M) + 20 * kappa B (RAM.bits M) := by ring
    omega

end PartA

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.pA_spec_oai := @EditMulticoloring.Dev.Ram.pA_spec_oai
