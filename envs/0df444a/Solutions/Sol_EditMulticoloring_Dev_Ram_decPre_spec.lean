-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.decPre_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:35:47.678143+00:00
-- url     : https://prove2.me/submissions/d125d0df-0f41-41d3-8964-840ae32db30e

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_EncS_greedy_length_le
import Theorems.Thm_EditMulticoloring_Dev_Ram_EncS_shortW_inverse
import Theorems.Thm_EditMulticoloring_Dev_Ram_EncS_shortW_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_dec_le_two_pow_ceilLog
import Theorems.Thm_EditMulticoloring_Dev_Ram_dec_one_le_r
import Theorems.Thm_EditMulticoloring_Dev_Ram_inputAt_le
import Theorems.Thm_EditMulticoloring_Dev_Ram_inputAt_sub_one
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le
import Theorems.Thm_EditMulticoloring_Dev_Ram_modulusW_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_paramsW_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_powW_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_readW_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_runLen_inputAt
import Theorems.Thm_EditMulticoloring_Dev_Ram_upd_eq
import Theorems.Thm_EditMulticoloring_Dev_Ram_upd_ne

section
-- module Solutions.EditMulticoloring.RamDecode4
/-!
# The decoder, part 4: the program `decProg` and its specification (q379, Part D)

The short-table routine is taken from `RamEncodeS4` (namespace `EncS`, a verbatim copy of
`RamShort*`), because `RamShort` and `RamColor` cannot be imported together (name clashes
`value_lt`, `visBound`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## The split of a short-code index -/

/-! ## Monotone bounds -/

/-! ## The program -/

section Top
variable (B : ℕ)

set_option maxHeartbeats 4000000 in
theorem decPre_spec_oai {q : ℕ} (t n : ℕ) (hq : 2 ≤ q) (y : Word q)
    (H1 : ∃ l ≤ n, rhoCond q t (parameters q t n).h l)
    (H2 : modSearch (decB q t n) < dTW q t n)
    (H3 : (parameters q t n).m + (parameters q t n).ρ = n) :
    let s := (decPre q t).exec (RAM.inputAt y) (HS.init n)
    DInv q t n (modSearch (decB q t n)) none s ∧
    s.regs ((dC0 t).lenR t) = (y.take (n + t + 1)).length ∧
    WordAt s ((dC0 t).buf t) 0 (y.take (n + t + 1)) ∧
    s.regs 10 = (if n + t < (y.take (n + t + 1)).length then 1 else 0) +
      (if (y.take (n + t + 1)).length + t < n then 1 else 0) ∧
    (decPre q t).cost (RAM.inputAt y) B (HS.init n) ≤ preCost q t n B := by
  intro s
  set inp := RAM.inputAt y with hinp
  set P := parameters q t n with hP
  set κ := kappa B (RAM.bits (DM q t n)) with hκ
  have kb : ∀ a, a ≤ DM q t n → kappa B (RAM.bits a) ≤ κ := fun a h => kappa_bits_le B h
  have hDM : DM q t n = 4 * q ^ n + 2 * q ^ P.h + 2 * (P.Q * P.Q) + 2 * dTW q t n + primeBound P.L +
    dVb q t n + P.L + 4 * n + P.k + 2 * q + 100 * t + 1000 := rfl
  set b := decB q t n with hb
  set p := modSearch b with hpdef
  have hqn : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
  have hρn : P.ρ ≤ n := by omega
  have hmn : P.m ≤ n := by omega
  have hqρ : q ^ P.ρ ≤ q ^ n := Nat.pow_le_pow_right (by omega) hρn
  have hhh : P.h = P.h₁ + P.h₂ := rfl
  have hqh2 : q ^ P.h₂ ≤ q ^ P.h := Nat.pow_le_pow_right (by omega) (by omega)
  have hh2 : P.h₂ < q ^ P.h₂ := Nat.lt_pow_self (by omega)
  have hbW : b + 1 < dTW q t n := Nat.lt_two_pow_self
  have hKQ : P.K ≤ P.Q := by
    have h1 : P.r * P.K + 1 ≤ P.Q := dec_le_two_pow_ceilLog _
    have h2 : 1 ≤ P.r := dec_one_le_r q t n (by omega)
    have : P.K ≤ P.r * P.K := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hQQ : P.Q ≤ P.Q * P.Q := Nat.le_mul_self _
  -- phase 1
  set s0 := HS.init n with hs0
  set s1 := s0.setR 1 1 with hs1
  have s1r0 : s1.regs 0 = n := by simp [hs1, hs0, HS.init]
  have s1r1 : s1.regs 1 = 1 := by simp [hs1]
  -- phase 2: parameters
  obtain ⟨pa, ptab, parr, pfr, pcur, pout, pcost⟩ := paramsW_spec inp B q t 0 1 100 s1
    (paramsBound q t n 1) hq (by omega) (by omega) (by rw [s1r0]; exact H1)
    (by rw [s1r0, s1r1])
  rw [s1r0] at pa ptab parr pcost
  rw [s1r1] at ptab parr
  set s2 := (paramsW q t 0 1 100).exec inp s1 with hs2
  -- phase 3: modulus
  have e102 : s2.regs 102 = b := pa.hb
  obtain ⟨m200, mfr, mmem, mcur, mout, mcost⟩ := modulusW_spec inp B 102 200 s2
    ((2 ^ b + 4) * 2 ^ (2 * (b + 1))) (by omega) (by rw [e102])
  rw [e102] at m200 mcost
  set s3 := (modulusW 102 200).exec inp s2 with hs3
  have m200' : s3.regs 200 = p := m200
  have pW : s2.regs 106 = b + 1 := pa.hW
  have pK : s2.regs 101 = P.K := pa.hK
  have pQ : s2.regs 103 = P.Q := pa.hQ
  -- phase 4
  set s4 := (dSetA q).exec inp s3 with hs4
  have r4 : ∀ r, r ≠ 400 → r ≠ 403 → r ≠ 418 → r ≠ 424 → r ≠ 4 → s4.regs r = s3.regs r := by
    intro r h1 h2 h3 h4 h5; simp (disch := omega) [hs4, dSetA, upd_ne]
  have m4 : s4.mem = s3.mem := by simp [hs4, dSetA]
  have c4' : s4.cur = s3.cur := by simp [hs4, dSetA]
  have o4 : s4.out = s3.out := by simp [hs4, dSetA]
  have F23 : ∀ r, (r < 200 ∨ 226 ≤ r) → s3.regs r = s2.regs r := mfr
  have v400 : s4.regs 400 = p := by simp (disch := omega) [hs4, dSetA, upd_ne, m200, hpdef]
  have v403 : s4.regs 403 = b + 1 := by
    simp (disch := omega) [hs4, dSetA, upd_ne]; rw [F23 _ (by omega)]; exact pa.hW
  have v418 : s4.regs 418 = P.K := by
    simp (disch := omega) [hs4, dSetA, upd_ne]; rw [F23 _ (by omega)]; exact pa.hK
  have v424 : s4.regs 424 = P.Q := by
    simp (disch := omega) [hs4, dSetA, upd_ne]; rw [F23 _ (by omega)]; exact pa.hQ
  have v4 : s4.regs 4 = q := by simp (disch := omega) [hs4, dSetA, upd_ne]
  have hpb : p < dTW q t n := H2
  have c4 : (dSetA q).cost inp B s3 ≤ 5 * κ := by
    simp (disch := omega) only [dSetA, cost_seqs_cons, cost_seqs_nil, cost_lit, cost_cp,
      exec_seqs_cons, exec_cp, HS.setR_regs, upd_ne, m200']
    rw [F23 106 (by omega), F23 101 (by omega), F23 103 (by omega), pW, pK, pQ]
    have := kb p (by omega)
    have := kb (b + 1) (by omega)
    have := kb P.K (by omega)
    have := kb P.Q (by omega)
    have := kb q (by omega)
    omega
  -- phase 5: q^h₂
  have e110 : s4.regs 110 = P.h₂ := by
    rw [r4 _ (by omega) (by omega) (by omega) (by omega) (by omega), F23 _ (by omega)]
    exact pa.hh₂
  obtain ⟨w3, wfr, wmem, wcur, wout, wcost⟩ := powW_spec inp B 4 110 3 s4 (DM q t n) (by omega)
    (by omega) (by rw [v4]; omega) (by rw [v4, e110]; omega)
  rw [v4, e110] at w3
  rw [e110] at wcost
  set s5 := (powW 4 110 3).exec inp s4 with hs5
  have F25 : ∀ r, (r < 2 ∨ (100 ≤ r ∧ r < 149)) → s5.regs r = s2.regs r := by
    intro r hr
    rw [wfr r (by omega), r4 r (by omega) (by omega) (by omega) (by omega) (by omega), F23 r (by omega)]
  -- phase 6
  set s6 := (dSetS t).exec inp s5 with hs6
  have r6 : ∀ r, r ≠ 530 + 15 * t → r ≠ 531 + 15 * t → s6.regs r = s5.regs r := by
    intro r h1 h2; simp (disch := omega) [hs6, dSetS, upd_ne]
  have v6a : s6.regs (530 + 15 * t) = P.ρ := by
    simp (disch := omega) [hs6, dSetS, upd_ne]; rw [F25 _ (by omega)]; exact pa.hρ
  have v6b' : s6.regs (531 + 15 * t) = q ^ P.ρ := by
    simp (disch := omega) [hs6, dSetS, upd_ne]; rw [F25 _ (by omega)]; exact pa.hqρ
  have v6b : s6.regs (530 + 15 * t + 1) = q ^ P.ρ := by
    rw [show 530 + 15 * t + 1 = 531 + 15 * t by ring]; exact v6b'
  have c6 : (dSetS t).cost inp B s5 ≤ 2 * κ := by
    simp (disch := omega) only [dSetS, cost_seqs_cons, cost_seqs_nil, cost_cp, exec_seqs_cons,
      exec_cp, HS.setR_regs, upd_ne]
    rw [F25 113 (by omega), F25 114 (by omega)]
    have e1 : s2.regs 113 = P.ρ := pa.hρ
    have e2 : s2.regs 114 = q ^ P.ρ := pa.hqρ
    rw [e1, e2]
    have := kb P.ρ (by omega)
    have := kb (q ^ P.ρ) (by omega)
    omega
  have m6 : s6.mem = s5.mem := by simp [hs6, dSetS]
  -- phase 7: the short table
  have hq0 : 0 < q := by omega
  obtain ⟨⟨-, -, -, -, -, -, -, -, iINV, ifr, iarr, icur, iout⟩, icost⟩ :=
    EncS.shortW_spec inp B hq0 t (530 + 15 * t) (16 + 5 * t) P.ρ s6 v6a v6b
  have hinvS := EncS.shortW_inverse inp hq0 t P.h (530 + 15 * t) (16 + 5 * t) s6 v6a v6b
  set s7 := (EncS.shortW q t (530 + 15 * t) (16 + 5 * t)).exec inp s6 with hs7
  -- phase 8
  set s8 := (dSetR t).exec inp s7 with hs8
  have r8 : ∀ r, r ≠ 7 → r ≠ 5 → r ≠ 270 → r ≠ 271 → r ≠ 272 → s8.regs r = s7.regs r := by
    intro r h1 h2 h3 h4 h5; simp (disch := omega) [hs8, dSetR, upd_ne]
  have m8 : s8.mem = s7.mem := by simp [hs8, dSetR]
  have s7r0 : s7.regs 0 = n := by
    rw [ifr 0 (by omega), r6 _ (by omega) (by omega), F25 _ (by omega)]
    rw [pfr 0 (by omega)]; exact s1r0
  have v270 : s8.regs 270 = 15 + 5 * t := by simp (disch := omega) [hs8, dSetR, upd_ne]
  have v271 : s8.regs 271 = 0 := by simp (disch := omega) [hs8, dSetR, upd_ne]
  have v272 : s8.regs 272 = n + t + 1 := by
    simp (disch := omega) [hs8, dSetR, upd_ne, s7r0]; omega
  have c8 : (dSetR t).cost inp B s7 ≤ 5 * κ := by
    simp (disch := omega) only [dSetR, cost_seqs_cons, cost_seqs_nil, cost_cp, cost_lit, cost_ar,
      exec_seqs_cons, exec_cp, exec_lit, exec_ar, HS.setR_regs, upd_ne, upd_eq, s7r0, arith_add]
    have := kb (t + 1) (by omega)
    have := kb (n + (t + 1)) (by omega)
    have := kb (15 + 5 * t) (by omega)
    have := kb 0 (by omega)
    omega
  have cur8 : s8.cur = 0 := by
    rw [show s8.cur = s7.cur by simp [hs8, dSetR], icur, show s6.cur = s5.cur by simp [hs6, dSetS],
      wcur, c4', mcur, pcur]
    simp [hs1, hs0, HS.init]
  have out8 : s8.out = [] := by
    rw [show s8.out = s7.out by simp [hs8, dSetR], iout, show s6.out = s5.out by simp [hs6, dSetS],
      wout, o4, mout, pout]
    simp [hs1, hs0, HS.init]
  -- phase 9: read
  obtain ⟨d1, d2, d3, dfr, dcur, dout, dcost⟩ := readW_spec inp B 270 s8 q (DM q t n)
    (fun i _ => inputAt_le y _) (by
      rw [v270, show s8.regs (270 + 1) = 0 from v271, show s8.regs (270 + 2) = n + t + 1 from v272, cur8]
      omega)
  have v271' : s8.regs (270 + 1) = 0 := v271
  have v272' : s8.regs (270 + 2) = n + t + 1 := v272
  rw [v270, v271', v272', cur8] at d1
  rw [v270, v271', v272'] at d2
  rw [v272', cur8] at d3
  rw [v272'] at dcost
  set s9 := (readW 270).exec inp s8 with hs9
  set z := y.take (n + t + 1) with hz
  have hzl : z.length = min y.length (n + t + 1) := by rw [hz, List.length_take]; omega
  have e273 : s9.regs 273 = z.length := by rw [d3, runLen_inputAt, hzl]; omega
  -- phase 10
  set s10 := (dCheck t).exec inp s9 with hs10
  have r10 : ∀ r, r ≠ 528 + 15 * t → r ≠ 2 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 12 →
      s10.regs r = s9.regs r := by
    intro r h1 h2 h3 h4 h5 h6 h7; simp (disch := omega) [hs10, dCheck, upd_ne]
  have m10 : s10.mem = s9.mem := by simp [hs10, dCheck]
  have s9r0 : s9.regs 0 = n := by
    rw [dfr 0 (by omega), r8 _ (by omega) (by omega) (by omega) (by omega) (by omega), s7r0]
  have v10 : s10.regs 10 = (if n + t < z.length then 1 else 0) + (if z.length + t < n then 1 else 0) := by
    simp (disch := omega) [hs10, dCheck, upd_ne, s9r0, e273]
  have vlen : s10.regs (528 + 15 * t) = z.length := by
    simp (disch := omega) [hs10, dCheck, upd_ne, e273]
  have v2 : s10.regs 2 = 0 := by simp (disch := omega) [hs10, dCheck, upd_ne]
  have c10 : (dCheck t).cost inp B s9 ≤ 8 * κ := by
    have hz1 : z.length ≤ n + t + 1 := by omega
    simp (disch := omega) only [dCheck, cost_seqs_cons, cost_seqs_nil, cost_cp, cost_lit, cost_ar,
      exec_seqs_cons, exec_cp, exec_lit, exec_ar, HS.setR_regs, upd_ne, upd_eq, s9r0, e273,
      arith_add, arith_lt]
    have := kb z.length (by omega)
    have := kb 0 (by omega)
    have := kb t (by omega)
    have := kb (n + t) (by omega)
    have := kb (n + t + z.length) (by omega)
    have := kb (z.length + t) (by omega)
    have := kb (z.length + t + n) (by omega)
    have := kb ((if n + t < z.length then 1 else 0) + (if z.length + t < n then 1 else 0)) (by split_ifs <;> omega)
    omega
  -- the final state
  have F510 : ∀ r, (r < 2 ∨ r = 3 ∨ r = 4 ∨ r = 6 ∨ (13 ≤ r ∧ r < 270) ∨ (279 ≤ r ∧ r < 528 + 15 * t)) →
      s10.regs r = s5.regs r := by
    intro r hr
    rw [r10 r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      dfr r (by omega), r8 r (by omega) (by omega) (by omega) (by omega) (by omega),
      ifr r (by omega), r6 r (by omega) (by omega)]
  have G : ∀ r, 100 ≤ r → r < 117 → s10.regs r = s2.regs r := fun r h1 h2 => by
    rw [F510 r (by omega), F25 r (by omega)]
  have G4 : ∀ r, 279 ≤ r → r < 528 + 15 * t → s10.regs r = s4.regs r := fun r h1 h2 => by
    rw [F510 r (by omega), wfr r (by omega)]
  have A1 : ∀ i, s10.arr 1 i = s2.arr 1 i := by
    intro i
    rw [show s10.arr 1 i = s9.arr 1 i by simp [HS.arr, m10], d2 1 i (by omega),
      show s8.arr 1 i = s7.arr 1 i by simp [HS.arr, m8], iarr 1 i (by omega),
      show s6.arr 1 i = s5.arr 1 i by simp [HS.arr, m6], show s5.arr 1 i = s4.arr 1 i by simp [HS.arr, wmem],
      show s4.arr 1 i = s3.arr 1 i by simp [HS.arr, m4], show s3.arr 1 i = s2.arr 1 i by simp [HS.arr, mmem]]
  have AI : ∀ i, s10.arr (dINV t) i = s7.arr (16 + 5 * t + 2) i := by
    intro i
    have e : dINV t = 16 + 5 * t + 2 := by unfold dINV; ring
    rw [e, show s10.arr (16 + 5 * t + 2) i = s9.arr (16 + 5 * t + 2) i by simp [HS.arr, m10],
      d2 _ i (by omega), show s8.arr (16 + 5 * t + 2) i = s7.arr (16 + 5 * t + 2) i by simp [HS.arr, m8]]
  have hctx : DCtx q t n p s10 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [F510 0 (by omega), F25 0 (by omega), pfr 0 (by omega)]; exact s1r0
    · rw [F510 1 (by omega), F25 1 (by omega), pfr 1 (by omega)]; exact s1r1
    · rw [F510 3 (by omega)]; exact w3
    · rw [F510 4 (by omega), wfr 4 (by omega)]; exact v4
    · exact ⟨(G _ (by omega) (by omega)).trans pa.hr, (G _ (by omega) (by omega)).trans pa.hK,
        (G _ (by omega) (by omega)).trans pa.hb, (G _ (by omega) (by omega)).trans pa.hQ,
        (G _ (by omega) (by omega)).trans pa.hB, (G _ (by omega) (by omega)).trans pa.hL,
        (G _ (by omega) (by omega)).trans pa.hW, (G _ (by omega) (by omega)).trans pa.hf,
        (G _ (by omega) (by omega)).trans pa.hJ, (G _ (by omega) (by omega)).trans pa.hh₁,
        (G _ (by omega) (by omega)).trans pa.hh₂, (G _ (by omega) (by omega)).trans pa.hh,
        (G _ (by omega) (by omega)).trans pa.hqh, (G _ (by omega) (by omega)).trans pa.hρ,
        (G _ (by omega) (by omega)).trans pa.hqρ, (G _ (by omega) (by omega)).trans pa.hm,
        (G _ (by omega) (by omega)).trans pa.hk⟩
    · rw [G4 400 (by omega) (by omega)]; exact v400
    · rw [G4 403 (by omega) (by omega)]; exact v403
    · rw [G4 418 (by omega) (by omega)]; exact v418
    · rw [G4 424 (by omega) (by omega)]; exact v424
    · intro i hi; rw [A1]; exact ptab i hi
    · intro z' hz'
      simp only [AI]
      rw [hinvS z']
      have hz2 : z'.length = shortLength q t P.h := hz'
      simp only [hz2, true_and]
      rfl
    · intro u hu
      show _ ≤ q ^ P.ρ
      rw [AI, iINV u hu]
      split_ifs with hm
      · have h1 := List.idxOf_lt_length_of_mem hm
        have h2 := EncS.greedy_length_le q t P.ρ
        omega
      · omega
  have hout10 : s10.out = [] := by
    rw [show s10.out = s9.out by simp [hs10, dCheck], dout, out8]
  have hss : s = s10 := rfl
  rw [hss]
  refine ⟨⟨hctx, hout10, Or.inl ⟨rfl, v2⟩⟩, ?_, ?_, v10, ?_⟩
  · have e : (dC0 t).lenR t = 528 + 15 * t := by simp [dC0]; ring
    rw [e, vlen]
  · have e : (dC0 t).buf t = 15 + 5 * t := by simp [dC0]; ring
    rw [e]
    intro i hi
    have hiy : i < y.length := by rw [List.length_take] at hi; omega
    rw [show s10.arr (15 + 5 * t) (0 + i) = s9.arr (15 + 5 * t) (0 + i) by simp [HS.arr, m10],
      d1 i (by rw [List.length_take] at hi; omega), zero_add, hinp,
      inputAt_sub_one y i hiy, List.getElem_take]
  · have hco : (decPre q t).cost inp B s0 = (lit 1 1).cost inp B s0 +
        ((paramsW q t 0 1 100).cost inp B s1 + ((modulusW 102 200).cost inp B s2 +
        ((dSetA q).cost inp B s3 + ((powW 4 110 3).cost inp B s4 + ((dSetS t).cost inp B s5 +
        ((EncS.shortW q t (530 + 15 * t) (16 + 5 * t)).cost inp B s6 + ((dSetR t).cost inp B s7 +
        ((readW 270).cost inp B s8 + ((dCheck t).cost inp B s9 + 0))))))))) := rfl
    rw [hco]
    have c1 : (lit 1 1).cost inp B s0 ≤ κ := by simp only [cost_lit]; exact kb 1 (by omega)
    have wcost' : (powW 4 110 3).cost inp B s4 ≤ (2 * P.h₂ + 3) * κ := wcost
    have dcost' : (readW 270).cost inp B s8 ≤ (11 * (n + t + 1) + 6) * κ := dcost
    have pcost' : (paramsW q t 0 1 100).cost inp B s1 ≤
        paramsCost q t n * kappa B (RAM.bits (paramsBound q t n 1)) := pcost
    have mcost' : (modulusW 102 200).cost inp B s2 ≤ (2 ^ decB q t n + 1) ^ 2 * (44 * decB q t n + 90) *
        kappa B (RAM.bits ((2 ^ decB q t n + 4) * 2 ^ (2 * (decB q t n + 1)))) := mcost
    have icost' : (EncS.shortW q t (530 + 15 * t) (16 + 5 * t)).cost inp B s6 ≤
        EncS.shortCost B q t (parameters q t n).ρ (16 + 5 * t) := icost
    have e : (11 * n + 2 * P.h₂ + 11 * t + 60) * κ =
        (2 * P.h₂ + 3) * κ + (11 * (n + t + 1) + 6) * κ + 40 * κ := by ring
    have hpc : preCost q t n B = paramsCost q t n * kappa B (RAM.bits (paramsBound q t n 1)) +
      (2 ^ decB q t n + 1) ^ 2 * (44 * decB q t n + 90) *
        kappa B (RAM.bits ((2 ^ decB q t n + 4) * 2 ^ (2 * (decB q t n + 1)))) +
      EncS.shortCost B q t (parameters q t n).ρ (16 + 5 * t) +
      (11 * n + 2 * P.h₂ + 11 * t + 60) * κ := rfl
    rw [hpc, e]
    omega

end Top

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.decPre_spec_oai := @EditMulticoloring.Dev.Ram.decPre_spec_oai
