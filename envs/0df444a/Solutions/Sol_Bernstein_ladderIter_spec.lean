-- Prove2me | solution 1 for Bernstein.ladderIter_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-22T17:59:38.748789+00:00
-- url     : https://prove2.me/submissions/eaff758d-4aa7-40d7-8e85-2c7c34d79f92

import Mathlib
import Definitions.Def_Curve25519Bernstein
import Theorems.Thm_Bernstein_theorem_B_1
import Theorems.Thm_Bernstein_theorem_B_2
import Theorems.Thm_Bernstein_not_isSquare_two_and_disc

set_option autoImplicit false

namespace Bernstein.Ladder

theorem p25519_ge_five : 5 ≤ p25519 := by unfold p25519; norm_num

theorem a24_eq [Fact p25519.Prime] :
    (121665 : ZMod p25519) = (((A25519 : ℤ) : ZMod p25519) - 2) / 4 := by
  have h4 : (4 : ZMod p25519) ≠ 0 := by
    have : ((4 : ℕ) : ZMod p25519) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      unfold p25519 at this; norm_num at this
    exact_mod_cast this
  rw [eq_div_iff h4]; unfold A25519; push_cast; norm_num

theorem frac_one [Fact p25519.Prime] (q : ZMod p25519) :
    frac q 1 = some (emb p25519 q) := by
  simp [frac]

/-- One step of the ladder: doubling by Theorem B.1, differential addition by Theorem B.2. -/
theorem step_spec [Fact p25519.Prime] (q : ZMod p25519) (hq : q ≠ 0)
    (Q : Pt p25519 A25519) (hQ : X Q = some (emb p25519 q)) (P : Pt p25519 A25519) (b : Bool)
    (x z x' z' : ZMod p25519) (hxz : (x, z) ≠ (0, 0)) (hxz' : (x', z') ≠ (0, 0))
    (h : frac x z = X P) (h' : frac x' z' = X (P + Q)) :
    let st := ladderStep (121665 : ZMod p25519) q b (x, z, x', z')
    (st.1, st.2.1) ≠ (0, 0) ∧ (st.2.2.1, st.2.2.2) ≠ (0, 0) ∧
      frac st.1 st.2.1 = X (P + P + (if b then Q else 0)) ∧
      frac st.2.2.1 st.2.2.2 = X (P + P + (if b then Q else 0) + Q) := by
  have hp := p25519_ge_five
  have hA := (not_isSquare_two_and_disc).2.2
  have ha := a24_eq
  -- doubling of (x, z) and of (x', z')
  have D := theorem_B_1 p25519 hp A25519 hA x z hxz
  have D' := theorem_B_1 p25519 hp A25519 hA x' z' hxz'
  -- addition (x', z') + (x, z) with difference Q = q/1
  have S := theorem_B_2 p25519 hp A25519 hA x' z' x z q 1 hxz' hxz hq one_ne_zero
  dsimp only at D D' S
  obtain ⟨D1, D2, D3⟩ := D
  obtain ⟨D1', D2', D3'⟩ := D'
  obtain ⟨S1, S2, S3⟩ := S
  have hD := D3 P h.symm
  have hD' := D3' (P + Q) h'.symm
  have hS := S3 (P + Q) P h'.symm h.symm (by rw [frac_one, add_sub_cancel_left, hQ])
  rw [D1, D2, ← ha] at hD
  rw [D1', D2', ← ha] at hD'
  rw [S1, S2, mul_one] at hS
  cases b with
  | false =>
    simp only [ladderStep, Bool.false_eq_true, if_false, add_zero]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := hD.1; rwa [mul_comm ((x - z) ^ 2)] at this
    · exact hS.1
    · rw [two_nsmul] at hD; rw [hD.2, mul_comm ((x - z) ^ 2)]
    · rw [← hS.2]; congr 1; abel
  | true =>
    simp only [ladderStep, if_true]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hS.1
    · have := hD'.1; rwa [mul_comm ((x' - z') ^ 2)] at this
    · rw [← hS.2]; congr 1; abel
    · rw [two_nsmul] at hD'; rw [show P + P + Q + Q = P + Q + (P + Q) by abel, hD'.2, mul_comm ((x' - z') ^ 2)]

theorem div_two_pow_succ (n k : ℕ) :
    n / 2 ^ k = 2 * (n / 2 ^ (k + 1)) + (if n.testBit k then 1 else 0) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, pow_succ, ← Nat.div_div_eq_div_mul]
  have := Nat.div_add_mod (n / 2 ^ k) 2
  have h2 := Nat.mod_two_eq_zero_or_one (n / 2 ^ k)
  rcases h2 with h2 | h2 <;> simp [h2] <;> omega

theorem ladderIter_spec_dev [Fact p25519.Prime] (q : ZMod p25519) (hq : q ≠ 0)
    (Q : Pt p25519 A25519) (hQ : X Q = some (emb p25519 q)) (n k : ℕ)
    (x z x' z' : ZMod p25519) (hxz : (x, z) ≠ (0, 0)) (hxz' : (x', z') ≠ (0, 0))
    (h : frac x z = X (((n / 2 ^ k : ℕ) : ℤ) • Q))
    (h' : frac x' z' = X (((n / 2 ^ k : ℕ) : ℤ) • Q + Q)) :
    let st := ladderIter (121665 : ZMod p25519) q n k (x, z, x', z')
    (st.1, st.2.1) ≠ (0, 0) ∧ (st.2.2.1, st.2.2.2) ≠ (0, 0) ∧
      frac st.1 st.2.1 = X ((n : ℤ) • Q) ∧ frac st.2.2.1 st.2.2.2 = X ((n : ℤ) • Q + Q) := by
  induction k generalizing x z x' z' with
  | zero =>
    simp only [pow_zero, Nat.div_one] at h h'
    exact ⟨hxz, hxz', h, h'⟩
  | succ k ih =>
    have E := step_spec q hq Q hQ (((n / 2 ^ (k + 1) : ℕ) : ℤ) • Q) (n.testBit k)
      x z x' z' hxz hxz' h h'
    dsimp only at E
    obtain ⟨E1, E2, E3, E4⟩ := E
    have key : ((n / 2 ^ (k + 1) : ℕ) : ℤ) • Q + ((n / 2 ^ (k + 1) : ℕ) : ℤ) • Q +
        (if n.testBit k then Q else 0) = ((n / 2 ^ k : ℕ) : ℤ) • Q := by
      rw [div_two_pow_succ n k]
      cases n.testBit k <;> simp [add_smul, two_mul]
    rw [key] at E3 E4
    exact ih _ _ _ _ E1 E2 E3 E4

end Bernstein.Ladder

open Bernstein.Ladder in
theorem solution [Fact Bernstein.p25519.Prime] (q : ZMod Bernstein.p25519) (hq : q ≠ 0)
    (Q : Bernstein.Pt Bernstein.p25519 Bernstein.A25519)
    (hQ : Bernstein.X Q = some (Bernstein.emb Bernstein.p25519 q)) (n k : ℕ)
    (x z x' z' : ZMod Bernstein.p25519) (hxz : (x, z) ≠ (0, 0)) (hxz' : (x', z') ≠ (0, 0))
    (h : Bernstein.frac x z = Bernstein.X (((n / 2 ^ k : ℕ) : ℤ) • Q))
    (h' : Bernstein.frac x' z' = Bernstein.X (((n / 2 ^ k : ℕ) : ℤ) • Q + Q)) :
    let st := Bernstein.ladderIter (121665 : ZMod Bernstein.p25519) q n k (x, z, x', z')
    (st.1, st.2.1) ≠ (0, 0) ∧ (st.2.2.1, st.2.2.2) ≠ (0, 0) ∧
      Bernstein.frac st.1 st.2.1 = Bernstein.X ((n : ℤ) • Q) ∧
      Bernstein.frac st.2.2.1 st.2.2.2 = Bernstein.X ((n : ℤ) • Q + Q) :=
  ladderIter_spec_dev q hq Q hQ n k x z x' z' hxz hxz' h h'
