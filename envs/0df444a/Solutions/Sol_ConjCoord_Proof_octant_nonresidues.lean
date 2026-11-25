-- Prove2me | solution 1 for ConjCoord.Proof.octant_nonresidues
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:04:43.547648+00:00
-- url     : https://prove2.me/submissions/a7dd18ac-e91d-4b38-9765-983e85382b66

module
public import Definitions.Def_ConjCoord_Compute
public import Definitions.Def_ConjCoord_TwoSquares
public import Definitions.Def_ConjCoord_Main
public import Theorems.Thm_ConjCoord_Proof_octant_sum

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution (S : SturmInput phi 512) {p : ℕ} [hpF : Fact p.Prime]
    (h5 : p % 16 = 5) {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) {h h' : ℕ}
    (hG : r3 p = 12 * h) (hG' : r3 (2 * p) = 12 * h')
    (hBerndt : 4 * ∑ x ∈ Icc 1 (p / 8), legendreSym p x = (h' : ℤ) - h) :
    (((Icc 1 (p / 8)).filter fun x : ℕ => legendreSym p (x : ℤ) = -1).card : ℤ) ≡
      ((p - 5) / 16 : ℕ) + octA b [ZMOD 2] := by
  have hs := octant_sum S h5 hab hb hG hG' hBerndt
  have hval : ∀ x ∈ Icc 1 (p / 8), legendreSym p (x : ℤ) =
      1 - 2 * (if legendreSym p (x : ℤ) = -1 then 1 else 0) := by
    intro x hx
    rw [mem_Icc] at hx
    have hx0 : ((x : ℤ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro hd
      have : (p : ℤ) ≤ x := Int.le_of_dvd (by omega) hd
      have : p / 8 < p := Nat.div_lt_self hpF.out.pos (by norm_num)
      omega
    rcases legendreSym.eq_one_or_neg_one p hx0 with h1 | h1 <;> simp [h1]
  rw [sum_congr rfl hval, sum_sub_distrib, ← mul_sum, sum_boole] at hs
  simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel] at hs
  unfold Int.ModEq at *
  have : ((p / 8 : ℕ) : ℤ) = 2 * (((p - 5) / 16 : ℕ) : ℤ) := by omega
  rw [nsmul_eq_mul, mul_one] at hs
  omega
end ConjCoord.Proof
