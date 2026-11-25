-- Prove2me | solution 1 for ConjCoord.Proof.octant_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:02:46.141812+00:00
-- url     : https://prove2.me/submissions/a5af243b-1781-4f0c-8d8d-0c1509fbdc25

module
public import Definitions.Def_ConjCoord_Compute
public import Definitions.Def_ConjCoord_TwoSquares
public import Definitions.Def_ConjCoord_Main
public import Theorems.Thm_ConjCoord_Proof_class_number_congruence

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution (S : SturmInput phi 512) {p : ℕ} [hpF : Fact p.Prime] (h5 : p % 16 = 5)
    {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) {h h' : ℕ}
    (hG : r3 p = 12 * h) (hG' : r3 (2 * p) = 12 * h')
    (hBerndt : 4 * ∑ x ∈ Icc 1 (p / 8), legendreSym p x = (h' : ℤ) - h) :
    ∑ x ∈ Icc 1 (p / 8), legendreSym p x ≡ 2 * octA b [ZMOD 4] := by
  have hc := class_number_congruence S hpF.out h5 hab hb hG hG'
  unfold Int.ModEq at *
  omega
end ConjCoord.Proof
