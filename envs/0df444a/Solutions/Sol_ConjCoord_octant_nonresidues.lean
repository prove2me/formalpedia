-- Prove2me | solution 1 for ConjCoord.octant_nonresidues
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:05:59.29238+00:00
-- url     : https://prove2.me/submissions/c2fb31cd-2515-4c3a-8d14-1a4f36a41d22

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_octant_nonresidues


set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord
namespace ConjCoord
theorem _root_.solution (S : SturmInput phi 512) {p : ℕ} [Fact p.Prime]
    (h5 : p % 16 = 5) {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) {h h' : ℕ}
    (hG : r3 p = 12 * h) (hG' : r3 (2 * p) = 12 * h')
    (hBerndt : 4 * ∑ x ∈ Icc 1 (p / 8), legendreSym p x = (h' : ℤ) - h) :
    (((Icc 1 (p / 8)).filter fun x : ℕ => legendreSym p (x : ℤ) = -1).card : ℤ) ≡
      ((p - 5) / 16 : ℕ) + octA b [ZMOD 2] :=
  Proof.octant_nonresidues S h5 hab hb hG hG' hBerndt
end ConjCoord
