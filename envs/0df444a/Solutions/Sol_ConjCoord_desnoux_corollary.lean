-- Prove2me | solution 1 for ConjCoord.desnoux_corollary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:04:26.971662+00:00
-- url     : https://prove2.me/submissions/b50eb3a2-7f0f-4a33-926d-b921f446b09d

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_desnoux_corollary


set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord
namespace ConjCoord
theorem _root_.solution (S : SturmInput phi 512) {p : ℕ} (hp : p.Prime) (h5 : p % 16 = 5)
    {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) {h h' : ℕ}
    (hG : r3 p = 12 * h) (hG' : r3 (2 * p) = 12 * h') (c₂ R S₀ R' S₀' hplus hplus2 : ℤ)
    (hPell : R ^ 2 - (p : ℤ) * S₀ ^ 2 = 1) (hPell' : R' ^ 2 - 2 * (p : ℤ) * S₀' ^ 2 = 1)
    (hD : (h : ℤ) - c₂ * R * (S₀ / 2) * hplus + h' - 17 * R' * (S₀' / 2) * hplus2 ≡
      32 * (if p % 32 = 5 ∨ p % 32 = 29 then 1 else 0) [ZMOD 64]) :
    2 * (S₀ / 2) = S₀ ∧ 2 * (S₀' / 2) = S₀' ∧
      c₂ * R * (S₀ / 2) * hplus + 17 * R' * (S₀' / 2) * hplus2 ≡ 2 * h + 8 * octA b [ZMOD 16] :=
  Proof.desnoux_corollary S hp h5 hab hb hG hG' c₂ R S₀ R' S₀' hplus hplus2 hPell hPell' hD
end ConjCoord
