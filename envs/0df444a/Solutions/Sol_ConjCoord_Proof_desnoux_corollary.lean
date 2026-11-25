-- Prove2me | solution 1 for ConjCoord.Proof.desnoux_corollary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:02:50.535286+00:00
-- url     : https://prove2.me/submissions/e077838e-5ad7-47aa-ae89-1dd6f601da99

module
public import Definitions.Def_ConjCoord_Compute
public import Definitions.Def_ConjCoord_TwoSquares
public import Definitions.Def_ConjCoord_Main
public import Theorems.Thm_ConjCoord_Proof_class_number_congruence
public import Theorems.Thm_ConjCoord_Proof_desnoux_halves_exact

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution (S : SturmInput phi 512) {p : ℕ} (hp : p.Prime) (h5 : p % 16 = 5)
    {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) {h h' : ℕ}
    (hG : r3 p = 12 * h) (hG' : r3 (2 * p) = 12 * h') (c₂ R S₀ R' S₀' hplus hplus2 : ℤ)
    (hPell : R ^ 2 - (p : ℤ) * S₀ ^ 2 = 1) (hPell' : R' ^ 2 - 2 * (p : ℤ) * S₀' ^ 2 = 1)
    (hD : (h : ℤ) - c₂ * R * (S₀ / 2) * hplus + h' - 17 * R' * (S₀' / 2) * hplus2 ≡
      32 * (if p % 32 = 5 ∨ p % 32 = 29 then 1 else 0) [ZMOD 64]) :
    2 * (S₀ / 2) = S₀ ∧ 2 * (S₀' / 2) = S₀' ∧
      c₂ * R * (S₀ / 2) * hplus + 17 * R' * (S₀' / 2) * hplus2 ≡ 2 * h + 8 * octA b [ZMOD 16] := by
  refine ⟨(desnoux_halves_exact h5 hPell hPell').1, (desnoux_halves_exact h5 hPell hPell').2, ?_⟩
  have hc := class_number_congruence S hp h5 hab hb hG hG'
  unfold Int.ModEq at *
  split_ifs at hD <;> omega
end ConjCoord.Proof
