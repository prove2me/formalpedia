-- Prove2me | solution 1 for ConjCoord.Proof.desnoux_halves_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:56:15.545159+00:00
-- url     : https://prove2.me/submissions/a04cb5f4-a1cc-42d2-a3b4-e1bb67221fe7

module
public import Definitions.Def_ConjCoord_Compute
public import Definitions.Def_ConjCoord_TwoSquares
public import Definitions.Def_ConjCoord_Main
public import Theorems.Thm_ConjCoord_Proof_pell_even
public import Theorems.Thm_ConjCoord_Proof_pell2_even

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution {p : ℕ} (h5 : p % 16 = 5) {R S₀ R' S₀' : ℤ}
    (hPell : R ^ 2 - (p : ℤ) * S₀ ^ 2 = 1) (hPell' : R' ^ 2 - 2 * (p : ℤ) * S₀' ^ 2 = 1) :
    2 * (S₀ / 2) = S₀ ∧ 2 * (S₀' / 2) = S₀' :=
  ⟨Int.mul_ediv_cancel' (even_iff_two_dvd.1 (pell_even h5 hPell)),
    Int.mul_ediv_cancel' (even_iff_two_dvd.1 (pell2_even h5 hPell'))⟩
end ConjCoord.Proof
