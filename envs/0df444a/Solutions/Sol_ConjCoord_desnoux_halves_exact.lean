-- Prove2me | solution 1 for ConjCoord.desnoux_halves_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:58:10.781494+00:00
-- url     : https://prove2.me/submissions/2d55591f-5119-4734-badf-2f84c52789b8

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_desnoux_halves_exact


set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord
namespace ConjCoord
theorem _root_.solution {p : ℕ} (h5 : p % 16 = 5) {R S₀ R' S₀' : ℤ}
    (hPell : R ^ 2 - (p : ℤ) * S₀ ^ 2 = 1) (hPell' : R' ^ 2 - 2 * (p : ℤ) * S₀' ^ 2 = 1) :
    2 * (S₀ / 2) = S₀ ∧ 2 * (S₀' / 2) = S₀' :=
  Proof.desnoux_halves_exact h5 hPell hPell'
end ConjCoord
