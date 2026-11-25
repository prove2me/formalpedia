-- Prove2me | solution 1 for ConjCoord.Proof.reps_congruence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:00:41.95368+00:00
-- url     : https://prove2.me/submissions/7e51a3f8-f556-4499-a0c5-261e20c752fc

module
public import Definitions.Def_ConjCoord_Compute
public import Definitions.Def_ConjCoord_TwoSquares
public import Definitions.Def_ConjCoord_Main
public import Theorems.Thm_ConjCoord_Proof_tCoeff_dvd
public import Theorems.Thm_ConjCoord_Proof_gCount_prime


set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution (S : SturmInput phi 512) {p : ℕ} (hp : p.Prime) (h5 : p % 16 = 5)
    {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) :
    2 * (reps 1 2 4 p : ℤ) - reps 1 2 2 p ≡ 32 * octA b [ZMOD 64] := by
  have hT := tCoeff_dvd S p
  have hG := gCount_prime hp h5 hab hb
  unfold tCoeff at hT
  rw [if_pos h5] at hT
  unfold Int.ModEq at *
  omega
end ConjCoord.Proof
