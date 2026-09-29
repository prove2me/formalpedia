-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.HasKernelOfDegree.eq_of_pow_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/38613989-6473-557b-a9a5-974bfea53f1f

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_eq_of_pow_of_pow

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem solution
    {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] [Nontrivial B] {φ : Series B} {h h' : ℕ}
    (hh : FormalODModule.HasKernelOfDegree φ (p ^ h)) (hh' : FormalODModule.HasKernelOfDegree φ (p ^ h')) :
    h = h' := by
  classical
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal B
  letI : Field (B ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have e1 := hh.2.2 (B ⧸ 𝔪) (Ideal.Quotient.mk 𝔪)
  have e2 := hh'.2.2 (B ⧸ 𝔪) (Ideal.Quotient.mk 𝔪)
  have hp : p ^ h = p ^ h' := e1.symm.trans e2
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le hp

end S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_eq_of_pow_of_pow
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_eq_of_pow_of_pow (solution)
