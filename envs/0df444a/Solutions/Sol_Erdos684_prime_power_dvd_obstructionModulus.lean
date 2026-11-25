-- Prove2me | solution 1 for Erdos684.prime_power_dvd_obstructionModulus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:48:39.604608+00:00
-- url     : https://prove2.me/submissions/38d72131-482a-4064-8fba-46f203adcec6

module
public import Definitions.Def_Erdos684_Finite
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Definitions.Def_Erdos684_Lower

set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos684
namespace Erdos684
theorem _root_.solution {K p : ℕ} (hp : p.Prime) (hpk : p ≤ K) :
    p ^ (Nat.log p K + 1) ∣ obstructionModulus K := by
  have hd : p ^ Nat.log p K ∣ Nat.lcmUpto K :=
    (hp.pow_dvd_iff_le_factorization (Nat.lcmUpto_ne_zero K)).mpr (by
      rw [Nat.factorization_lcmUpto K hp])
  have hpdiv : p ∣ primorial K := hp.dvd_primorial_iff.mpr hpk
  simpa only [obstructionModulus, pow_succ] using mul_dvd_mul hd hpdiv
end Erdos684
