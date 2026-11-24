-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.poc_powSmul_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:43.491989+00:00
-- url     : https://prove2.me/submissions/8d54f15a-1101-4943-ae0f-698f6ff5a987

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PrimitiveOfPCycle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open scoped Pointwise
namespace Formalism.GaloisIrreducibility
theorem _root_.solution {M Y : Type*} [Group M] [MulAction M Y] (s : M) (p : ℕ) (hp : p.Prime)
    (hs : s ^ p = 1) (y : Y) (hy : s • y ≠ y) :
    ∀ i < p, ∀ j < p, s ^ i • y = s ^ j • y → i = j := by
  have key : ∀ d : ℕ, 0 < d → d < p → s ^ d • y ≠ y := by
    intro d hd0 hdp hd
    have hnd : ¬ p ∣ d := fun h => absurd (Nat.le_of_dvd hd0 h) (by omega)
    have hcop : Nat.Coprime d p := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)
    have h1 : s ^ d ∈ MulAction.stabilizer M y := MulAction.mem_stabilizer_iff.mpr hd
    have h2 : s ^ p ∈ MulAction.stabilizer M y := by rw [hs]; exact one_mem _
    have hb := Nat.gcd_eq_gcd_ab d p
    rw [hcop.gcd_eq_one] at hb
    have e : s = (s ^ d) ^ (Nat.gcdA d p) * (s ^ p) ^ (Nat.gcdB d p) := by
      rw [← zpow_natCast s d, ← zpow_natCast s p, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hb,
        Nat.cast_one, zpow_one]
    have h3 : s ∈ MulAction.stabilizer M y := by
      rw [e]; exact mul_mem (zpow_mem h1 _) (zpow_mem h2 _)
    exact hy (MulAction.mem_stabilizer_iff.mp h3)
  have step : ∀ i j : ℕ, i < j → j < p → s ^ i • y = s ^ j • y → False := by
    intro i j hij hjp h
    apply key (j - i) (by omega) (by omega)
    have h' : s ^ i • (s ^ (j - i) • y) = s ^ i • y := by
      rw [smul_smul, ← pow_add, show i + (j - i) = j by omega]
      exact h.symm
    exact (smul_left_cancel_iff _).mp h'
  intro i hi j hj hij
  rcases lt_trichotomy i j with h | h | h
  · exact (step i j h hj hij).elim
  · exact h
  · exact (step j i h hi hij.symm).elim
end Formalism.GaloisIrreducibility
