-- Prove2me | solution 1 for Formalism.HermitianLattices.StabilizerLevels.PfB.sqf3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:17:27.723843+00:00
-- url     : https://prove2.me/submissions/b41c2fae-3c15-49d4-a5d0-cf643ff9ea34

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_CongruenceTorsion
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CongruenceSubgroupTorsionFree
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_pow
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.StabilizerLevels
open Formalism.HermitianLattices.StabilizerLevels.PfB
open NumberField IntermediateField
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.HermitianLattices.StabilizerLevels.PfB
theorem _root_.solution (q d : ℕ) (h : HypOdd q d) (i1 i2 i3 : ℕ) (h1 : i1 ≤ 1) (h2 : i2 ≤ 1) (h3 : i3 ≤ 1) :
    Squarefree ((2 : ℤ) ^ i3 * (-(q : ℤ)) ^ i1 * (-(d : ℤ)) ^ i2) := by
  obtain ⟨hq, hd, hqd, hq2, hd2⟩ := h
  rw [← Int.squarefree_natAbs]
  have e : ((2 : ℤ) ^ i3 * (-(q : ℤ)) ^ i1 * (-(d : ℤ)) ^ i2).natAbs = 2 ^ i3 * q ^ i1 * d ^ i2 := by
    simp [Int.natAbs_mul, Int.natAbs_pow]
  rw [e]
  have hp : ∀ p : ℕ, p.Prime → ∀ i : ℕ, i ≤ 1 → Squarefree (p ^ i) := by
    intro p hp i hi
    interval_cases i
    · simp
    · simpa using hp.prime.squarefree
  have c1 : Nat.Coprime (2 ^ i3) (q ^ i1) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hq).2 (Ne.symm hq2))
  have c2 : Nat.Coprime (2 ^ i3 * q ^ i1) (d ^ i2) :=
    Nat.Coprime.mul_left (Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hd).2 (Ne.symm hd2)))
      (Nat.Coprime.pow _ _ ((Nat.coprime_primes hq hd).2 hqd))
  rw [Nat.squarefree_mul c2, Nat.squarefree_mul c1]
  exact ⟨⟨hp 2 Nat.prime_two i3 h3, hp q hq i1 h1⟩, hp d hd i2 h2⟩
end Formalism.HermitianLattices.StabilizerLevels.PfB
