-- Prove2me | solution 1 for Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfM.congruencePowers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:55:38.889803+00:00
-- url     : https://prove2.me/submissions/6d39329d-1f74-4621-9536-6c32b20eaff2

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_OrbitPointsDistinct
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_BehrendSets_TranslateMean
import Definitions.Def_Formalism_BehrendSets_FinalE
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.FiltrationBoundaryCriterion
open Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfM
open Formalism.HermitianLattices.FiltrationBoundaryCriterion Formalism.FrobeniusOrbits NumberField Ideal
namespace Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfM
theorem _root_.solution : CongruencePowers := by
  intro R _ I g k hg A hA m

  have hmul : ∀ (a b : ℕ) (X Y : Matrix (Fin k) (Fin k) R), (∀ i j, X i j ∈ I ^ a) →
      (∀ i j, Y i j ∈ I ^ b) → ∀ i j, (X * Y) i j ∈ I ^ (a + b) := by
    intro a b X Y hX hY i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => by rw [pow_add]; exact Ideal.mul_mem_mul (hX i l) (hY l j)
  induction m with
  | zero => simpa using hA
  | succ m ih =>
    set B := A ^ g ^ m with hB
    have hBI : ∀ i j, (B - 1) i j ∈ I := fun i j => Ideal.pow_le_self (by omega) (ih i j)
    have hpow : ∀ n : ℕ, ∀ i j, (B ^ n - 1) i j ∈ I := by
      intro n
      induction n with
      | zero => intro i j; simp
      | succ n ihn =>
        intro i j
        have : B ^ (n + 1) - 1 = (B ^ n - 1) * (B - 1) + (B ^ n - 1) + (B - 1) := by
          rw [pow_succ]; noncomm_ring
        rw [this]
        refine I.add_mem (I.add_mem ?_ (ihn i j)) (hBI i j)
        have := hmul 1 1 _ _ (by simpa using ihn) (by simpa using hBI) i j
        exact Ideal.pow_le_self (by omega) this
    have hgeom : B ^ g - 1 = (B - 1) * ∑ n ∈ Finset.range g, B ^ n := by
      have := (Commute.one_right B).mul_geom_sum₂ g
      simpa using this.symm
    have hsum : ∀ i j, (∑ n ∈ Finset.range g, B ^ n) i j ∈ I ^ 1 := by
      intro i j
      have : (∑ n ∈ Finset.range g, B ^ n) = (∑ n ∈ Finset.range g, (B ^ n - 1)) + (g : R) • 1 := by
        rw [Finset.sum_sub_distrib]; simp [Matrix.smul_one_eq_diagonal, nsmul_eq_mul]
        ext i j; simp [Matrix.natCast_apply, Matrix.diagonal_apply]
      rw [this, pow_one, Matrix.add_apply, Matrix.sum_apply]
      refine I.add_mem (Ideal.sum_mem _ fun n _ => hpow n i j) ?_
      rw [Matrix.smul_apply]
      exact I.mul_mem_right _ hg
    intro i j
    have e1 : A ^ g ^ (m + 1) = B ^ g := by rw [hB, ← pow_mul, pow_succ]
    rw [e1, hgeom]
    exact hmul (m + 1) 1 _ _ ih hsum i j
end Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfM
