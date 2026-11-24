-- Prove2me | solution 1 for Formalism.HermitianLattices.StabilizerLevels.PfB.congruenceTorsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:38:49.211875+00:00
-- url     : https://prove2.me/submissions/b89fca1a-0e45-4bc2-aba1-bf8549146156

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
import Theorems.Thm_Formalism_HermitianLattices_FiltrationBoundaryCriterion_congruence_powers
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
open NumberField IsDedekindDomain
open scoped TensorProduct
namespace Formalism.HermitianLattices.StabilizerLevels.PfB
theorem _root_.solution : CongruenceTorsion := by
  intro R _ I g k hg hgI hinf A hA N hN hAN
  obtain ⟨s, N', hN', hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' g hg.ne_one
  refine ⟨s, ?_⟩
  set Bm := A ^ (g ^ s) with hB
  have hBN : Bm ^ N' = 1 := by rw [hB, ← pow_mul, ← hNe, hAN]
  have hB1 : ∀ i j, (Bm - 1) i j ∈ I := fun i j =>
    Ideal.pow_le_self (Nat.succ_ne_zero s) (Formalism.HermitianLattices.FiltrationBoundaryCriterion.congruence_powers R I g k hgI A hA s i j)
  have hcop : Nat.Coprime g N' := (Nat.Prime.coprime_iff_not_dvd hg).2 hN'
  have hN'0 : 0 < N' := Nat.pos_of_ne_zero (by rintro rfl; exact hN' (dvd_zero _))
  have hfix : ∀ m : ℕ, Bm ^ (g ^ (N'.totient * m)) = Bm := by
    intro m
    have h1 : g ^ (N'.totient * m) ≡ 1 [MOD N'] := by
      rw [pow_mul]
      simpa using (Nat.ModEq.pow_totient hcop).pow m
    rw [pow_eq_pow_mod _ hBN, h1, ← pow_eq_pow_mod _ hBN, pow_one]
  have hz : ∀ i j, (Bm - 1) i j = 0 := by
    intro i j
    have : (Bm - 1) i j ∈ (⨅ m : ℕ, I ^ m) := by
      rw [Ideal.mem_iInf]
      intro m
      have h := Formalism.HermitianLattices.FiltrationBoundaryCriterion.congruence_powers R I g k hgI Bm hB1 (N'.totient * m) i j
      rw [hfix m] at h
      refine Ideal.pow_le_pow_right ?_ h
      have := Nat.totient_pos.2 hN'0
      nlinarith
    rw [hinf] at this
    simpa using this
  have : Bm - 1 = 0 := by ext i j; exact hz i j
  exact sub_eq_zero.1 this
end Formalism.HermitianLattices.StabilizerLevels.PfB
