-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ETerm.fact_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:56.70981+00:00
-- url     : https://prove2.me/submissions/792efc5c-ec56-4583-b8cf-d152242b5a85

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormNatCastLeOfDvd
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_C_mul_right
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_eq_sum
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_sum_right
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.InvariantFactorPaths.G7.ETerm
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact jetPair_eq_sum jetPair_C_mul_right jetPair_sum_right)
namespace Formalism.InvariantFactorPaths.G7.ETerm
theorem _root_.solution {Φ κ : Type} [Fintype Φ] [Fintype κ] (k : Φ ⊕ κ ⊕ Fin 2 → ℕ) :
    (∑ x : κ, k (Sum.inr (Sum.inl x))).factorial ∣
      Nat.multinomial univ k * ∏ x : κ, (k (Sum.inr (Sum.inl x))).factorial := by
  have hs := Nat.multinomial_spec (univ : Finset (Φ ⊕ κ ⊕ Fin 2)) k
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at hs
  set A := ∏ φ : Φ, (k (Sum.inl φ)).factorial with hA
  set Bf := ∏ x : κ, (k (Sum.inr (Sum.inl x))).factorial with hBf
  set C2 := ∏ t : Fin 2, (k (Sum.inr (Sum.inr t))).factorial with hC2
  set sA := ∑ φ : Φ, k (Sum.inl φ) with hsA
  set sB := ∑ x : κ, k (Sum.inr (Sum.inl x)) with hsB
  set sC := ∑ t : Fin 2, k (Sum.inr (Sum.inr t)) with hsC
  have h1 : A ∣ sA.factorial := Nat.prod_factorial_dvd_factorial_sum _ _
  have h2 : C2 ∣ sC.factorial := Nat.prod_factorial_dvd_factorial_sum _ _
  have h3 : sB.factorial * sC.factorial ∣ (sB + sC).factorial :=
    Nat.factorial_mul_factorial_dvd_factorial_add _ _
  have h4 : sA.factorial * (sB + sC).factorial ∣ (sA + (sB + sC)).factorial :=
    Nat.factorial_mul_factorial_dvd_factorial_add _ _
  have h5 : A * (sB.factorial * C2) ∣ (sA + (sB + sC)).factorial :=
    (mul_dvd_mul h1 ((mul_dvd_mul (dvd_refl _) h2).trans h3)).trans h4
  rw [← hs] at h5
  have hpos : 0 < A * C2 :=
    Nat.mul_pos (Finset.prod_pos fun _ _ => Nat.factorial_pos _)
      (Finset.prod_pos fun _ _ => Nat.factorial_pos _)
  refine Nat.dvd_of_mul_dvd_mul_left hpos ?_
  have e1 : A * C2 * sB.factorial = A * (sB.factorial * C2) := by ring
  have e2 : A * C2 * (Nat.multinomial univ k * Bf) = A * (Bf * C2) * Nat.multinomial univ k := by
    ring
  rw [e1, e2]
  exact h5
end Formalism.InvariantFactorPaths.G7.ETerm
