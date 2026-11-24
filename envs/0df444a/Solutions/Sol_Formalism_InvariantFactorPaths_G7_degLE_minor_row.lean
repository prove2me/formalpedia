-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.degLE_minor_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:43:33.425953+00:00
-- url     : https://prove2.me/submissions/83e1f14f-9d19-4eb3-bde1-eb0592d34d78

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_X_of_notMem
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_det_rankOne
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_CC
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_shiftPoly_minorAt
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key


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
open Formalism.DworkPowerSeriesWeights (jetPair)
variable {K σ κ : Type} [Field K] [DecidableEq σ] [Fintype κ]
variable {r0 r1 l : ℕ} (s : σ) (T : Fin l → Fin r0 → K) (I : Fin l → Fin r1) (pos : κ → σ)
  (ξ : κ → Fin r0 → K) (col : κ → Fin r1)
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (W : Finset κ) (ξ0 : Fin r0 → K) (hW : ∀ k ∈ W, ξ k = ξ0) :
    degLE W 1 (shiftPoly (fun k => colDir (pos k) (ξ k) (col k)) (minorAt s T I)) := by
  classical
  rw [shiftPoly_minorAt]
  set φ : K →+* MvPolynomial κ (MvPolynomial (σ × Fin r0 × Fin r1) K) :=
    (MvPolynomial.C).comp MvPolynomial.C with hφ
  have key := degLE_det_rankOne (W := W) φ (fun a => degLE_CC W a)
    (Matrix.of fun (i c : Fin l) => ∑ a, MvPolynomial.C (MvPolynomial.C (T i a)) *
      (MvPolynomial.C (MvPolynomial.X (s, a, I c)) + ∑ k ∈ Wᶜ,
        MvPolynomial.C (MvPolynomial.C (colDir (pos k) (ξ k) (col k) (s, a, I c))) *
          MvPolynomial.X k))
    (fun i => ∑ a, T i a * ξ0 a)
    (fun c => ∑ k ∈ W, MvPolynomial.C (MvPolynomial.C (if s = pos k ∧ I c = col k then 1 else 0)) *
      MvPolynomial.X k)
    (fun i c => by
      simp only [Matrix.of_apply]
      refine degLE_sum _ _ fun a _ => ?_
      have := degLE_mul (degLE_CC W (ι := σ × Fin r0 × Fin r1) (T i a))
        (degLE_add (degLE_C W (MvPolynomial.X (s, a, I c))) (degLE_sum Wᶜ (fun k =>
          MvPolynomial.C (MvPolynomial.C (colDir (pos k) (ξ k) (col k) (s, a, I c))) *
          MvPolynomial.X k) fun k hk => by
            simpa using degLE_mul (degLE_CC W (K := K) (ι := σ × Fin r0 × Fin r1) _)
              (degLE_X_of_notMem (Finset.mem_compl.mp hk))))
      simpa using this)
    (fun c => degLE_sum _ _ fun k _ => by
      have := degLE_mul (degLE_CC W (K := K) (ι := σ × Fin r0 × Fin r1)
        (if s = pos k ∧ I c = col k then 1 else 0)) (degLE_X W k)
      rwa [zero_add] at this)
  convert key using 2
  refine Matrix.ext fun i c => ?_
  simp only [Matrix.of_apply, shiftGen]
  rw [hφ, RingHom.comp_apply, map_sum, map_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_sum_compl W, Finset.mul_sum, mul_add, mul_add, mul_add, Finset.mul_sum,
    Finset.mul_sum]
  have : ∀ k ∈ W, MvPolynomial.C (MvPolynomial.C (T i a)) *
      (MvPolynomial.C (MvPolynomial.C (colDir (pos k) (ξ k) (col k) (s, a, I c))) *
        MvPolynomial.X k) =
      (MvPolynomial.C (MvPolynomial.C (T i a * ξ0 a)) *
        (MvPolynomial.C (MvPolynomial.C (if s = pos k ∧ I c = col k then 1 else 0)) *
          MvPolynomial.X k) : MvPolynomial κ (MvPolynomial (σ × Fin r0 × Fin r1) K)) := by
    intro k hk
    unfold colDir
    simp only [hW k hk]
    split_ifs
    · simp only [map_mul, map_one]
      ring
    · simp
  rw [Finset.sum_congr rfl this]
  ring
end Formalism.InvariantFactorPaths.G7
