-- Prove2me | solution 1 for Formalism.REAL.dim_le_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:16:22.938798+00:00
-- url     : https://prove2.me/submissions/2d4248f0-f873-4cbe-abb3-a5e5394a8d9d

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CasComm
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnGroupSum
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IntegrableComplexContinuousBoundedSupport
import Theorems.Thm_Formalism_REAL_indefinite_unitary_inv_closed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped ContDiff ENNReal
set_option linter.unusedSimpArgs false
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    (n : ℝ) ≤ hs g := by
  have h1 := (indefinite_unitary_inv_closed n ε g hg).2
  have ht : Matrix.trace ((Jm ε * gᴴ * Jm ε) * g) = n := by rw [h1]; simp
  have hre : (n : ℝ) = (Matrix.trace ((Jm ε * gᴴ * Jm ε) * g)).re := by rw [ht]; simp
  have e : ∀ i j, (Jm ε * gᴴ * Jm ε) i j =
      (if ε i then 1 else -1) * star (g j i) * (if ε j then 1 else -1) := by
    intro i j
    simp [Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  rw [hre]
  generalize Jm ε * gᴴ * Jm ε = A at e
  unfold hs
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => ?_
  refine (Complex.re_le_norm _).trans ?_
  rw [e, norm_mul, norm_mul, norm_mul, norm_star]
  have n1 : ∀ b : Bool, ‖(if b = true then (1 : ℂ) else -1)‖ = 1 := by
    intro b; cases b <;> simp
  rw [n1, n1]
  ring_nf; rfl
end Formalism.REAL
