-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.ball_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:58:30.745251+00:00
-- url     : https://prove2.me/submissions/04f55e8e-1917-4ffd-9fad-23a17c1abfb3

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_HermitianFormFactor_gN_sq__f8e7b367e001

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
attribute [local instance] isAddHaarMeasure_matrix_volume
attribute [local instance] haar_prod2
open scoped Pointwise
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution {k r : ℕ} {c : ℝ} (hc : 1 ≤ c) {g : Mt k r} (h : gN (Matrix.of g) ^ 2 ≤ c) : ‖g‖ ≤ c := by
  have hc0 : 0 ≤ c := by linarith
  rw [gN_sq'] at h
  refine (pi_norm_le_iff_of_nonneg hc0).2 fun i => (pi_norm_le_iff_of_nonneg hc0).2 fun j => ?_
  have h1 : Complex.normSq (g i j) ≤ ∑ i, ∑ j, Complex.normSq (Matrix.of g i j) :=
    le_trans (Finset.single_le_sum (f := fun j => Complex.normSq (Matrix.of g i j))
        (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ j))
      (Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (Matrix.of g i j))
        (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i))
  have h2 : ‖g i j‖ ^ 2 ≤ c := by
    have h3 : ‖g i j‖ ^ 2 = Complex.normSq (g i j) := by
      first
      | exact Complex.sq_norm _
      | exact (Complex.normSq_eq_norm_sq _).symm
    rw [h3]; linarith
  nlinarith [norm_nonneg (g i j), mul_le_mul_of_nonneg_left hc hc0]
end Formalism.FourierDecayAlt.P.HermitianFormFactor
