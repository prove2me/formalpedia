-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.entry_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:18:20.769012+00:00
-- url     : https://prove2.me/submissions/450e8968-7414-4818-b12e-1ac9f3d5dd5d

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor

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
theorem _root_.solution (C : Matrix P Q ℂ) (M : Matrix Q Q ℂ) (hC : ∑ i, ∑ j, Complex.normSq (C i j) ≤ 1)
    (hM : ∑ i, ∑ j, Complex.normSq (M i j) ≤ 1) (i : P) (j : Q) : ‖(C * M) i j‖ ≤ 1 := by
  have hn : ∀ z : ℂ, ‖z‖ ^ 2 = Complex.normSq z := fun z => by
    first
    | exact Complex.sq_norm z
    | exact (Complex.normSq_eq_norm_sq z).symm
  have hC' : ∑ l, ‖C i l‖ ^ 2 ≤ 1 := by
    rw [Finset.sum_congr rfl fun l _ => hn (C i l)]
    exact le_trans (Finset.single_le_sum (f := fun i => ∑ l, Complex.normSq (C i l))
      (fun i _ => Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _) (Finset.mem_univ i)) hC
  have hM' : ∑ l, ‖M l j‖ ^ 2 ≤ 1 := by
    rw [Finset.sum_congr rfl fun l _ => hn (M l j)]
    exact le_trans (Finset.sum_le_sum fun l _ => Finset.single_le_sum (f := fun j => Complex.normSq (M l j))
      (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ j)) hM
  have hx : ‖(C * M) i j‖ ≤ ∑ l, ‖C i l‖ * ‖M l j‖ := by
    rw [Matrix.mul_apply]
    exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun l _ => norm_mul _ _))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => ‖C i l‖) (fun l => ‖M l j‖)
  have h0a : 0 ≤ ∑ l, ‖C i l‖ ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  have h0b : 0 ≤ ∑ l, ‖M l j‖ ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  have hx0 : 0 ≤ ∑ l, ‖C i l‖ * ‖M l j‖ :=
    Finset.sum_nonneg fun l _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsq : (∑ l, ‖C i l‖ * ‖M l j‖) ^ 2 ≤ 1 := hcs.trans (by nlinarith)
  have hle : ∑ l, ‖C i l‖ * ‖M l j‖ ≤ 1 := by nlinarith
  exact hx.trans hle
end Formalism.FourierDecayAlt.P.HermitianFormFactor
