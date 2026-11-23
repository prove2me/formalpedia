-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AveragedKernelSums.thx_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:55.455393+00:00
-- url     : https://prove2.me/submissions/85255cf8-db79-4290-aef1-86b7d4a15a4b

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedKernelSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_psi_R

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.AveragedKernelSums
open Formalism.FourierDecayAlt.P.A5x6
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.AveragedKernelSums
theorem _root_.solution (hD : LocalDatum K R ψ) (m : ℕ) (A B : Finset K) (τ : K → Kˣ)
    (cr : K ⧸ R.toAddSubgroup → Kˣ) (hB : ∀ b ∈ B, b ∈ R) (z r : K) (hr : r ∈ R) :
    thx R ψ m cr A B τ (z + r) = thx R ψ m cr A B τ z := by
  have h1 : ∀ b ∈ B, ψ (-((z + r) * b)) = ψ (-(z * b)) := by
    intro b hb
    have : ψ (-(r * b)) = 1 := psi_R hD (R.neg_mem (R.mul_mem hr (hB b hb)))
    have e : -((z + r) * b) = -(z * b) + (-(r * b)) := by ring
    rw [e, AddChar.map_add_eq_mul, this, mul_one]
  funext h h'
  unfold thx
  congr 1
  refine Finset.sum_congr rfl fun ρ _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun b' hb' => ?_
  rw [h1 b hb, h1 b' hb']
end Formalism.FourierDecayAlt.P.AveragedKernelSums
