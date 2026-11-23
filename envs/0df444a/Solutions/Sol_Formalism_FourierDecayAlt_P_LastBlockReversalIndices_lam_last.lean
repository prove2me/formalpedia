-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LastBlockReversalIndices.lam_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:55.997716+00:00
-- url     : https://prove2.me/submissions/a7bda9b8-107a-4fce-9a63-3a41f95a28c1

import Definitions.Def_Formalism_HermitianCurvature_StatementA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondKernelPropertyKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LastBlockReversalIndices
open Formalism.DoubleCosetMeasures MeasureTheory
namespace Formalism.FourierDecayAlt.P.LastBlockReversalIndices
theorem _root_.solution {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (N : Fin n) (hN : N.val + 1 = n)
    (Z : Matrix (Fin n) (Fin n) K) :
    lamLin R Z (eLast R) = Submodule.Quotient.mk (Z⁻¹ N N) := by
  have hv : coeLin R (eLast R) = Pi.single N (1 : K) := by
    ext j
    simp only [coeLin, eLast, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Algebra.linearMap_apply, Pi.single_apply]
    by_cases h : j = N
    · subst h
      simp [hN]
    · have h' : ¬ (j.val + 1 = n) := fun e => h (Fin.ext (by omega))
      simp [h', h]
  have hlc : ∀ v : Fin n → K, lastCoord R v = v N := by
    intro v
    simp only [lastCoord, LinearMap.sum_apply]
    rw [Finset.sum_eq_single N]
    · simp [hN]
    · intro j _ hj
      have h' : ¬ (j.val + 1 = n) := fun e => hj (Fin.ext (by omega))
      simp [h']
    · simp
  simp only [lamLin, LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.restrictScalars_apply,
    Matrix.mulVecLin_apply, hv, hlc]
  congr 1
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]
end Formalism.FourierDecayAlt.P.LastBlockReversalIndices
