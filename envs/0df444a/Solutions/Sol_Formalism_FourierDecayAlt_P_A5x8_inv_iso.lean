-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.inv_iso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:38.088719+00:00
-- url     : https://prove2.me/submissions/448f99d8-a90d-418d-8757-d337b8ff2d2b

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_inv_orbZ
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_cokEquiv_eZ
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_cokEquiv_mk
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_lamLin_mul
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_liftR_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_lamLin_mk_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (w : Point K) (a : lowW K w.1 w.2) (ha : a ∈ intSub R (lowW K w.1 w.2))
    (b : upUniG K w.1.sum) (hb : b ∈ intSub R (upUniG K w.1.sum))
    (x : lowW K w.1 w.2) (y : upUniG K w.1.sum) :
    ∃ φ : coker R (orbZ w (x, y)) ≃ₗ[R] coker R (orbZ w (a * x, y * b)),
      φ ∈ isoZZ R (orbZ w (x, y)) (orbZ w (a * x, y * b)) := by
  rw [inv_orbZ]
  have haL : IsLowUni ((a : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) := a.2.1
  have hbU : IsUpUni ((b : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) := b.2
  have haI : IsInt R ((a : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) := ha.1
  have hbI : IsInt R ((b : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) := hb.1
  generalize ((a : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) = a0 at *
  generalize ((b : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) = b0 at *
  generalize orbZ w (x, y) = Z
  obtain ⟨A, rfl⟩ : ∃ A : Matrix (Fin w.1.sum) (Fin w.1.sum) R, A.map R.subtype = a0 :=
    ⟨Formalism.DoubleCosetMeasures.P.liftR R a0 haI, Formalism.DoubleCosetMeasures.P.liftR_map R a0 haI⟩
  obtain ⟨B, rfl⟩ : ∃ B : Matrix (Fin w.1.sum) (Fin w.1.sum) R, B.map R.subtype = b0 :=
    ⟨Formalism.DoubleCosetMeasures.P.liftR R b0 hbI, Formalism.DoubleCosetMeasures.P.liftR_map R b0 hbI⟩
  have hA := isLowUni_det K haL
  have hB := isUpUni_det K hbU
  refine ⟨Formalism.DoubleCosetMeasures.P.cokEquiv R A B Z hA hB, Formalism.DoubleCosetMeasures.P.cokEquiv_eZ R A B Z hA hB haL,
    fun v v' hv => ?_⟩
  rw [Formalism.DoubleCosetMeasures.P.cokEquiv_mk] at hv
  rw [← Formalism.FourierDecayAlt.P.A5x4.lamLin_mk_eq R _ hv, Formalism.DoubleCosetMeasures.P.lamLin_mul R A B Z hA hbU]
end Formalism.FourierDecayAlt.P.A5x8
