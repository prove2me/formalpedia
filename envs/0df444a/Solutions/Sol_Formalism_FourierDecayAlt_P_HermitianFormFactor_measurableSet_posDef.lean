-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.measurableSet_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:42:20.971125+00:00
-- url     : https://prove2.me/submissions/81c994af-eec0-417d-8c1c-825ce6534d08

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Frame_mp
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_det_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_isClosed_posSemidef

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
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution : MeasurableSet {T : Q → Q → ℂ | (Matrix.of T).PosDef} := by
  have : {T : Q → Q → ℂ | (Matrix.of T).PosDef} =
      {T : Q → Q → ℂ | (Matrix.of T).PosSemidef} ∩ {T : Q → Q → ℂ | (Matrix.of T).det ≠ 0} := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨h.posSemidef, ((Matrix.isUnit_iff_isUnit_det _).mp h.isUnit).ne_zero⟩
    · rintro ⟨h1, h2⟩
      exact h1.posDef_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h2))
  rw [this]
  refine isClosed_posSemidef.measurableSet.inter ?_
  exact (isOpen_ne_fun det_cont continuous_const).measurableSet
end Formalism.FourierDecayAlt.P.HermitianFormFactor
