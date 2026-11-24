-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.slice_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:41:00.726415+00:00
-- url     : https://prove2.me/submissions/1578c6c1-20fa-4491-8a49-76f5c12aa467

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_qf_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Sl_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Kf_slice
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_qfT_cont

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
theorem _root_.solution {T : Q → Q → ℂ} (hT : (Matrix.of T).PosDef ∧ (Matrix.trace (Matrix.of T)).re ≤ 1) :
    0 < ∫⁻ B : Q → P → ℂ, Kf P Q 1 (T, B) := by
  rw [Kf_slice hT, lintegral_indicator_one (Sl_meas T 1)]
  have hopen : IsOpen {B : Q → P → ℂ | qf (Matrix.of T) (cm B) < 1} :=
    isOpen_lt (qfT_cont _) continuous_const
  have hne : {B : Q → P → ℂ | qf (Matrix.of T) (cm B) < 1}.Nonempty :=
    ⟨0, by show qf _ _ < 1; rw [qf_zero]; norm_num⟩
  refine lt_of_lt_of_le (hopen.measure_pos volume hne) (measure_mono ?_)
  intro B hB
  have hB' : qf (Matrix.of T) (cm B) < 1 := hB
  show qf _ _ ≤ _
  rw [one_pow]; exact hB'.le
end Formalism.FourierDecayAlt.P.HermitianFormFactor
