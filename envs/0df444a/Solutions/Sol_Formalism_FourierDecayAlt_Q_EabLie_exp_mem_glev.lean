-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabLie.exp_mem_glev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:06:46.209477+00:00
-- url     : https://prove2.me/submissions/245e0773-2d37-4944-babe-90f294bfdca9

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DerivativePreservation_HasDerivAtExt
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_skew_real
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_exp_mem_UH
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_exp_fix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabLie
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.EabLie
theorem _root_.solution (i : Fin (r + 1)) (X : Mx k r) (hX : Xᴴ = -(Hpk k r * X * Hpk k r))
    (hc : ∀ a : Fin r, a.val < i.val → ∀ x, X x (eI k r a) = 0 ∧ X x (esI k r a) = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i := by
  refine ⟨exp_mem_UH _ (skew_real X hX t), fun a ha => ⟨?_, ?_⟩⟩
  · exact exp_fix _ _ (fun x => by rw [Matrix.smul_apply, (hc a ha x).1, smul_zero])
  · exact exp_fix _ _ (fun x => by rw [Matrix.smul_apply, (hc a ha x).2, smul_zero])
end Formalism.FourierDecayAlt.Q.EabLie
