-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.Phh_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:15:41.661017+00:00
-- url     : https://prove2.me/submissions/05612684-ef81-4d1a-8cef-c85ebe2257ed

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplLen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolynomialBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfUnitWords
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_hh_cd
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_hh_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    ∃ B : ℝ, ∀ z ∈ {z : ℂ | ε ≤ z.re}, ‖iteratedFDeriv ℝ j (Phh ε) z‖ ≤ B := by
  refine ⟨‖Complex.ofRealCLM‖ * (|(descPochhammer ℝ j).eval (-(1 / 2 : ℝ))| * ε ^ (-(1 / 2 : ℝ) - j) *
    ‖Complex.reCLM‖ ^ j), fun z hz => ?_⟩
  have hh' : ContDiff ℝ ∞ (hh ε ∘ Complex.reCLM) := (hh_cd hε).comp Complex.reCLM.contDiff
  have e : Phh ε = Complex.ofRealCLM ∘ (hh ε ∘ Complex.reCLM) := rfl
  rw [e]
  calc ‖iteratedFDeriv ℝ j (Complex.ofRealCLM ∘ (hh ε ∘ Complex.reCLM)) z‖
      ≤ ‖Complex.ofRealCLM‖ * ‖iteratedFDeriv ℝ j (hh ε ∘ Complex.reCLM) z‖ :=
        by
          first
          | exact Complex.ofRealCLM.norm_iteratedFDeriv_comp_left hh'.contDiffAt (by exact_mod_cast le_top)
          | exact Complex.ofRealCLM.norm_iteratedFDeriv_comp_left hh' z (by exact_mod_cast le_top)
          | exact Complex.ofRealCLM.norm_iteratedFDeriv_comp_left hh'.contDiffAt z (by exact_mod_cast le_top)
    _ ≤ _ := by
        gcongr
        calc ‖iteratedFDeriv ℝ j (hh ε ∘ Complex.reCLM) z‖
            = ‖(iteratedFDeriv ℝ j (hh ε) (Complex.reCLM z)).compContinuousLinearMap
                fun _ => Complex.reCLM‖ := by
              first
              | rw [Complex.reCLM.iteratedFDeriv_comp_right (hh_cd hε) z (by exact_mod_cast le_top)]
              | rw [Complex.reCLM.iteratedFDeriv_comp_right (hh_cd hε).contDiffAt (by exact_mod_cast le_top)]
              | rw [Complex.reCLM.iteratedFDeriv_comp_right (hh_cd hε) (by exact_mod_cast le_top)]
          _ ≤ ‖iteratedFDeriv ℝ j (hh ε) (Complex.reCLM z)‖ * ∏ _i : Fin j, ‖Complex.reCLM‖ :=
              ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
          _ = ‖iteratedFDeriv ℝ j (hh ε) (Complex.reCLM z)‖ * ‖Complex.reCLM‖ ^ j := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          _ ≤ _ := by
              gcongr
              exact hh_bound hε j hz
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
