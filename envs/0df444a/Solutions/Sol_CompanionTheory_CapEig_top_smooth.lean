-- Prove2me | solution 1 for CompanionTheory.CapEig.top_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:54:16.360517+00:00
-- url     : https://prove2.me/submissions/81136e10-1481-4961-9186-8c726d80349e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_Smooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_Transport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open CompanionTheory CompanionTheory.CapEig
variable {n : ℕ} {ε : Fin n → Bool} {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace CompanionTheory.CapEig
theorem _root_.solution {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f) (u : ℂ) (a b : Fin n) :
    SmoothOnGV ε (Top (EabV ε) u a b f) := by
  unfold Formalism.QuantumDeterminants.Top
  by_cases hab : a = b
  · simp only [if_pos hab]
    exact io_smooth_add (io_smooth_smul u hf) (io_eab_smooth hf a b)
  · simp only [if_neg hab]
    exact io_smooth_add io_smooth_zero (io_eab_smooth hf a b)
end CompanionTheory.CapEig
