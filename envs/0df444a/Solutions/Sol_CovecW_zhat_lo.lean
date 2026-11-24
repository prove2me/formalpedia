-- Prove2me | solution 1 for CovecW.zhat_lo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:03:28.049215+00:00
-- url     : https://prove2.me/submissions/965d0ed0-8858-4eaa-b92b-e165dfdb677e

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianCovectors_HermBvecLeft

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open CovecW
open Formalism.QuantumDeterminants
namespace CovecW
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b : Fin r) :
    Zhat k r z z' g a.castSucc b.castSucc = herm (Hpk k r) (g *ᵥ bvec (eI k r b)) (bvec (eI k r a)) := by
  have ha : (a.castSucc : Fin (r + 1)).val < r := by simp
  have hb : (b.castSucc : Fin (r + 1)).val < r := by simp
  simp only [Zhat, fvec, dif_pos ha, dif_pos hb]
  rfl
end CovecW
