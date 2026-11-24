-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TPresMain.eh_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:57:11.822222+00:00
-- url     : https://prove2.me/submissions/4cfeae24-83ec-46b8-b93c-8e624b6d57b3

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_HasDerivAtExt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_exp_first_hermitian_mem_level
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_exp_second_hermitian_mem_level
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_rdV_local

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresMain
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresLie
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.Q.TPresMain
theorem _root_.solution (hD : IsOpen D) (p q : Fin (mdim k r i)) (f f' : Mx k r → E)
    (h : ∀ x ∈ Glev k r i ∩ D, f x = f' x) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    EH k r (posL k r i p) (posL k r i q) f g = EH k r (posL k r i p) (posL k r i q) f' g := by
  simp only [EH, EabH]
  rw [rdV_local _ (exp_first_hermitian_mem_level p q) hD f f' h g hg, rdV_local _ (exp_second_hermitian_mem_level p q) hD f f' h g hg]
end Formalism.FourierDecayAlt.Q.TPresMain
