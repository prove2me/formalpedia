-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TPresMain.qminor_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:28:32.160807+00:00
-- url     : https://prove2.me/submissions/184cc78c-14ad-43ce-b062-e7105aded442

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_HasDerivAtExt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_iteratedOperator_clm_comp
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_qminor_eq

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
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.Q.TPresMain
theorem _root_.solution (hD : IsOpen D) {t : ℕ} (α β : Fin t → Fin (mdim k r i)) (u : ℂ)
    (L : E →L[ℂ] E') (f : Mx k r → E) (hf : SmoothLev k r i D f) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    qminorOp (EH k r) (fun j => posL k r i (α j)) (fun j => posL k r i (β j)) u (fun y => L (f y)) g =
      L (qminorOp (EH k r) (fun j => posL k r i (α j)) (fun j => posL k r i (β j)) u f g) := by
  rw [qminor_eq, qminor_eq]
  simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [iteratedOperator_clm_comp hD _ L f hf g hg]
end Formalism.FourierDecayAlt.Q.TPresMain
