-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TPresMain.sl_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:49:15.747395+00:00
-- url     : https://prove2.me/submissions/ef461808-4c93-4375-aa0d-5ff43cfda3fb

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_HasDerivAtExt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.Q.TPresMain
theorem _root_.solution (hD : IsOpen D) {f f' : Mx k r → E} (hf : SmoothLev k r i D f)
    (h : ∀ x ∈ Glev k r i ∩ D, f x = f' x) : SmoothLev k r i D f' := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U ∩ D, F, hU.inter hD, ⟨hgU, hg₀.2⟩, hF.mono Set.inter_subset_left, fun g hg hgG => ?_⟩
  rw [← h g ⟨hgG, hg.2⟩]
  exact hfF g hg.1 hgG
end Formalism.FourierDecayAlt.Q.TPresMain
