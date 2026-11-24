-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TPresMain.sl_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:38:11.24788+00:00
-- url     : https://prove2.me/submissions/7e20128d-25da-4f12-8ce0-9a420bcbc7c3

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
theorem _root_.solution {f f' : Mx k r → E} (hf : SmoothLev k r i D f) (hf' : SmoothLev k r i D f') :
    SmoothLev k r i D (f + f') := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g₀ hg₀
  refine ⟨U ∩ U', fun x => F x + F' x, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right), fun g hg hgG => ?_⟩
  simp only [Pi.add_apply, hfF g hg.1 hgG, hfF' g hg.2 hgG]
end Formalism.FourierDecayAlt.Q.TPresMain
