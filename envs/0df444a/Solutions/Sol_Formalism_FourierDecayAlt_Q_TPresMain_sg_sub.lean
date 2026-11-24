-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TPresMain.sg_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:15:58.954818+00:00
-- url     : https://prove2.me/submissions/80e7d56e-c870-4cbb-bc1b-80c384e9d209

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
theorem _root_.solution {c d : Mx k r → ℂ} (hc : SmoothG k r i c) (hd : SmoothG k r i d) :
    SmoothG k r i (fun x => c x - d x) := by
  obtain ⟨c', hc', hcc⟩ := hc
  obtain ⟨d', hd', hdd⟩ := hd
  exact ⟨fun x => c' x - d' x, hc'.sub hd', fun x hx => by simp only [hcc x hx, hdd x hx]⟩
end Formalism.FourierDecayAlt.Q.TPresMain
