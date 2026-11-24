-- Prove2me | solution 1 for Formalism.L2.Th1.E.Tor.gaussOne_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:24:02.533184+00:00
-- url     : https://prove2.me/submissions/9f5b3634-e8ea-4343-adad-25dd023249eb

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Taylor0ConstMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.F (opU sgStar th0 taylor0)
open Formalism.L2.Th1.B (fExp fLog)
open Formalism.L2.Th1.E.Tor
namespace Formalism.L2.Th1.E.Tor
theorem _root_.solution {K : Type} [NormedField K] {a : K} {f : K⟦X⟧} (ha : ‖a‖ = 1)
    (hf : GaussOne f) : GaussOne (C a * f) := by
  obtain ⟨h1, n, hn⟩ := hf
  refine ⟨fun m => ?_, n, ?_⟩
  · rw [coeff_C_mul, norm_mul, ha, one_mul]
    exact h1 m
  · rw [coeff_C_mul, norm_mul, ha, one_mul, hn]
end Formalism.L2.Th1.E.Tor
