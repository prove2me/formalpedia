-- Prove2me | solution 1 for Formalism.L2.Th1.E.Tor.nsmul_ptOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:27:23.646365+00:00
-- url     : https://prove2.me/submissions/578f323e-0d41-480c-a3a8-cb670af12833

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
variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
open Classical
namespace Formalism.L2.Th1.E.Tor
theorem _root_.solution (hA : PtOfAdd) (hZ : PtOfZero) (t : ℂ) (N : ℕ) :
    N • ptOf l L ι t = ptOf l L ι ((N : ℂ) * t) := by
  induction N with
  | zero =>
    rw [zero_nsmul, Nat.cast_zero, zero_mul]
    exact ((hZ l L ι 0).2 (zero_mem _)).symm
  | succ n ih =>
    rw [succ_nsmul, ih, ← hA]
    congr 1
    push_cast
    ring
end Formalism.L2.Th1.E.Tor
