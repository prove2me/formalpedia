-- Prove2me | solution 1 for Formalism.L2.KerInert.VC.intPS_wSer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:40:17.337804+00:00
-- url     : https://prove2.me/submissions/dc6dcaec-6f24-456c-a33d-93668beb11c9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
import Definitions.Def_Formalism_LocalToGlobal_InertKernelTheory_InertCoprimeLemmas_VarChange
import Theorems.Thm_Formalism_L2_Th1_A_seriesMap


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
open Formalism Formalism.L2 Formalism.L2.KerInert Formalism.L2.KerInert.VC
open Formalism.L2.Th1.A
open Formalism.L2.Th1.C
variable {K : Type} [Field K] [CharZero K] (R' : Subring K)
namespace Formalism.L2.KerInert.VC
theorem _root_.solution {W : WeierstrassCurve K} (hW : CoeffIn R' W) : IntPS R' (wSer W) := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  let WS : WeierstrassCurve R' := ⟨⟨_, h1⟩, ⟨_, h2⟩, ⟨_, h3⟩, ⟨_, h4⟩, ⟨_, h6⟩⟩
  have e : WS.map R'.subtype = W := by ext <;> rfl
  intro n
  rw [← e, ← (seriesMap R' K R'.subtype WS).1, coeff_map]
  exact SetLike.coe_mem _
end Formalism.L2.KerInert.VC
