-- Prove2me | solution 1 for Formalism.L2.Th1.E.Ser.unitAt_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:24:00.233139+00:00
-- url     : https://prove2.me/submissions/2e485236-7d19-4c92-bfb4-ad5164f029c6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Finset
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.Ser
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.L2.Th1.E.Ser
theorem _root_.solution {k : ℕ} {f : K⟦X⟧} {a : K} (ha : ‖a‖ = 1) (hf : UnitAt k f) :
    UnitAt k (C a * f) := by
  obtain ⟨b, V, hb, hV, rfl⟩ := hf
  refine ⟨a * b, V, by rw [norm_mul, ha, hb, one_mul], hV, ?_⟩
  rw [map_mul]
  ring
end Formalism.L2.Th1.E.Ser
