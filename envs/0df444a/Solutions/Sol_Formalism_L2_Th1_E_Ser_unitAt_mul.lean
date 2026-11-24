-- Prove2me | solution 1 for Formalism.L2.Th1.E.Ser.unitAt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:24:01.047471+00:00
-- url     : https://prove2.me/submissions/1b511856-7e42-413d-a608-8b30abe8fb3d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Theorems.Thm_Formalism_L2_Th1_E_Ser_oneUnit_mul
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
theorem _root_.solution {j k : ℕ} {f g : K⟦X⟧} (hf : UnitAt j f) (hg : UnitAt k g) :
    UnitAt (j + k) (f * g) := by
  obtain ⟨a, V, ha, hV, rfl⟩ := hf
  obtain ⟨b, W, hb, hW, rfl⟩ := hg
  refine ⟨a * b, V * W, by rw [norm_mul, ha, hb, one_mul], oneUnit_mul hV hW, ?_⟩
  rw [map_mul, pow_add]
  ring
end Formalism.L2.Th1.E.Ser
