-- Prove2me | solution 1 for Formalism.L2.Th1.E.Ser.unitAt_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:09:40.697012+00:00
-- url     : https://prove2.me/submissions/88976c53-4114-49fe-880c-7c5bccf03915

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Theorems.Thm_Formalism_L2_Th1_E_Ser_oneUnit_pow

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
theorem _root_.solution {k : ℕ} {f : K⟦X⟧} (hf : UnitAt k f) (n : ℕ) : UnitAt (k * n) (f ^ n) := by
  obtain ⟨a, V, ha, hV, rfl⟩ := hf
  refine ⟨a ^ n, V ^ n, by rw [norm_pow, ha, one_pow], oneUnit_pow hV n, ?_⟩
  rw [map_pow, pow_mul, mul_pow, mul_pow]
end Formalism.L2.Th1.E.Ser
