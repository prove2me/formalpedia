-- Prove2me | solution 1 for Formalism.L2.Th1.E.Ser.unitAt_gaussOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:08:43.8518+00:00
-- url     : https://prove2.me/submissions/556a4124-8559-4e89-bedd-8bbc9a281fe1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Theorems.Thm_Formalism_L2_Th1_E_Ser_unitAt_intS

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
theorem _root_.solution {k : ℕ} {f : K⟦X⟧} (hf : UnitAt k f) : GaussOne f := by
  refine ⟨unitAt_intS hf, k, ?_⟩
  obtain ⟨a, V, ha, hV, rfl⟩ := hf
  have : coeff (0 + k) (X ^ k * V) = coeff 0 V := coeff_X_pow_mul V k 0
  rw [mul_assoc, coeff_C_mul, norm_mul, ha, one_mul]
  rw [zero_add, coeff_zero_eq_constantCoeff_apply, hV.1] at this
  rw [this, norm_one]
end Formalism.L2.Th1.E.Ser
