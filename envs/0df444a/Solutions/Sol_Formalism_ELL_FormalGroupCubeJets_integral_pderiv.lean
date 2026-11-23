-- Prove2me | solution 1 for Formalism.ELL.FormalGroupCubeJets.integral_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:41.334326+00:00
-- url     : https://prove2.me/submissions/811a7ea7-a887-41db-b824-19bc73a1d2fd

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsCube

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.FormalGroupCubeJets
open MvPowerSeries Formalism.G Formalism.G.LogCR Formalism.G.LogP
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]
namespace Formalism.ELL.FormalGroupCubeJets
theorem _root_.solution {σ : Type} (i : σ) {f : MvPowerSeries σ K} (hf : IntegralMv f) :
    IntegralMv (MvPowerSeries.pderiv K i f) := by
  classical
  intro d
  rw [coeff_pderiv, norm_mul]
  have h1 : ((d i : K) + 1) = ((d i + 1 : ℕ) : K) := by push_cast; rfl
  rw [h1]
  exact mul_le_one₀ (hf _) (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one K _)
end Formalism.ELL.FormalGroupCubeJets
