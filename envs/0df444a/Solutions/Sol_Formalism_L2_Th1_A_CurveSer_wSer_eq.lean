-- Prove2me | solution 1 for Formalism.L2.Th1.A.CurveSer.wSer_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:16.800667+00:00
-- url     : https://prove2.me/submissions/fae24b10-1e81-4b2f-a400-c73a1cf499fc

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_wSer_fixed
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_wSer_cc
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open PowerSeries
universe u v
noncomputable section
namespace Formalism.L2.Th1.A
namespace CurveSer
section Tools
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
end Tools
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
private theorem exists_wSer_eq_X_cube_mul : ∃ v : R⟦X⟧, wSer W = X ^ 3 * v := by
  have hfix := (wSer_fixed W).2
  obtain ⟨v1, hv1⟩ := (PowerSeries.X_dvd_iff).mpr (wSer_cc W)
  obtain ⟨v2, hv2⟩ : X ^ 2 ∣ wSer W := ⟨X + C W.a₁ * v1 + C W.a₂ * X * v1 + C W.a₃ * v1 ^ 2
      + C W.a₄ * X * v1 ^ 2 + C W.a₆ * X * v1 ^ 3, by rw [hfix, hv1]; ring⟩
  exact ⟨1 + C W.a₁ * v2 + C W.a₂ * X * v2 + C W.a₃ * X * v2 ^ 2 + C W.a₄ * X ^ 2 * v2 ^ 2
      + C W.a₆ * X ^ 3 * v2 ^ 3, by rw [hfix, hv2]; ring⟩
section Map
variable {S : Type v} [CommRing S] (φ : R →+* S)
end Map
end CurveSer
open CurveSer
end Formalism.L2.Th1.A
end
end

set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.CurveSer
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
namespace Formalism.L2.Th1.A.CurveSer
theorem _root_.solution : wSer W = X ^ 3 * wU W := by
  obtain ⟨v, hv⟩ := exists_wSer_eq_X_cube_mul W
  have hu : wU W = v := by
    ext n
    unfold wU
    rw [coeff_mk, hv]
    simp [coeff_X_pow_mul']
  rw [hu]
  exact hv
end Formalism.L2.Th1.A.CurveSer
