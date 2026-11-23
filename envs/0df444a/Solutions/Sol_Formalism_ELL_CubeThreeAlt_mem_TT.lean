-- Prove2me | solution 1 for Formalism.ELL.CubeThreeAlt.mem_TT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:04.614653+00:00
-- url     : https://prove2.me/submissions/01f7b1ac-97c0-4908-aabd-f8efd9de1850

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeThree

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
open Formalism Formalism.ELL
open Formalism.ELL.CubeThreeAlt
open WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "cc" => MvPowerSeries.constantCoeff
variable {W : WeierstrassCurve K} {σ : Type}
namespace Formalism.ELL.CubeThreeAlt
theorem _root_.solution {φ : MvPowerSeries σ K} : φ ∈ TT W σ ↔ ∀ e, MvPowerSeries.coeff e φ ∈ Sadj W := by
  rw [TT, RingHom.mem_range]
  constructor
  · rintro ⟨ψ, rfl⟩ e
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff e ψ).2
  · intro h
    refine ⟨(fun e => ⟨MvPowerSeries.coeff e φ, h e⟩ : MvPowerSeries σ (Formalism.ELL.WeierstrassChordSeries.Sadj W)), ?_⟩
    ext e
    rfl
end Formalism.ELL.CubeThreeAlt
