-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.exists_inv_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:50.275496+00:00
-- url     : https://prove2.me/submissions/4a249026-d544-48ef-9572-eaf47972dfd3

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef

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
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsHom
open Formalism.ELL Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
namespace Formalism.ELL.FormalGroupPointsHom
theorem _root_.solution {E : MvPowerSeries (Fin 2) K} (hE : IntegralMv E)
    (h1 : MvPowerSeries.constantCoeff E = 1) : ∃ ψ, IntegralMv ψ ∧ E * ψ = 1 := by
  let EU : MvPowerSeries (Fin 2) (unitBall K) := fun d => ⟨MvPowerSeries.coeff d E, hE d⟩
  have hmap : MvPowerSeries.map (unitBall K).subtype EU = E := by
    ext d; rw [MvPowerSeries.coeff_map]; rfl
  have hc : MvPowerSeries.constantCoeff EU = 1 := by
    apply Subtype.ext
    have : MvPowerSeries.constantCoeff E = 1 := h1
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at this ⊢
    exact this
  obtain ⟨v, hv⟩ := MvPowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hc]; exact isUnit_one)
  refine ⟨MvPowerSeries.map (unitBall K).subtype ↑v⁻¹, fun d => ?_, ?_⟩
  · rw [MvPowerSeries.coeff_map]; exact (MvPowerSeries.coeff d (↑v⁻¹ : MvPowerSeries (Fin 2) (unitBall K))).2
  · rw [← hmap, ← map_mul, ← hv, Units.mul_inv, map_one]
end Formalism.ELL.FormalGroupPointsHom
