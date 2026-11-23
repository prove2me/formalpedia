-- Prove2me | solution 1 for Formalism.ELL.CubeThreeAlt.inv_mem_TT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:26.793526+00:00
-- url     : https://prove2.me/submissions/87aa4d19-1fa2-4c47-b6b1-752d6821e166

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
theorem _root_.solution {φ : MvPowerSeries σ K} (h : φ ∈ TT W σ) (h0 : cc φ ≠ 0)
    (hi : (cc φ)⁻¹ ∈ Sadj W) : φ⁻¹ ∈ TT W σ := by
  have h' := h
  rw [TT, RingHom.mem_range] at h'
  obtain ⟨ψ, hψ⟩ := h'
  have hc : ((MvPowerSeries.constantCoeff ψ : Formalism.ELL.WeierstrassChordSeries.Sadj W) : K) = cc φ := by
    rw [← hψ, MvPowerSeries.constantCoeff_map]
    rfl
  have hmul : MvPowerSeries.constantCoeff ψ * (⟨(cc φ)⁻¹, hi⟩ : Formalism.ELL.WeierstrassChordSeries.Sadj W) = 1 :=
    Subtype.ext (by
      show ((MvPowerSeries.constantCoeff ψ : Formalism.ELL.WeierstrassChordSeries.Sadj W) : K) * (cc φ)⁻¹ = 1
      rw [hc]
      exact mul_inv_cancel₀ h0)
  have hu : IsUnit (MvPowerSeries.constantCoeff ψ) := ⟨⟨_, _, hmul, (mul_comm _ _).trans hmul⟩, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, ψ * g = 1 := by
    exact (MvPowerSeries.isUnit_iff_constantCoeff.mpr hu).exists_right_inv
  have hφg : φ * MvPowerSeries.map (algebraMap (Formalism.ELL.WeierstrassChordSeries.Sadj W) K) g = 1 := by
    rw [← hψ, ← map_mul, hg, map_one]
  have key : φ⁻¹ = MvPowerSeries.map (algebraMap (Formalism.ELL.WeierstrassChordSeries.Sadj W) K) g := by
    calc φ⁻¹ = φ⁻¹ * (φ * MvPowerSeries.map (algebraMap (Formalism.ELL.WeierstrassChordSeries.Sadj W) K) g) := by rw [hφg, mul_one]
    _ = MvPowerSeries.map (algebraMap (Formalism.ELL.WeierstrassChordSeries.Sadj W) K) g := by
      rw [← mul_assoc, MvPowerSeries.inv_mul_cancel _ h0, one_mul]
  rw [key]
  exact RingHom.mem_range_self _ g
end Formalism.ELL.CubeThreeAlt
