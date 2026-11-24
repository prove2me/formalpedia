-- Prove2me | solution 1 for Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular.eventually_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:19:28.524739+00:00
-- url     : https://prove2.me/submissions/f7d207fc-b51f-45b7-9c6d-ff490afdebd8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EqOneOfZpowMem
import Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_UnitaryIsometries_Modular_haar_preimage
import Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_UnitaryIsometries_Modular_exists_compact_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology Filter
open scoped ENNReal NNReal Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular
variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
local notation "Δ" => Measure.modularCharacterFun (G := G)
namespace Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular
theorem _root_.solution (ε : ℝ) (hε : 0 < ε) : ∀ᶠ h in 𝓝 (1 : G), (Δ h : ℝ) < 1 + ε := by
  obtain ⟨C, hC, hpos, hfin⟩ := exists_compact_pos (G := G)
  have hlt : (Measure.haar : Measure G) C < ENNReal.ofReal (1 + ε) * (Measure.haar : Measure G) C := by
    have h1 : (1 : ℝ≥0∞) < ENNReal.ofReal (1 + ε) := by
      rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    have := ENNReal.mul_lt_mul_right hpos.ne' hfin h1
    simpa [mul_comm] using this
  obtain ⟨U, hCU, hU, hUlt⟩ := Set.exists_isOpen_lt_of_lt C _ hlt
  obtain ⟨V, hV, hCV⟩ := compact_open_separated_mul_right hC hU hCU
  have hV' : ∀ᶠ h in 𝓝 (1 : G), h⁻¹ ∈ V := by
    have ht : Tendsto (fun h : G => h⁻¹) (𝓝 1) (𝓝 1) := by simpa using continuous_inv.tendsto (1 : G)
    exact ht hV
  filter_upwards [hV'] with h hh
  have hsub : (· * h) ⁻¹' C ⊆ U := by
    intro x hx
    apply hCV
    exact ⟨x * h, hx, h⁻¹, hh, by group⟩
  have h2 : (Δ h : ℝ≥0∞) * (Measure.haar : Measure G) C < ENNReal.ofReal (1 + ε) * (Measure.haar : Measure G) C := by
    rw [← haar_preimage h hC.isClosed.measurableSet]
    exact lt_of_le_of_lt (measure_mono hsub) hUlt
  have h3 : (Δ h : ℝ≥0∞) < ENNReal.ofReal (1 + ε) :=
    not_le.1 fun hle => lt_irrefl _ (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle zero_le) h2)
  rw [← ENNReal.ofReal_coe_nnreal] at h3
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).1 h3
end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular
