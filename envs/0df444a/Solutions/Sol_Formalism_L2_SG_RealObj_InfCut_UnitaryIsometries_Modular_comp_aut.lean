-- Prove2me | solution 1 for Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular.comp_aut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:19:26.92937+00:00
-- url     : https://prove2.me/submissions/f6412d40-364b-4e32-a84d-b0013f5cd240

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EqOneOfZpowMem
import Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_UnitaryIsometries_Modular_map_right
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
theorem _root_.solution (α : G ≃ₜ* G) (g : G) : Δ (α g) = Δ g := by
  obtain ⟨C, hC, hpos, hfin⟩ := exists_compact_pos (G := G)
  have hmeas : Measurable α := α.continuous.measurable
  have : ((Measure.haar : Measure G).map α).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ α
  set c := ((Measure.haar : Measure G).map α).haarScalarFactor Measure.haar with hc
  have hcpos : 0 < c := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  have hmap : (Measure.haar : Measure G).map α = c • Measure.haar :=
    Measure.isMulLeftInvariant_eq_smul _ _
  have key : ((Measure.haar : Measure G).map α).map (· * α g) = ((Measure.haar : Measure G).map (· * g)).map α := by
    rw [Measure.map_map (measurable_mul_const _) hmeas, Measure.map_map hmeas (measurable_mul_const _)]
    congr 1
    funext x
    simp [map_mul]
  rw [hmap, map_right, Measure.map_smul, Measure.map_smul, map_right, hmap, smul_smul, smul_smul] at key
  have := congrArg (fun μ : Measure G => μ C) key
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at this
  have hcC : ((c * Δ (α g) : ℝ≥0) : ℝ≥0∞) = ((Δ g * c : ℝ≥0) : ℝ≥0∞) :=
    (ENNReal.mul_left_inj hpos.ne' hfin).1 (by simpa [ENNReal.coe_mul] using this)
  have h2 : c * Δ (α g) = Δ g * c := by exact_mod_cast hcC
  rw [mul_comm (Δ g)] at h2
  exact mul_left_cancel₀ hcpos.ne' h2
end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular
