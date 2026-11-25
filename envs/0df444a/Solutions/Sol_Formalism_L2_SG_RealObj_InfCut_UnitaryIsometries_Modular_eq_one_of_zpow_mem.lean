-- Prove2me | solution 1 for Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular.eq_one_of_zpow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:13:21.044555+00:00
-- url     : https://prove2.me/submissions/ef188293-3b71-497c-8c58-f28e2d64d2f5

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
theorem _root_.solution {k : G} {Q : Set G} (hQ : IsCompact Q) (hk : ∀ j : ℤ, k ^ j ∈ Q) : Δ k = 1 := by
  obtain ⟨C, hC, hpos, hfin⟩ := exists_compact_pos (G := G)
  have hCQ : IsCompact (C * Q⁻¹) := hC.mul hQ.inv
  set M := (Measure.haar : Measure G) (C * Q⁻¹) with hM
  have hMfin : M ≠ ⊤ := hCQ.measure_lt_top.ne
  have hbound : ∀ j : ℤ, ((Δ k ^ j : ℝ≥0) : ℝ≥0∞) * (Measure.haar : Measure G) C ≤ M := by
    intro j
    have hsub : (· * k ^ j) ⁻¹' C ⊆ C * Q⁻¹ := by
      intro x hx
      refine ⟨x * k ^ j, hx, (k ^ j)⁻¹, Set.inv_mem_inv.2 (hk j), by group⟩
    have := haar_preimage (k ^ j) hC.isClosed.measurableSet
    have hz : Δ (k ^ j) = Δ k ^ j := map_zpow (Measure.modularCharacter (G := G)) k j
    rw [hz] at this
    calc ((Δ k ^ j : ℝ≥0) : ℝ≥0∞) * (Measure.haar : Measure G) C
        = (Measure.haar : Measure G) ((· * k ^ j) ⁻¹' C) := by rw [this]
      _ ≤ M := measure_mono hsub
  have hx : 0 < (Δ k : ℝ) := by exact_mod_cast Measure.modularCharacterFun_pos k
  set B := M.toReal / ((Measure.haar : Measure G) C).toReal with hB
  have hCr : 0 < ((Measure.haar : Measure G) C).toReal := ENNReal.toReal_pos hpos.ne' hfin
  have hb : ∀ j : ℤ, (Δ k : ℝ) ^ j ≤ B := by
    intro j
    have h1 := hbound j
    rw [hB, le_div_iff₀ hCr]
    have h2 := (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin) hMfin).2 h1
    rw [ENNReal.toReal_mul] at h2
    simpa using h2
  by_contra hne
  rcases lt_or_gt_of_ne (show (Δ k : ℝ) ≠ 1 from fun h => hne (by exact_mod_cast h)) with hlt | hgt
  · have ht : Tendsto (fun j : ℕ => ((Δ k : ℝ)⁻¹) ^ j) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (one_lt_inv₀ hx |>.2 hlt)
    obtain ⟨j, hj⟩ := (ht.eventually_gt_atTop B).exists
    have := hb (-(j : ℤ))
    rw [zpow_neg, zpow_natCast, ← inv_pow] at this
    linarith
  · have ht : Tendsto (fun j : ℕ => (Δ k : ℝ) ^ j) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hgt
    obtain ⟨j, hj⟩ := (ht.eventually_gt_atTop B).exists
    have := hb (j : ℤ)
    rw [zpow_natCast] at this
    linarith
end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular
