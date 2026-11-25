-- Prove2me | solution 1 for Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular.eq_one_of_iterate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:14:52.087955+00:00
-- url     : https://prove2.me/submissions/83b5182c-71b2-4a64-be18-7f8e4000f456

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EqOneOfZpowMem
import Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_UnitaryIsometries_Modular_eventually_lt
import Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_UnitaryIsometries_Modular_comp_aut

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
theorem _root_.solution (α : G ≃ₜ* G) (g k : G) (hk : Δ k = 1)
    (hlim : Tendsto (fun m : ℕ => (⇑α)^[m] g) atTop (𝓝 k)) : Δ g = 1 := by
  have hit : ∀ m : ℕ, Δ ((⇑α)^[m] g) = Δ g := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', comp_aut, ih]
  set hseq := fun m : ℕ => k⁻¹ * (⇑α)^[m] g with hh
  have hlim1 : Tendsto hseq atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := k⁻¹)).mul hlim
    simpa using this
  have hval : ∀ m, Δ (hseq m) = Δ g := fun m => by
    simp only [hh, Measure.modularCharacterFun_map_mul, hit]
    have : Δ k⁻¹ = 1 := by
      have h1 := Measure.modularCharacterFun_map_mul (G := G) k⁻¹ k
      rw [inv_mul_cancel, Measure.modularCharacterFun_map_one, hk, mul_one] at h1
      exact h1.symm
    rw [this, one_mul]
  have hvalinv : ∀ m, Δ (hseq m)⁻¹ * Δ g = 1 := fun m => by
    rw [← hval m, ← Measure.modularCharacterFun_map_mul, inv_mul_cancel, Measure.modularCharacterFun_map_one]
  have hx : 0 < (Δ g : ℝ) := by exact_mod_cast Measure.modularCharacterFun_pos g
  by_contra hne
  rcases lt_or_gt_of_ne (show (Δ g : ℝ) ≠ 1 from fun h => hne (by exact_mod_cast h)) with hlt | hgt
  ·
    have hlim2 : Tendsto (fun m => (hseq m)⁻¹) atTop (𝓝 1) := by simpa using hlim1.inv
    have hε : 0 < (Δ g : ℝ)⁻¹ - 1 := by rw [sub_pos]; exact (one_lt_inv₀ hx).2 hlt
    obtain ⟨m, hm⟩ := (hlim2.eventually (eventually_lt _ hε)).exists
    have h1 := hvalinv m
    have h2 : (Δ (hseq m)⁻¹ : ℝ) * Δ g = 1 := by exact_mod_cast h1
    have h3 : (Δ (hseq m)⁻¹ : ℝ) = (Δ g : ℝ)⁻¹ := by field_simp; linarith
    linarith
  · have hε : 0 < (Δ g : ℝ) - 1 := by linarith
    obtain ⟨m, hm⟩ := (hlim1.eventually (eventually_lt _ hε)).exists
    have := hval m
    rw [show (Δ (hseq m) : ℝ) = Δ g by exact_mod_cast this] at hm
    linarith
end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular
