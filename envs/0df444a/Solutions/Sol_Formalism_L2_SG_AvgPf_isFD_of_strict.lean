-- Prove2me | solution 1 for Formalism.L2.SG.AvgPf.isFD_of_strict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:17:58.25505+00:00
-- url     : https://prove2.me/submissions/784bf7b5-4ad7-458e-8110-e451c9a1c4e0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_LieAveraging_LsSetresAvg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology Set
open scoped Pointwise ENNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.AvgPf
namespace Formalism.L2.SG.AvgPf
theorem _root_.solution {Γ α : Type*} [Group Γ] [MulAction Γ α] [MeasurableSpace α] (μ : Measure α) {S : Set α}
    (hS : MeasurableSet S) (hcov : ∀ᵐ x ∂μ, ∃ g : Γ, g • x ∈ S)
    (huniq : ∀ x ∈ S, ∀ g : Γ, g • x ∈ S → g = 1) : IsFundamentalDomain Γ S μ := by
  refine ⟨hS.nullMeasurableSet, hcov, ?_⟩
  intro g h hgh
  show AEDisjoint μ (g • S) (h • S)
  refine Disjoint.aedisjoint ?_
  rw [Set.disjoint_left]
  rintro y ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
  have hmem : (h⁻¹ * g) • a ∈ S := by
    have hba' : h • b = g • a := hba
    rw [mul_smul, ← hba', inv_smul_smul]
    exact hb
  have e := huniq a ha _ hmem
  rw [inv_mul_eq_one] at e
  exact hgh e.symm
end Formalism.L2.SG.AvgPf
