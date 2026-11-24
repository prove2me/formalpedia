-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrkb_r_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:41:43.090802+00:00
-- url     : https://prove2.me/submissions/c2350aa4-0f75-49b4-8b25-a62811762362

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkAesmTsum
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkbLeOneAddSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  {Γ : Subgroup G} [Countable Γ] {D : Set G}
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (h : rr_FD μ Γ D) {r : G → G} (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D) :
    ∀ᵐ y ∂μ.restrict D, ∀ γ : Γ, r ((γ : G) * y) = y := by
  classical
  have hnull : ∀ δ : Γ, (δ : G) ≠ 1 →
      μ ((fun y => (δ : G) * y) ⁻¹' ((fun y => (δ : G) * y) '' D ∩ D)) = 0 := by
    intro δ hδ
    rw [measure_preimage_mul]
    exact h.3 δ δ.2 hδ
  have hB : μ (⋃ δ : Γ, ⋃ (_ : (δ : G) ≠ 1),
      (fun y => (δ : G) * y) ⁻¹' ((fun y => (δ : G) * y) '' D ∩ D)) = 0 :=
    measure_iUnion_null (fun δ => measure_iUnion_null (fun hδ => hnull δ hδ))
  rw [ae_restrict_iff' h.1, ae_iff]
  refine measure_mono_null ?_ hB
  intro y hy
  simp only [Set.mem_setOf_eq] at hy
  push_neg at hy
  obtain ⟨hyD, γ, hγ⟩ := hy
  obtain ⟨γ', hγ'Γ, hr1, hmem⟩ := hr ((γ : G) * y)
  have hδ : ((⟨γ' * γ, Γ.mul_mem hγ'Γ γ.2⟩ : Γ) : G) ≠ 1 := by
    intro h1
    apply hγ
    rw [hr1, ← mul_assoc]
    exact (congrArg (· * y) h1).trans (one_mul y)
  simp only [Set.mem_iUnion]
  refine ⟨⟨γ' * γ, Γ.mul_mem hγ'Γ γ.2⟩, hδ, ?_⟩
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_image]
  refine ⟨⟨y, hyD, rfl⟩, ?_⟩
  show γ' * γ * y ∈ D
  rw [mul_assoc]
  exact hmem
end Formalism.MainNotions.LeviCoordinates
