-- Prove2me | solution 1 for Formalism.L2.SG.FoldBound.tsum_transversal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:17:45.761778+00:00
-- url     : https://prove2.me/submissions/8ce457a4-f571-4e09-a674-0ea21f731cd6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_FoldBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.FoldBound
namespace Formalism.L2.SG.FoldBound
theorem _root_.solution {G : Type*} [Group G] (Γ S : Subgroup G) (hSΓ : S ≤ Γ) (D : Set G)
    (hD : IsRightTransversal Γ S D) (φ : G → ℝ≥0∞) :
    ∑' δ : D, ∑' s : S, φ ((δ : G)⁻¹ * (s : G)) = ∑' γ : Γ, φ (γ : G) := by
  classical
  have hmem : ∀ (δ : D) (s : S), (δ : G)⁻¹ * (s : G) ∈ Γ := fun δ s =>
    Γ.mul_mem (Γ.inv_mem (hD.1 δ.2)) (hSΓ s.2)
  let f : D × S → Γ := fun p => ⟨(p.1 : G)⁻¹ * (p.2 : G), hmem p.1 p.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨δ, s⟩ ⟨δ', s'⟩ h
      have h' : (δ : G)⁻¹ * (s : G) = (δ' : G)⁻¹ * (s' : G) := congrArg Subtype.val h
      have hγ : (s : G)⁻¹ * (δ : G) ∈ Γ := Γ.mul_mem (Γ.inv_mem (hSΓ s.2)) (hD.1 δ.2)
      obtain ⟨p, -, hp⟩ := hD.2 _ hγ
      have e1 := hp (s⁻¹, δ) (by simp)
      have h'' : (s' : G)⁻¹ * (δ' : G) = (s : G)⁻¹ * (δ : G) := by
        have := congrArg (·⁻¹) h'
        simp only [mul_inv_rev, inv_inv] at this
        exact this.symm
      have e2 := hp (s'⁻¹, δ') (by simpa using h'')
      have := e1.trans e2.symm
      simp only [Prod.mk.injEq, inv_inj] at this
      obtain ⟨rfl, rfl⟩ := this
      rfl
    · rintro ⟨γ, hγ⟩
      obtain ⟨p, hp, -⟩ := hD.2 _ (Γ.inv_mem hγ)
      refine ⟨(p.2, p.1⁻¹), Subtype.ext ?_⟩
      simp only [f, Subgroup.coe_inv]
      rw [← mul_inv_rev, hp, inv_inv]
  rw [← ENNReal.tsum_prod]
  exact (Equiv.ofBijective f hf).tsum_eq (fun γ : Γ => φ (γ : G))
end Formalism.L2.SG.FoldBound
