-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.OrbSum.exists_reps_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:35.909406+00:00
-- url     : https://prove2.me/submissions/62949981-d8b7-4f08-a3c5-d0c2dcc104ff

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsRepsOfCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
open Formalism.HermitianLattices.Ext.L3.OrbSum
variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]
namespace Formalism.HermitianLattices.Ext.L3.OrbSum
theorem _root_.solution (A : Set X) (hA : ∀ g : G, ∀ x ∈ A, g • x ∈ A) (C : Set X)
    (hC : C.Finite) (hCA : ∀ c ∈ C, c ∈ A) (hcov : ∀ x ∈ A, ∃ c ∈ C, ∃ g : G, g • c = x) :
    ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ ∀ x ∈ A, ∃! t, t ∈ T ∧ ∃ g : G, g • t = x := by
  classical
  let rep : X → X := fun x => (Quotient.mk (MulAction.orbitRel G X) x).out
  have hrep : ∀ x, ∃ g : G, g • x = rep x := fun x => by
    have h1 : Quotient.mk (MulAction.orbitRel G X) (rep x) = Quotient.mk _ x := Quotient.out_eq _
    have h2 : rep x ∈ MulAction.orbit G x := Quotient.exact h1
    exact MulAction.mem_orbit_iff.1 h2
  have hrepA : ∀ x ∈ A, rep x ∈ A := fun x hx => by
    obtain ⟨g, hg⟩ := hrep x
    rw [← hg]
    exact hA g x hx
  have hrep_eq : ∀ x y : X, ∀ g : G, g • y = x → rep y = rep x := fun x y g hg => by
    show (Quotient.mk (MulAction.orbitRel G X) y).out = (Quotient.mk (MulAction.orbitRel G X) x).out
    congr 1
    apply Quotient.sound
    show y ∈ MulAction.orbit G x
    rw [MulAction.mem_orbit_iff]
    exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩
  refine ⟨hC.toFinset.image rep, ?_, ?_⟩
  · intro t ht
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 ht
    exact hrepA c (hCA c (hC.mem_toFinset.1 hc))
  · intro x hx
    obtain ⟨c, hc, g, hg⟩ := hcov x hx
    obtain ⟨g', hg'⟩ := hrep c
    refine ⟨rep c, ⟨Finset.mem_image.2 ⟨c, hC.mem_toFinset.2 hc, rfl⟩, ⟨g * g'⁻¹, ?_⟩⟩, ?_⟩
    · rw [← hg', mul_smul, inv_smul_smul, hg]
    · rintro t ⟨ht, h, hh⟩
      obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 ht
      obtain ⟨g'', hg''⟩ := hrep c'
      have e1 : rep c' = rep x := (hrep_eq (rep c') c' g'' hg'').trans (hrep_eq x (rep c') h hh)
      have e2 : rep c = rep x := hrep_eq x c g hg
      rw [e1, e2]
end Formalism.HermitianLattices.Ext.L3.OrbSum
