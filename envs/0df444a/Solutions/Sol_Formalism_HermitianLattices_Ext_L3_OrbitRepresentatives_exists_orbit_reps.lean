-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives.exists_orbit_reps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:11.089713+00:00
-- url     : https://prove2.me/submissions/b3861ada-fd6f-4c86-b75b-e40432ac06b8

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomMapOfEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AdjoinMemGenusIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardStabilizerAutSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
open Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives
namespace Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives
theorem _root_.solution {G X : Type*} [Group G] [MulAction G X] (A : Set X) (hfin : A.Finite)
    (hA : ∀ g : G, ∀ x ∈ A, g • x ∈ A) :
    ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ ∀ x ∈ A, ∃! t, t ∈ T ∧ ∃ g : G, g • t = x := by
  classical
  let r := MulAction.orbitRel G X
  let f : X → X := fun x => (@Quotient.mk _ r x).out
  have hf1 : ∀ x, ∃ g : G, g • x = f x := fun x => MulAction.orbitRel_apply.mp (@Quotient.mk_out _ r x)
  have hf2 : ∀ x y (g : G), g • y = x → f x = f y := fun x y g hg =>
    congrArg Quotient.out (@Quotient.sound _ r x y (MulAction.orbitRel_apply.mpr ⟨g, hg⟩))
  refine ⟨hfin.toFinset.image f, ?_, ?_⟩
  · intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨g, hg⟩ := hf1 x
    rw [← hg]
    exact hA g x (hfin.mem_toFinset.mp hx)
  · intro x hx
    obtain ⟨g, hg⟩ := hf1 x
    refine ⟨f x, ⟨Finset.mem_image_of_mem f (hfin.mem_toFinset.mpr hx), g⁻¹, ?_⟩, ?_⟩
    · rw [← hg, inv_smul_smul]
    · rintro y ⟨hy, g', hg'⟩
      obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨k, hk⟩ := hf1 z
      exact (hf2 x z (g' * k) (by rw [mul_smul, hk, hg'])).symm
end Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives
