-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.cnt_gmap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:41:07.142689+00:00
-- url     : https://prove2.me/submissions/6f93ef33-9f00-4bfb-aa91-f50c0d53aed1

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SigmaCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FormRightMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.LIOrb
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (n : 𝓞 F) (Ω : Set V) :
    cnt h (Formalism.HermitianLatticesTheory.gmap g A) 𝔭 k n (g '' Ω) = cnt h A 𝔭 k n Ω := by
  let e : ↥A ≃ₗ[𝓞 K] ↥(Formalism.HermitianLatticesTheory.gmap g A) := (g.restrictScalars (𝓞 K)).submoduleMap A
  have he : ∀ y : ↥A, ((e y : ↥(Formalism.HermitianLatticesTheory.gmap g A)) : V) = g y := fun y => rfl
  have hmap : ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A).map (e : ↥A →ₗ[𝓞 K] ↥(Formalism.HermitianLatticesTheory.gmap g A)) =
      ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(Formalism.HermitianLatticesTheory.gmap g A)) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  let E := Submodule.Quotient.equiv _ _ e hmap
  have hE : ∀ y : ↥A, E (Submodule.Quotient.mk y) = Submodule.Quotient.mk (e y) := fun y => rfl
  refine (Nat.card_congr (Equiv.subtypeEquiv E.toEquiv fun x => ?_)).symm
  constructor
  · rintro ⟨y, rfl, hc, hy⟩
    refine ⟨e y, (hE y).symm, ?_, y, hy, (he y).symm⟩
    rw [he, hg]
    exact hc
  · rintro ⟨y', e', hc, w, hw, hwy⟩
    obtain ⟨y, rfl⟩ := e.surjective y'
    refine ⟨y, E.injective ?_, ?_, ?_⟩
    · rw [hE]; exact e'
    · rw [he, hg] at hc
      exact hc
    · rw [he] at hwy
      rw [← g.injective hwy]
      exact hw
end Formalism.HermitianLattices.Ext.L3.LIOrb
