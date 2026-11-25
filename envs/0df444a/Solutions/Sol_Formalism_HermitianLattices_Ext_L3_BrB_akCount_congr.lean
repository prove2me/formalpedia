-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BrB.akCount_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:17:33.932902+00:00
-- url     : https://prove2.me/submissions/ca904c89-f64b-455e-a84b-b5e871698fa9

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsIntegralLatOfForall
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SumLocRepsEq

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BrB
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.BrB
theorem _root_.solution {A B : Submodule (𝓞 K) V} (e : ↥A ≃ₗ[𝓞 K] ↥B)
    (he : ∀ x y : ↥A, h (e x : V) (e y : V) = h (x : V) (y : V)) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    akCount h B 𝔭 k = akCount h A 𝔭 k := by
  have hmap : ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A).map (e : ↥A →ₗ[𝓞 K] ↥B) =
      ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥B) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  let ε := Submodule.Quotient.equiv _ _ e hmap
  have hε : ∀ x : ↥A, ε (Submodule.Quotient.mk x) = Submodule.Quotient.mk (e x) := fun x => rfl
  unfold akCount
  refine (Nat.card_congr (Equiv.subtypeEquiv ε.conj.toEquiv ?_)).symm
  intro X
  have hX : ∀ x : ↥A, (ε.conj X) (Submodule.Quotient.mk (e x)) = ε (X (Submodule.Quotient.mk x)) := by
    intro x
    rw [LinearEquiv.conj_apply_apply, ← hε, LinearEquiv.symm_apply_apply]
  constructor
  · intro H x y x' y' h1 h2
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    obtain ⟨x', rfl⟩ := e.surjective x'
    obtain ⟨y', rfl⟩ := e.surjective y'
    rw [he, he]
    refine H x y x' y' ?_ ?_
    · apply ε.injective
      rw [hε, ← hX]
      exact h1
    · apply ε.injective
      rw [hε, ← hX]
      exact h2
  · intro H x y x' y' h1 h2
    rw [← he, ← he x y]
    refine H (e x) (e y) (e x') (e y') ?_ ?_
    · change _ = (ε.conj X) _
      rw [hX, ← h1, hε]
    · change _ = (ε.conj X) _
      rw [hX, ← h2, hε]
end Formalism.HermitianLattices.Ext.L3.BrB
