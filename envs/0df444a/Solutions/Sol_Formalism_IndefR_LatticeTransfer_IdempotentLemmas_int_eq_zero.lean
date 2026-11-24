-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.IdempotentLemmas.int_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:03.960878+00:00
-- url     : https://prove2.me/submissions/1590e905-0249-44a7-be81-f488833a19a3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinrankIntSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
open Formalism.IndefR.LatticeTransfer.IdempotentLemmas
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace Formalism.IndefR.LatticeTransfer.IdempotentLemmas
theorem _root_.solution {T U : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K G T) (σ : Representation K G U)
    (hτ : ∀ W : Submodule K T, (∀ g : G, ∀ w ∈ W, τ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hσ : ∀ W : Submodule K U, (∀ g : G, ∀ w ∈ W, σ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hch : charOf τ ≠ charOf σ) (f : Representation.IntertwiningMap τ σ) : f = 0 := by
  by_contra hf
  have hf' : f.toLinearMap ≠ 0 := fun h =>
    hf (Representation.IntertwiningMap.ext (by simpa using h))
  have hker : LinearMap.ker f.toLinearMap = ⊥ := by
    rcases hτ (LinearMap.ker f.toLinearMap) (fun g w hw => by
      simp only [LinearMap.mem_ker, Representation.IntertwiningMap.toLinearMap_apply] at hw ⊢
      rw [f.isIntertwining, hw, map_zero]) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.mp h) hf'
  have hrange : LinearMap.range f.toLinearMap = ⊤ := by
    rcases hσ (LinearMap.range f.toLinearMap) (fun g w hw => by
      obtain ⟨v, rfl⟩ := hw
      exact ⟨τ g v, LinearMap.congr_fun (f.isIntertwining' g) v⟩) with h | h
    · exact absurd (LinearMap.range_eq_bot.mp h) hf'
    · exact h
  let e : T ≃ₗ[K] U := LinearEquiv.ofBijective f.toLinearMap
    ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hrange⟩
  have he : ∀ x, e x = f x := fun x => rfl
  apply hch
  funext g
  have hconj : e.conj (τ g) = σ g := by
    apply LinearMap.ext
    intro u
    rw [LinearEquiv.conj_apply_apply, he, f.isIntertwining, ← he, LinearEquiv.apply_symm_apply]
  show LinearMap.trace K T (τ g) = LinearMap.trace K U (σ g)
  rw [← hconj, LinearMap.trace_conj']
end Formalism.IndefR.LatticeTransfer.IdempotentLemmas
