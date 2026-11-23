-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.Sch_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:21:50.192814+00:00
-- url     : https://prove2.me/submissions/3cc8d018-ac83-4c8f-98ea-b6bcdce63f00

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_FourierTransformIdentityHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.PairingIndexBounds Formalism.L2.PairingIndexBounds.Mv
variable {k : Type*} [Field k] {A B T : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup T] [Module k T]
namespace Formalism.L2.PairingIndexBounds.Mv
theorem _root_.solution {c : B → A → k} {A₀ : AddSubgroup A} {f g : Sch c A₀ →ₗ[k] T}
    (h : ∀ a b, f ⟨gen c A₀ a b, gen_mem c A₀ a b⟩ = g ⟨gen c A₀ a b, gen_mem c A₀ a b⟩) : f = g := by
  ext ⟨Φ, hΦ⟩
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    exact h a b
  | zero =>
    have e : (⟨0, Submodule.zero_mem _⟩ : Sch c A₀) = 0 := rfl
    rw [e, map_zero, map_zero]
  | add x y hx hy ihx ihy =>
    have e : (⟨x + y, Submodule.add_mem _ hx hy⟩ : Sch c A₀) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [e, map_add, map_add, ihx, ihy]
  | smul r x hx ih =>
    have e : (⟨r • x, Submodule.smul_mem _ r hx⟩ : Sch c A₀) = r • ⟨x, hx⟩ := rfl
    rw [e, map_smul, map_smul, ih]
end Formalism.L2.PairingIndexBounds.Mv
