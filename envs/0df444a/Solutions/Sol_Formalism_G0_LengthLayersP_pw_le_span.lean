-- Prove2me | solution 1 for Formalism.G0.LengthLayersP.pw_le_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:28.824551+00:00
-- url     : https://prove2.me/submissions/fc247d97-56dc-4b47-b3f3-dc28426f6acd

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
import Theorems.Thm_Formalism_G0_LengthLayersP_mem_pw

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
open Formalism Formalism.G0
open Formalism.G0.LengthLayersP
variable {O : Type} [CommRing O]
namespace Formalism.G0.LengthLayersP
theorem _root_.solution {M : Type} [AddCommGroup M] [Module O M] (π : O) (P : Submodule O M)
    (g E : ℕ) (h : AllButLE π ⊤ P g E) :
    ∃ C : Finset (M ⧸ P), C.card ≤ g ∧ pw π (M ⧸ P) E ≤ Submodule.span O (C : Set (M ⧸ P)) := by
  classical
  obtain ⟨C, -, hcard, hC⟩ := h
  refine ⟨C.image P.mkQ, le_trans Finset.card_image_le hcard, ?_⟩
  intro y hy
  obtain ⟨y0, rfl⟩ := mem_pw.mp hy
  obtain ⟨x, rfl⟩ := P.mkQ_surjective y0
  have hx := hC x Submodule.mem_top
  rw [Finset.coe_image, Submodule.span_image]
  obtain ⟨p, hp, t, ht, hpt⟩ := Submodule.mem_sup.mp hx
  refine Submodule.mem_map.mpr ⟨t, ht, ?_⟩
  have hp0 : P.mkQ p = 0 := (Submodule.Quotient.mk_eq_zero P).mpr hp
  rw [← map_smul, ← hpt, map_add, hp0, zero_add]
end Formalism.G0.LengthLayersP
