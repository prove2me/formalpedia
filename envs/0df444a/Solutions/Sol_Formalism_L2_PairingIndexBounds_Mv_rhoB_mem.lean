-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.rhoB_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:14:05.319194+00:00
-- url     : https://prove2.me/submissions/379d5845-67a5-4be5-9ddc-191c566e0358

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_FourierTransformIdentityHolds
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_rhoB_gen

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
theorem _root_.solution (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) (b : B) :
    ∀ Φ ∈ Sch c A₀, rhoB c b Φ ∈ Sch c A₀ := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a, b'⟩, rfl⟩ := hx
    simp only
    rw [rhoB_gen c hc]
    exact Submodule.smul_mem _ _ (gen_mem c A₀ _ _)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul r x _ ih => rw [map_smul]; exact Submodule.smul_mem _ r ih
end Formalism.L2.PairingIndexBounds.Mv
