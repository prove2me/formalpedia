-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.Sch_le_span_eFam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:13:56.396039+00:00
-- url     : https://prove2.me/submissions/23d7720a-f11d-47bd-8f60-2a14c378f6a2

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_FourierTransformIdentityHolds
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_gen_eq_eFam

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
theorem _root_.solution (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) :
    Sch c A₀ ≤ Submodule.span k (Set.range (eFam (k := k) A₀)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨a, b⟩, rfl⟩
  simp only
  rw [gen_eq_eFam c hc A₀ a b]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
end Formalism.L2.PairingIndexBounds.Mv
