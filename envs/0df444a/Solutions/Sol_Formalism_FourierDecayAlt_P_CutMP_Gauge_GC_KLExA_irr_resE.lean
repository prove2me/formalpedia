-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA.irr_resE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:30:39.297303+00:00
-- url     : https://prove2.me/submissions/a8aad4e4-1a67-4d71-b308-fb05ccdc89d7

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreKLExistsOfAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ V} (S : Submodule ℂ V) (hS : Stab E S) (hne : S ≠ ⊥)
    (hirr : ∀ S' : Submodule ℂ V, S' ≤ S → Stab E S' → S' = ⊥ ∨ S' = S) : Irr (resE E S hS) := by
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 hne, fun T hT => ?_⟩
  have hinj := Submodule.map_injective_of_injective S.injective_subtype
  have hst : Stab E (T.map S.subtype) := by
    intro a b v hv
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hv
    exact Submodule.mem_map.2 ⟨resE E S hS a b x, hT a b x hx, rfl⟩
  rcases hirr (T.map S.subtype) (Submodule.map_subtype_le S T) hst with h | h
  · left
    exact hinj (h.trans (Submodule.map_bot _).symm)
  · right
    exact hinj (h.trans (Submodule.map_subtype_top S).symm)
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA
