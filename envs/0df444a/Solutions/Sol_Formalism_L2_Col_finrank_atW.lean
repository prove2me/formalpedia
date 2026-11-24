-- Prove2me | solution 1 for Formalism.L2.Col.finrank_atW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:14:20.203807+00:00
-- url     : https://prove2.me/submissions/3b8f5368-90db-49c6-8d8d-84c2b86b0132

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff
import Theorems.Thm_Formalism_L2_Col_atW_finite
import Theorems.Thm_Formalism_L2_Col_atW_free
import Theorems.Thm_Formalism_L2_Col_span_atW

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.L2.Col
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) {L : Submodule (𝓞 K) V} (h : L.FG) :
    Module.finrank (Ow w) (atW w L) = Module.finrank K (Submodule.span K (L : Set V)) := by
  have := atW_finite w h
  have := atW_free w h
  let b := Module.Free.chooseBasis (Ow w) (atW w L)
  have hli : LinearIndependent (Ow w) (fun i => ((b i : atW w L) : V)) :=
    b.linearIndependent.map' (atW w L).subtype (Submodule.ker_subtype _)
  have hliK : LinearIndependent K (fun i => ((b i : atW w L) : V)) :=
    (LinearIndependent.iff_fractionRing (Ow w) K).1 hli
  have hsp : Submodule.span (Ow w) (Set.range fun i => ((b i : atW w L) : V)) = atW w L := by
    have h1 : (Set.range fun i => ((b i : atW w L) : V)) = (atW w L).subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [h1, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have key : ∀ S : Set V, Submodule.span (Ow w) S = atW w L →
      Submodule.span K S = Submodule.span K (L : Set V) := fun S hS => by
    rw [← span_atW w L, ← hS, Submodule.span_span_of_tower]
  have hspK := key _ hsp
  rw [← hspK, finrank_span_eq_card hliK, Module.finrank_eq_card_basis b]
end Formalism.L2.Col
