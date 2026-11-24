-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx8.G_comm_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:49:43.982949+00:00
-- url     : https://prove2.me/submissions/578062d0-8ba5-41bd-b1a3-db1f272536fe

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_p_c
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_p_ci


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx8
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)
namespace Formalism.FourierDecayAlt.P.Mx8
theorem _root_.solution (l m : Fin r) (h : l ≠ m) : ∀ x ∈ G L l, ∀ y ∈ G L m, Commute x y := by
  have h' := h.symm
  have pc : ∀ a b : Fin r, a ≠ b → Commute (L.p a) (L.c b) := fun a b hab => by
    have := L.p_c a b; rwa [if_neg hab, add_zero] at this
  have pci : ∀ a b : Fin r, a ≠ b → Commute (L.p a) (L.ci b) := fun a b hab => by
    have := L.p_ci a b; rwa [if_neg hab, sub_zero] at this
  have pbcb : ∀ a b : Fin r, a ≠ b → Commute (L.pb a) (L.cb b) := fun a b hab => by
    have := L.pb_cb a b; rwa [if_neg hab, add_zero] at this
  have pbcbi : ∀ a b : Fin r, a ≠ b → Commute (L.pb a) (L.cbi b) := fun a b hab => by
    have := L.pb_cbi a b; rwa [if_neg hab, sub_zero] at this
  intro x hx y hy
  simp only [G, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (try simp only [Commute.neg_left_iff, Commute.neg_right_iff]) <;>
    first
    | exact L.p_p _ _ | exact L.p_pb _ _ | exact (L.p_pb _ _).symm | exact L.pb_pb _ _
    | exact pc _ _ h | exact (pc _ _ h').symm | exact pci _ _ h | exact (pci _ _ h').symm
    | exact pbcb _ _ h | exact (pbcb _ _ h').symm | exact pbcbi _ _ h | exact (pbcbi _ _ h').symm
    | exact L.p_cb _ _ | exact (L.p_cb _ _).symm | exact L.p_cbi _ _ | exact (L.p_cbi _ _).symm
    | exact L.pb_c _ _ | exact (L.pb_c _ _).symm | exact L.pb_ci _ _ | exact (L.pb_ci _ _).symm
    | exact L.fns_comm _ (by simp) _ (by simp)
end Formalism.FourierDecayAlt.P.Mx8
