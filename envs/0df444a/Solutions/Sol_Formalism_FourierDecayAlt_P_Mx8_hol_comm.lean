-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx8.hol_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:50:56.637874+00:00
-- url     : https://prove2.me/submissions/d41b6de8-38cd-434e-be08-4d78b3904daf

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators

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
theorem _root_.solution (l : Fin r) : ∀ x ∈ ({L.p l, L.c l, L.ci l} : Set A),
    ∀ y ∈ ({-L.pb l, L.cb l, L.cbi l} : Set A), Commute x y := by
  intro x hx y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    (try simp only [Commute.neg_left_iff, Commute.neg_right_iff]) <;>
    first
    | exact L.p_pb _ _ | exact L.p_cb _ _ | exact L.p_cbi _ _
    | exact (L.pb_c _ _).symm | exact (L.pb_ci _ _).symm
    | exact L.fns_comm _ (by simp) _ (by simp)
end Formalism.FourierDecayAlt.P.Mx8
