-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx8.gamma_family_commute_generators
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:49:48.9541+00:00
-- url     : https://prove2.me/submissions/74e2cb9a-34bf-4bbd-86ee-aecb384dbfab

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
theorem _root_.solution (l : Fin r) : ∀ x ∈ G L l,
    ∀ y ∈ ({L.ζ, L.ζb, L.GG, L.GGi, L.nab, L.nabs} : Set A), Commute x y := by
  intro x hx y hy
  simp only [G, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (try simp only [Commute.neg_left_iff, Commute.neg_right_iff]) <;>
    first
    | exact L.p_ζ _ | exact L.p_ζb _ | exact L.p_GG _ | exact L.p_GGi _ | exact L.p_nab _ | exact L.p_nabs _
    | exact L.pb_ζ _ | exact L.pb_ζb _ | exact L.pb_GG _ | exact L.pb_GGi _ | exact L.pb_nab _
    | exact L.pb_nabs _
    | exact (L.nab_c _).symm | exact (L.nab_ci _).symm | exact (L.nab_cb _).symm | exact (L.nab_cbi _).symm
    | exact (L.nabs_c _).symm | exact (L.nabs_ci _).symm | exact (L.nabs_cb _).symm
    | exact (L.nabs_cbi _).symm
    | exact L.fns_comm _ (by simp) _ (by simp)
end Formalism.FourierDecayAlt.P.Mx8
