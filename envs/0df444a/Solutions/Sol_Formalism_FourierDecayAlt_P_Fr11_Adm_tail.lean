-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr11.Adm_tail
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:07.894218+00:00
-- url     : https://prove2.me/submissions/a4ff067c-3626-445c-940a-dc299180d2d0

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ResidueForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr11
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
noncomputable section
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
variable {r : ℕ} (L : LevelData A r) (st : Start A)
namespace Formalism.FourierDecayAlt.P.Fr11
theorem _root_.solution (l : Letter ℂ S) (w : List (Letter ℂ S)) (h : admitted st (l :: w)) : admitted st w := by
  unfold admitted at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, fun l' hl' => h2 l' (List.mem_cons_of_mem _ hl'),
    fun l' hl' => h3 l' (List.mem_cons_of_mem _ hl'), (List.pairwise_cons.mp h4).2⟩
  rw [List.map_cons, List.nodup_cons] at h1
  exact h1.2
end Formalism.FourierDecayAlt.P.Fr11
