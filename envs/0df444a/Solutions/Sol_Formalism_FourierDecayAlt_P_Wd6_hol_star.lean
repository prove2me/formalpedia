-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.hol_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:00.605675+00:00
-- url     : https://prove2.me/submissions/82b66d9d-d9d1-44f9-ab54-38fcdd38cf14

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_commute_Avr_Bvr_of_commute_siteOps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd6
theorem _root_.solution {σ : Site A} (hσ : IsSite σ) (Y Y' : K) (i j r s : Fin 2) :
    Commute (Ts σ Y i j) (star (Ts σ Y' r s)) := by
  have hh := hσ.2
  have m1 : σ.p ∈ hol σ := by simp [hol]
  have m2 : σ.c ∈ hol σ := by simp [hol]
  have m3 : σ.ci ∈ hol σ := by simp [hol]
  rw [← commute_star_comm]
  apply commute_Avr_Bvr_of_commute_siteOps <;> rw [commute_star_comm] <;> symm <;> apply commute_Avr_Bvr_of_commute_siteOps
  all_goals first
    | exact (hh _ m1 _ m1).symm
    | exact (hh _ m1 _ m2).symm
    | exact (hh _ m1 _ m3).symm
    | exact (hh _ m2 _ m1).symm
    | exact (hh _ m2 _ m2).symm
    | exact (hh _ m2 _ m3).symm
    | exact (hh _ m3 _ m1).symm
    | exact (hh _ m3 _ m2).symm
    | exact (hh _ m3 _ m3).symm
end Formalism.FourierDecayAlt.P.Wd6
