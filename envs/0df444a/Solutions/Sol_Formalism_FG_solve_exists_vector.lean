-- Prove2me | solution 1 for Formalism.FG.solve_exists_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:17:31.43029+00:00
-- url     : https://prove2.me/submissions/50af3e91-be20-4980-b302-3020e80400fb

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_hasSubst_of_low
import Theorems.Thm_Formalism_FG_SolveVAux_degree_eq_one
import Theorems.Thm_Formalism_FG_SolveVAux_lim_low
import Theorems.Thm_Formalism_FG_SolveVAux_lim_fixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG
open MvPowerSeries SolveVAux
namespace Formalism.FG
theorem _root_.solution : Formalism.FG.SolveExistsV.{u, v, w} := by
  intro R _ ι _ _ τ _ f G hf hG
  classical
  obtain ⟨hf0, hf1⟩ := hf
  set g : ι → MvPowerSeries ι R := fun j => f j - X j with hgdef
  have hg : ∀ j, Low 2 (g j) := by
    intro j d hd
    simp only [hgdef, map_sub]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hd with h0 | h1
    · have : d = 0 := (Finsupp.degree_eq_zero_iff d).1 (by omega)
      subst this
      rw [coeff_zero_eq_constantCoeff_apply, hf0 j, coeff_X,
        if_neg (fun h => (Finsupp.single_ne_zero.2 one_ne_zero) h.symm), sub_zero]
    · obtain ⟨i, rfl⟩ := degree_eq_one d h1
      rw [hf1 j i, coeff_X]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Finsupp.single_left_inj one_ne_zero]
  have hGl : ∀ j, Low 1 (G j) := fun j => (low_one_iff _).2 (hG j)
  refine ⟨lim G g, fun i => (low_one_iff _).1 (lim_low hGl hg i), fun j => ?_⟩
  have hs := hasSubst_of_low (lim_low hGl hg)
  have hfix := lim_fixed hGl hg j
  simp only [phi] at hfix
  have hfj : f j = g j + X j := by simp [hgdef]
  rw [hfj, subst_add hs, subst_X hs, ← hfix]
  abel
end Formalism.FG
