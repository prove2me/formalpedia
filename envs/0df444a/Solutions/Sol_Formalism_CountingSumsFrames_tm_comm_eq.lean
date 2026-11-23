-- Prove2me | solution 1 for Formalism.CountingSumsFrames.tm_comm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:12.163828+00:00
-- url     : https://prove2.me/submissions/e356406b-72ea-42a2-bf7e-0e42a758a906

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_comm_XD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (LL : Letters N) (j : ℕ) (i : Fin N) (c d a b : Fin r)
    (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    tm (p := p) LL j i c d (tm (p := p) LL j i a b y) - tm (p := p) LL j i a b (tm (p := p) LL j i c d y) =
      (if d = a then tm (p := p) LL j i c b y else 0) - (if b = c then tm (p := p) LL j i a d y else 0) := by
  have key := comm_XD (k := ℚ_[p]) (i, c) (i, d) (i, a) (i, b) y
  have key2 := comm_XD (k := ℚ_[p]) (i, d) (i, c) (i, b) (i, a) y
  by_cases hij : (i : ℕ) < j
  · by_cases hv : LL.vec i = true
    · simp only [tm, if_pos hij, if_pos hv]
      show X (i, c) * pderiv (i, d) (X (i, a) * pderiv (i, b) y) -
          X (i, a) * pderiv (i, b) (X (i, c) * pderiv (i, d) y) =
        (if d = a then X (i, c) * pderiv (i, b) y else 0) - (if b = c then X (i, a) * pderiv (i, d) y else 0)
      rw [key]
      rcases eq_or_ne d a with hda | hda <;> rcases eq_or_ne b c with hbc | hbc
      · subst hda; subst hbc; simp
      · subst hda; simp [hbc, hbc.symm]
      · subst hbc; simp [hda, hda.symm]
      · simp [hda, hbc, hda.symm, hbc.symm]
    · simp only [tm, if_pos hij, if_neg hv]
      show -(X (i, d) * pderiv (i, c) (-(X (i, b) * pderiv (i, a) y))) -
          -(X (i, b) * pderiv (i, a) (-(X (i, d) * pderiv (i, c) y))) =
        (if d = a then -(X (i, b) * pderiv (i, c) y) else 0) - (if b = c then -(X (i, d) * pderiv (i, a) y) else 0)
      simp only [map_neg, mul_neg, neg_neg]
      rw [key2]
      rcases eq_or_ne d a with hda | hda <;> rcases eq_or_ne b c with hbc | hbc
      · subst hda; subst hbc; simp [sub_neg_eq_add, neg_add_eq_sub]
      · subst hda; simp [hbc, hbc.symm, sub_neg_eq_add, neg_add_eq_sub]
      · subst hbc; simp [hda, hda.symm, sub_neg_eq_add, neg_add_eq_sub]
      · simp [hda, hbc, hda.symm, hbc.symm]
  · simp only [tm, if_neg hij]
    simp
end Formalism.CountingSumsFrames
