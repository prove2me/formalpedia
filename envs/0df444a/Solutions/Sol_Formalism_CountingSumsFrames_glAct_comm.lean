-- Prove2me | solution 1 for Formalism.CountingSumsFrames.glAct_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:52.077791+00:00
-- url     : https://prove2.me/submissions/4024802a-f141-4013-aba4-fd224ae8936c

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_eq_sum
import Theorems.Thm_Formalism_CountingSumsFrames_tm_comm_ne
import Theorems.Thm_Formalism_CountingSumsFrames_tm_comm_eq

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
theorem _root_.solution (LL : Letters N) (j : ℕ) (c d a b : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p LL j c d (glAct p LL j a b x) - glAct p LL j a b (glAct p LL j c d x) =
      (if d = a then glAct p LL j c b x else 0) - (if b = c then glAct p LL j a d x else 0) := by
  simp only [glAct_eq_sum, LinearMap.sum_apply, map_sum]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun o n => tm (p := p) LL j n c d (tm (p := p) LL j o a b x)), ← Finset.sum_sub_distrib]
  have hrow : ∀ i : Fin N, (∑ i', tm (p := p) LL j i c d (tm (p := p) LL j i' a b x)) -
      ∑ i', tm (p := p) LL j i' a b (tm (p := p) LL j i c d x) =
      (if d = a then tm (p := p) LL j i c b x else 0) - (if b = c then tm (p := p) LL j i a d x else 0) := by
    intro i
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i, tm_comm_eq]
    · intro i' _ hi'
      rw [tm_comm_ne LL j i i' (Ne.symm hi') c d a b x, sub_self]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [Finset.sum_congr rfl (fun i _ => hrow i)]
  split_ifs <;> simp [Finset.sum_sub_distrib]
end Formalism.CountingSumsFrames
