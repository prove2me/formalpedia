-- Prove2me | solution 1 for Formalism.CountingSumsFrames.eul_glAct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:56.289964+00:00
-- url     : https://prove2.me/submissions/ba7f0670-9502-4f6f-aef4-a50dd4104df4

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_eq_sum
import Theorems.Thm_Formalism_CountingSumsFrames_tm_mem
import Theorems.Thm_Formalism_CountingSumsFrames_eul_XD
import Theorems.Thm_Formalism_GM_FockB_eulL_mem
import Theorems.Thm_Formalism_GM_FockB_ops_apply_comm


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
theorem _root_.solution (LL : Letters N) (j : ℕ) (i0 : Fin N) (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    ProjS.eulL (fun c : Fin r => (i0, c)) (glAct p LL j c d x) = glAct p LL j c d (ProjS.eulL (fun c : Fin r => (i0, c)) x) := by
  have ht : Function.Injective (fun c : Fin r => (i0, c)) := fun a b h => (Prod.mk.inj h).2
  rw [glAct_eq_sum, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i = i0
  · subst hi
    unfold tm
    split_ifs with h1 h2
    · simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
      exact eul_XD (fun c : Fin r => (i, c)) ht c d x
    · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, map_neg]
      rw [eul_XD (fun c : Fin r => (i, c)) ht d c x]
    · simp
  · have hdisj : Disjoint {v : Fin N × Fin r | v.1 = i} {v : Fin N × Fin r | v.1 = i0} := by
      rw [Set.disjoint_left]; rintro v h1 h2
      simp only [Set.mem_ofPred_eq] at h1 h2; exact hi (h1 ▸ h2)
    exact (FockB.ops_apply_comm hdisj (tm_mem LL j i c d)
      (FockB.eulL_mem (S := {v : Fin N × Fin r | v.1 = i0}) (fun c : Fin r => (i0, c)) (fun c => rfl)) x).symm
end Formalism.CountingSumsFrames
