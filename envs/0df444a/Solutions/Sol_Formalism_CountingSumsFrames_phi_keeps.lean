-- Prove2me | solution 1 for Formalism.CountingSumsFrames.phi_keeps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:36.159109+00:00
-- url     : https://prove2.me/submissions/cc18b974-c2b8-4deb-80a1-ecceda611677

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_ops_keep_supp
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_top
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_mem
import Theorems.Thm_Formalism_CountingSumsFrames_phi_mem
import Theorems.Thm_Formalism_CountingSumsFrames_phi_pol
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_keep
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
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.CountingSumsFrames
theorem _root_.solution {N r : ℕ} [NeZero r] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i j : Fin T.t)
    (hij : i < j) : ∀ u ∈ Y p (r := r) LL T.J (T.thrUpTo i), T.phi p LL j u ∈ Y p (r := r) LL T.J (T.thrUpTo i) := by
  obtain ⟨hmono, hpos, _⟩ := hadm
  obtain ⟨h, _, _⟩ := hpos j
  have hpij : T.pos i < T.pos j := hmono hij
  intro u hu
  have hu1 := (Submodule.mem_inf.mp hu).1
  have hu2 := (Submodule.mem_inf.mp hu).2
  refine Submodule.mem_inf.mpr ⟨phi_pol LL T j h u hu1, ?_⟩
  rw [Submodule.mem_iInf] at hu2 ⊢
  intro k
  have hk2 := hu2 k
  simp only [TieData.thrUpTo] at hk2 ⊢
  split_ifs at hk2 ⊢ with hk
  · have hdisj : Disjoint {v : Fin N × Fin r | (v.1 : ℕ) = T.pos j ∨ (v.1 : ℕ) = T.pos j + 1}
        {v : Fin N × Fin r | (v.1 : ℕ) < T.J k} := by
      rw [Set.disjoint_left]
      rintro v hv1 hv2
      simp only [Set.mem_ofPred_eq] at hv1 hv2
      omega
    refine ycond_keep LL (T.J k) (T.thr k) (T.phi p LL j) (fun c d x => ?_) (fun x hx => ?_) u hk2
    · exact FockB.ops_apply_comm hdisj (phi_mem LL T j h) (glAct_mem LL (T.J k) c d) x
    · refine ops_keep_supp _ _ (fun m m' hmm' hm => ?_) (phi_mem LL T j h) x hx
      have : wt LL (T.J k) 0 m = wt LL (T.J k) 0 m' := by
        unfold wt
        refine Finset.sum_congr rfl fun i' _ => ?_
        split_ifs with hi
        · rw [hmm' (i', 0) (by simp only [Set.mem_ofPred_eq]; omega)]
        · rw [hmm' (i', 0) (by simp only [Set.mem_ofPred_eq]; omega)]
        · rfl
      simp only [Set.mem_ofPred_eq] at hm ⊢
      rw [← this]; exact hm
  · rw [ycond_top]; exact Submodule.mem_top
end Formalism.CountingSumsFrames
