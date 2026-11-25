-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.Ffull_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:15:26.928238+00:00
-- url     : https://prove2.me/submissions/79340039-e4aa-4791-a1df-828c6e65efc2

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_FfL_apply
import Theorems.Thm_Formalism_CountingSumsFrames_TO_wtsp_iff
import Theorems.Thm_Formalism_CountingSumsFrames_TO_Ffull_inj
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last



set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.GM.TM MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero N] [NeZero r] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t) (ρ : Fin r)
  (hρ : (ρ : ℕ) = r - 1) (n : Fin T.t → ℕ) (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i)
include hadm hS
include hρ
omit hρ
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (Ω : Finset (Fin r → ℤ)) (nb : (Fin r → ℤ) → ℕ)
    (f : ∀ w, Fin (nb w) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hf : ∀ w a, f w a ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w)
    (hli : ∀ w, LinearIndependent ℚ_[p] (f w)) :
    LinearIndependent ℚ_[p] (fun x : (Σ w : Ω, Fin (nb w.1)) => T.Ffull p (LL.setTies T n) i ρ (n i) (f x.1.1 x.2)) := by
  classical
  set LLK := (LL.setTies T n).takeD (T.pos i + 1) with hLLK
  have hPf : ∀ w a, f w a ∈ Pol p r LLK := fun w a =>
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp (hf w a)).1).1).1
  rw [Fintype.linearIndependent_iff]
  intro c hc x0
  have h1 : T.Ffull p (LL.setTies T n) i ρ (n i) (∑ x : (Σ w : Ω, Fin (nb w.1)), c x • f x.1.1 x.2) = 0 := by
    rw [← FfL_apply, map_sum, ← hc]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_smul, FfL_apply]
  have hsumP : (∑ x : (Σ w : Ω, Fin (nb w.1)), c x • f x.1.1 x.2) ∈ Pol p r LLK :=
    Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (hPf _ _)
  have h2 := Ffull_inj LL T hadm i ρ n hS _ hsumP h1
  have h3 := congrArg (weightedHomogeneousComponent (wv LLK (T.pos i + 1)) x0.1.1) h2
  rw [map_sum, map_zero, Fintype.sum_sigma] at h3
  have h4 : ∀ (w : Ω) (a : Fin (nb w.1)),
      weightedHomogeneousComponent (wv LLK (T.pos i + 1)) x0.1.1 (c ⟨w, a⟩ • f w.1 a) =
        if x0.1 = w then c ⟨w, a⟩ • f w.1 a else 0 := by
    intro w a
    have hW : IsWeightedHomogeneous (wv LLK (T.pos i + 1)) (f w.1 a) w.1 :=
      (wtsp_iff LLK (T.pos i + 1) w.1 _).mp (Submodule.mem_inf.mp (hf w.1 a)).2
    rw [map_smul, weightedHomogeneousComponent_of_mem hW]
    by_cases h : x0.1 = w
    · rw [if_pos h, if_pos (congrArg Subtype.val h)]
    · rw [if_neg h, if_neg (fun h' => h (Subtype.ext h')), smul_zero]
  simp only [h4] at h3
  rw [Finset.sum_eq_single x0.1 (fun w _ hw => by simp [Ne.symm hw]) (fun h => absurd (Finset.mem_univ _) h)] at h3
  simp only [if_true] at h3
  have := Fintype.linearIndependent_iff.mp (hli x0.1.1) (fun a => c ⟨x0.1, a⟩) h3 x0.2
  simpa using this
end Formalism.CountingSumsFrames.TO
