-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C.t_ClassSquaresSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:13.262342+00:00
-- url     : https://prove2.me/submissions/155e922c-108b-42ea-be19-d8a63514d874

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_C_normsq_tsum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C
theorem _root_.solution : Formalism.FourierDecayAlt.PN.ClassSquaresSum := by
  intro ι C V _ _ _ v cl hv
  classical
  set A : C → ι → V := fun c => ({i | cl i = c} : Set ι).indicator v with hA
  have hAn : ∀ c, Summable (fun i => ‖A c i‖) := by
    intro c
    have : (fun i => ‖A c i‖) = ({i | cl i = c} : Set ι).indicator (fun i => ‖v i‖) := by
      funext i
      simp only [hA]
      exact norm_indicator_eq_indicator_norm _ _
    rw [this]
    exact hv.indicator _
  set G : C × (ι × ι) → ℝ := fun x => (inner ℂ (A x.1 x.2.1) (A x.1 x.2.2) : ℂ).re with hG
  set F : ι × ι → ℝ := ({p | cl p.1 = cl p.2} : Set (ι × ι)).indicator
        (fun p => (inner ℂ (v p.1) (v p.2) : ℂ).re) with hF
  set emb : ι × ι → C × (ι × ι) := fun p => (cl p.1, p) with hemb
  have hinj : Function.Injective emb := by
    intro p p' h
    exact (Prod.ext_iff.1 h).2
  have hGF : ∀ p, G (emb p) = F p := by
    intro p
    simp only [hG, hF, hemb, hA]
    by_cases h : cl p.1 = cl p.2
    · simp [Set.indicator, h]
    · have h' : ¬ cl p.2 = cl p.1 := fun e => h e.symm
      simp [Set.indicator, h, h']
  have hsupp : ∀ x, x ∉ Set.range emb → G x = 0 := by
    intro x hx
    have hc : ¬ cl x.2.1 = x.1 := by
      intro e
      exact hx ⟨x.2, by simp [hemb, e]⟩
    simp [hG, hA, Set.indicator, hc]
  have hFs : Summable F := by
    refine Summable.of_norm_bounded (g := fun p : ι × ι => ‖v p.1‖ * ‖v p.2‖)
      (Summable.mul_of_nonneg hv hv (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)) ?_
    intro p
    simp only [hF]
    by_cases h : cl p.1 = cl p.2
    · simp only [Set.indicator, Set.mem_ofPred_eq, h, if_true]
      exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
    · simp only [Set.indicator, Set.mem_ofPred_eq, h, if_false, norm_zero]
      positivity
  have hGs : Summable G := by
    rw [← hinj.summable_iff hsupp]
    have : G ∘ emb = F := funext hGF
    rw [this]; exact hFs
  have hrow : ∀ c, ∑' p : ι × ι, G (c, p) = ‖∑' i, A c i‖ ^ 2 := by
    intro c
    exact (normsq_tsum (A c) (hAn c)).symm
  constructor
  · have := hGs.prod
    simpa only [hrow] using this
  · have e1 : ∑' p, F p = ∑' x, G x := by
      rw [← hinj.tsum_eq (f := G)]
      · exact tsum_congr (fun p => (hGF p).symm)
      · intro x hx
        by_contra hn
        exact hx (hsupp x hn)
    rw [e1, hGs.tsum_prod]
    exact tsum_congr hrow
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C
