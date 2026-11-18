-- Prove2me | solution 1 for FengLiYangMatching.General.expected_accounting
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T18:22:23.725811+00:00
-- url     : https://prove2.me/submissions/af1b3148-69fa-4b7e-b128-5f85370938a8

import Theorems.Thm_FengLiYangMatching_General_output_accounting
import Theorems.Thm_FengLiYangMatching_General_recovery_in_expectation
import Theorems.Thm_FengLiYangMatching_General_lemma_2_4
import Theorems.Thm_FengLiYangMatching_General_lemma_2_5
import Theorems.Thm_FengLiYangMatching_General_survival_moments
open MeasureTheory Finset Classical
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

lemma accounting_reduction {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n)
    (hMG : M ⊆ graphEdges G) (hM : IsMatching M) (hmax : M.card = OPT G)
    (a : ℝ) (ha : 0 ≤ a) (hab : a < 3/8) :
    (∫ w, ALG G a (3/8) w ∂sampleLaw G (5/11)) ≥ (6/11 : ℝ) * OPT G +
      (1/2 : ℝ) * (∫ t, ((M2 G M a (3/8) t).card : ℝ) ∂arrivalLaw G) -
      (1/22 : ℝ) * (∫ t, U G M t a ∂arrivalLaw G) -
      (1/10 : ℝ) * (∫ t, U G M t (3/8) ∂arrivalLaw G) := by
  haveI : IsProbabilityMeasure (arrivalLaw G) := by
    haveI : IsProbabilityMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) := ⟨by simp⟩
    unfold arrivalLaw RandomOrderCRS.arrivalTimeLaw
    infer_instance
  obtain ⟨hTa,hTb,hZ,hALG⟩ := output_accounting G a ha hab
  obtain ⟨hM1,hYY,hRec⟩ := recovery_in_expectation G M hMG hM hmax a ha hab
  obtain ⟨hU,hM2,hM2val⟩ := survival_moments G M hMG hM hmax a ha hab
  have hUa := (hU a ⟨ha,le_of_lt hab⟩).1
  have hUb := (hU (3/8) ⟨by norm_num,le_refl _⟩).1
  have hYYval : (fun t : Times G => ((MYY M (history G (3/8) t)).card : ℝ)) = (fun t => U G M t (3/8)) := by
    funext t
    have heq : MYY M (history G (3/8) t) = M.filter (free (shadowAt G t (3/8))) := by
      ext e
      simp only [MYY,free,Yset,history,History.accepted,Finset.mem_filter,Finset.mem_sdiff,Finset.mem_univ,true_and]
    rw [heq]
    rfl
  have hBaseI := (integrable_const (μ := arrivalLaw G) (2*(OPT G:ℝ))).sub (hTb.const_mul 2)
  have hMidI := hBaseI.sub hUa
  have h24 := integral_mono (hMidI.add hM2) (hM1.add hYY)
    (fun t => lemma_2_4 G M hMG hM hmax a (3/8) (5/11) ha hab (by norm_num) (by norm_num) (by norm_num) t)
  simp only [Pi.add_apply,Pi.sub_apply] at h24
  have hA := integral_add hMidI hM2
  have hB := integral_sub hBaseI hUa
  have hC := integral_sub (integrable_const (μ := arrivalLaw G) (2*(OPT G:ℝ))) (hTb.const_mul 2)
  have hLeft := integral_add hM1 hYY
  simp only [Pi.add_apply,Pi.sub_apply] at hA hB hC hLeft
  rw [hA,hB,hC,hLeft,integral_const_mul,integral_const] at h24
  simp only [integral_const_mul] at h24
  simp only [Measure.real,measure_univ,ENNReal.toReal_one,one_smul] at h24
  have h25 := integral_mono ((hUa.sub hUb).add hM2) ((hTb.sub hTa).const_mul 2)
    (fun t => lemma_2_5 G M hMG hM hmax a (3/8) (5/11) ha hab (by norm_num) (by norm_num) (by norm_num) t)
  simp only [Pi.add_apply,Pi.sub_apply] at h25
  have hD := integral_add (hUa.sub hUb) hM2
  have hE := integral_sub hUa hUb
  have hF := integral_sub hTb hTa
  simp only [Pi.add_apply,Pi.sub_apply] at hD hE hF
  rw [hD,hE,integral_const_mul,hF] at h25
  rw [hYYval] at h24 hRec
  linarith only [hALG,hRec,h24,h25]

end
end FengLiYangMatching.General

open FengLiYangMatching.General


theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n)
    (hMG : M ⊆ graphEdges G) (hM : IsMatching M) (hmax : M.card = OPT G)
    (a : ℝ) (ha : 0 ≤ a) (hab : a < 3/8) :
    (∫ w, ALG G a (3/8) w ∂sampleLaw G (5/11)) ≥ (6/11 : ℝ) * OPT G +
      (1/2 : ℝ) * (∫ t, ((M2 G M a (3/8) t).card : ℝ) ∂arrivalLaw G) -
      (1/22 : ℝ) * (∫ t, U G M t a ∂arrivalLaw G) -
      (1/10 : ℝ) * (∫ t, U G M t (3/8) ∂arrivalLaw G) := by
  exact accounting_reduction G M hMG hM hmax a ha hab


