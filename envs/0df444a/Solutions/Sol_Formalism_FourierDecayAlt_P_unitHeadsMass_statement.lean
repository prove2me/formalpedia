-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.unitHeadsMass_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:51:59.583496+00:00
-- url     : https://prove2.me/submissions/5f9026f8-daa3-4ed4-86f7-58a89283914a

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderChainWeights
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrderChainWeights_ae_pi_all

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Finset MeasureTheory
open Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.OrderChainWeights
open scoped ENNReal
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.UnitHeadsMass := by
  intro X _ μ _ nrm Kk Rs Ru r hRs hRu hnrm hae hK
  set A := {c : Fin (r + 1) → X | ∀ l : Fin (r + 1), (l : ℕ) < r → c l ∈ Ru} with hAdef
  set B : Set (Fin (r + 1) → X) := Set.univ.pi fun l : Fin (r + 1) => if (l : ℕ) < r then Ru else Rs
    with hBdef
  have hBm : MeasurableSet B := by
    refine MeasurableSet.univ_pi fun l => ?_
    split_ifs
    · exact hRu
    · exact hRs
  have hBA : B ⊆ A := by
    intro c hc l hl
    have := hc l (Set.mem_univ _)
    simpa [hl] using this
  have hcongr : ∀ᵐ c ∂((Measure.pi fun _ : Fin (r + 1) => μ).restrict A),
      Kk (r + 1) c * chainWeight nrm (r + 1) c = B.indicator 1 c := by
    have hA : ∀ᵐ c ∂((Measure.pi fun _ : Fin (r + 1) => μ).restrict A), c ∈ A := by
      rw [ae_restrict_iff']
      · exact Filter.Eventually.of_forall fun c hc => hc
      · have : A = ⋂ l : Fin (r + 1), {c : Fin (r + 1) → X | (l : ℕ) < r → c l ∈ Ru} := by
          ext c
          simp [hAdef]
        rw [this]
        refine MeasurableSet.iInter fun l => ?_
        by_cases hl : (l : ℕ) < r
        · simp only [hl, true_implies]
          exact measurable_pi_apply l hRu
        · simp only [hl, false_implies, Set.setOf_true]
          exact MeasurableSet.univ
    filter_upwards [hA, ae_restrict_of_ae (ae_pi_all μ (r + 1) _ hae)] with c hcA hc0
    rw [hK c hcA (hc0 _)]
    have hw : chainWeight nrm (r + 1) c = 1 := by
      unfold chainWeight
      refine Finset.prod_eq_one fun l hl => Finset.prod_eq_one fun j _ => ?_
      split_ifs with hjl
      · have hl' := Finset.mem_range.mp hl
        rw [hnrm _ (hcA j (by omega)), one_pow]
      · rfl
    rw [hw, mul_one]
    by_cases hs : c (Fin.last r) ∈ Rs
    · have hcB : c ∈ B := by
        intro l _
        by_cases hl : (l : ℕ) < r
        · simp only [hl, if_true]
          exact hcA l hl
        · have hle : l = Fin.last r := Fin.ext (by have := l.is_lt; simp; omega)
          subst hle
          simpa using hs
      rw [Set.indicator_of_mem hs, Set.indicator_of_mem hcB]
      simp
    · have hcB : c ∉ B := by
        intro hmem
        apply hs
        have := hmem (Fin.last r) (Set.mem_univ _)
        simpa using this
      rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hcB]
  rw [lintegral_congr_ae hcongr, lintegral_indicator_one hBm, Measure.restrict_apply hBm,
    Set.inter_eq_left.mpr hBA, Measure.pi_pi, Fin.prod_univ_castSucc]
  simp [Finset.prod_const]
end Formalism.FourierDecayAlt.P
