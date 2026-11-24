-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.push_calc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:36:24.401124+00:00
-- url     : https://prove2.me/submissions/b3e7bcb9-5409-47a4-bf0f-793cfc1a1160

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Sq_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Vb_ne_top
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Vb_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_lint_Wf
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Ff_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Rf_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Jc_ne_top
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Jc_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_inner_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_outer_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoByOneBlock
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open Set
open scoped Pointwise
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
theorem _root_.solution (k : ℕ) (hk : 1 ≤ k) (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ ∀ φ : ℂ → ℝ≥0∞, Measurable φ →
      (∫⁻ u : Fin (k + 1) → ℂ in {u | 0 < Nq k u ∧ Nq k u ≤ T'},
          φ (((-(√T * √(T' / Nq k u)) : ℝ) : ℂ) * u (Fin.last k))) =
        c * ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k T T' ζ) * φ ζ := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hc0 : ((n + 1 : ℕ) * Vb (n + 1) : ℝ≥0∞) ≠ 0 := mul_ne_zero (by simp) (Vb_ne_zero _)
  have hct : ((n + 1 : ℕ) * Vb (n + 1) : ℝ≥0∞) ≠ ∞ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (Vb_ne_top _)
  refine ⟨((n + 1 : ℕ) * Vb (n + 1) : ℝ≥0∞) * Jc n T T', mul_ne_zero hc0 (Jc_ne_zero n hT hT'),
    ENNReal.mul_ne_top hct (Jc_ne_top n hT hT'), ?_⟩
  intro φ hφ
  rw [lint_Wf]
  have hNq : Measurable (Nq (n + 1)) := by
    unfold Nq
    exact (Complex.continuous_normSq.measurable.comp (measurable_pi_apply _)).sub
      (Finset.measurable_sum _ fun i _ => Complex.continuous_normSq.measurable.comp (measurable_pi_apply _))
  have hA : MeasurableSet {u : Fin (n + 1 + 1) → ℂ | 0 < Nq (n + 1) u ∧ Nq (n + 1) u ≤ T'} :=
    (measurableSet_lt measurable_const hNq).inter (measurableSet_le hNq measurable_const)
  rw [← lintegral_indicator hA]
  let Φ : ℂ × (Fin (n + 1) → ℂ) → ℝ≥0∞ := fun p => Ff T T' φ p.1 (Complex.normSq p.1 - Sq (n + 1) p.2)
  have hΦ : Measurable Φ :=
    (Ff_meas T T' hφ).comp (measurable_fst.prodMk ((Complex.continuous_normSq.measurable.comp measurable_fst).sub
      ((Sq_cont _).measurable.comp measurable_snd)))
  have e := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1 + 1) => ℂ) (Fin.last (n + 1))
  have h1 : ∀ u : Fin (n + 1 + 1) → ℂ,
      {u : Fin (n + 1 + 1) → ℂ | 0 < Nq (n + 1) u ∧ Nq (n + 1) u ≤ T'}.indicator
        (fun u => φ (((-(√T * √(T' / Nq (n + 1) u)) : ℝ) : ℂ) * u (Fin.last (n + 1)))) u =
      Φ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1 + 1) => ℂ) (Fin.last (n + 1)) u) := by
    intro u
    have hv : MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1 + 1) => ℂ) (Fin.last (n + 1)) u =
        (u (Fin.last (n + 1)), fun j : Fin (n + 1) => u j.castSucc) := by
      simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
      rfl
    rw [hv]
    show _ = (Ioc 0 T').indicator (fun s => φ (cs T T' s * u (Fin.last (n + 1)))) (Nq (n + 1) u)
    rw [Set.indicator_apply, Set.indicator_apply]
    rfl
  rw [lintegral_congr h1, e.lintegral_comp hΦ, Measure.volume_eq_prod, lintegral_prod _ hΦ.aemeasurable]
  have h2 : ∀ y : ℂ, (∫⁻ x : Fin (n + 1) → ℂ, Φ (y, x)) =
      ((n + 1 : ℕ) * Vb (n + 1) : ℝ≥0∞) * ∫⁻ s : ℝ, Rf n T T' φ y s := fun y => inner_eq n hT hT' hφ y
  have hJ : Measurable ((Ioc 0 T').indicator
      fun s : ℝ => ENNReal.ofReal ((s / (T * T')) ^ n) * ENNReal.ofReal (s / (T * T'))) :=
    ((ENNReal.measurable_ofReal.comp ((measurable_id.div_const _).pow_const _)).mul
      (ENNReal.measurable_ofReal.comp (measurable_id.div_const _))).indicator measurableSet_Ioc
  rw [lintegral_congr h2, lintegral_const_mul _ (Rf_meas n T T' hφ).lintegral_prod_right',
    lintegral_lintegral_swap (Rf_meas n T T' hφ).aemeasurable, lintegral_congr (outer_eq n hT hT' hφ),
    lintegral_mul_const _ hJ, lintegral_indicator measurableSet_Ioc]
  unfold Jc
  ring
end Formalism.FourierDecayAlt.P.TwoByOneBlock
