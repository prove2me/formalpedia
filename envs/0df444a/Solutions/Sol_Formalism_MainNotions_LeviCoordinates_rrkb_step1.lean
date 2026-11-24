-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrkb_step1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:38:59.494116+00:00
-- url     : https://prove2.me/submissions/9f472e94-757f-4503-a4e7-9f5e1659ae67

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkAesmTsum
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkbLeOneAddSq
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrkb_le_one_add_sq
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrkb_sq_fin
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrkb_lint
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_rep_ae_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  {Γ : Subgroup G} [Countable Γ] {D : Set G}
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (h : rr_FD μ Γ D) {φ : G → ℂ} (hφm : Measurable φ) {r : G → G} (hrm : Measurable r)
    (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D)
    {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))} (hR : rr_IsReg μ Γ D R)
    (T : Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D)) (hφ : Integrable φ μ)
    (hT : ∀ u v : Lp ℂ 2 (μ.restrict D), ⟪u, T v⟫_ℂ = ∫ g, φ g * ⟪u, R g v⟫_ℂ ∂μ) (f : Lp ℂ 2 (μ.restrict D)) :
    ((T f : Lp ℂ 2 (μ.restrict D)) : G → ℂ) =ᵐ[μ.restrict D] fun x => ∫ g, φ g * (f : G → ℂ) (r (x * g)) ∂μ := by
  set f0 : G → ℂ := (f : G → ℂ) with hf0
  have hf0m : StronglyMeasurable f0 := Lp.stronglyMeasurable f
  set Φ : G × G → ℂ := fun p => φ p.1 * f0 (r (p.2 * p.1)) with hΦ
  have hΦm : StronglyMeasurable Φ :=
    ((hφm.comp measurable_fst).stronglyMeasurable).mul
      (hf0m.comp_measurable (hrm.comp (measurable_snd.mul measurable_fst)))
  have hInt : ∀ s, MeasurableSet s → (μ.restrict D) s < ∞ →
      Integrable Φ (μ.prod ((μ.restrict D).restrict s)) := by
    intro s hs hfin
    refine ⟨hΦm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hΦm.enorm.aemeasurable]
    set C : ℝ≥0∞ := (μ.restrict D) s + ∫⁻ y in D, ‖f0 y‖ₑ ^ 2 ∂μ with hC
    have hCfin : C ≠ ∞ := ENNReal.add_ne_top.2 ⟨hfin.ne, rrkb_sq_fin f⟩
    have hb : ∀ g, ∫⁻ x, ‖Φ (g, x)‖ₑ ∂((μ.restrict D).restrict s) ≤ ‖φ g‖ₑ * C := by
      intro g
      have hm1 : Measurable fun x => ‖f0 (r (x * g))‖ₑ :=
        (hf0m.comp_measurable (hrm.comp (measurable_mul_const g))).enorm
      simp only [hΦ, enorm_mul]
      rw [lintegral_const_mul _ hm1]
      refine mul_le_mul' le_rfl ?_
      calc ∫⁻ x, ‖f0 (r (x * g))‖ₑ ∂((μ.restrict D).restrict s)
          ≤ ∫⁻ x, (1 + ‖f0 (r (x * g))‖ₑ ^ 2) ∂((μ.restrict D).restrict s) :=
            lintegral_mono fun x => rrkb_le_one_add_sq _
        _ = (μ.restrict D) s + ∫⁻ x, ‖f0 (r (x * g))‖ₑ ^ 2 ∂((μ.restrict D).restrict s) := by
            rw [lintegral_add_left measurable_const, lintegral_one, Measure.restrict_apply_univ]
        _ ≤ (μ.restrict D) s + ∫⁻ x in D, ‖f0 (r (x * g))‖ₑ ^ 2 ∂μ :=
            add_le_add le_rfl (lintegral_mono' Measure.restrict_le_self le_rfl)
        _ = C := by rw [rrkb_lint h hr g (F := fun y => ‖f0 y‖ₑ ^ 2) (hf0m.enorm.pow_const 2)]
    calc ∫⁻ g, ∫⁻ x, ‖Φ (g, x)‖ₑ ∂((μ.restrict D).restrict s) ∂μ ≤ ∫⁻ g, ‖φ g‖ₑ * C ∂μ := lintegral_mono hb
      _ = (∫⁻ g, ‖φ g‖ₑ ∂μ) * C := lintegral_mul_const _ hφm.enorm
      _ < ∞ := ENNReal.mul_lt_top hφ.2 (lt_top_iff_ne_top.2 hCfin)
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite ?_ ?_ ?_
  · intro s hs hfin
    exact integrableOn_Lp_of_measure_ne_top _ (by norm_num) hfin.ne
  · intro s hs hfin
    exact (hInt s hs hfin).integral_prod_right
  · intro s hs hfin
    rw [← L2.inner_indicatorConstLp_one (𝕜 := ℂ) hs hfin.ne (T f), hT]
    have e : ∀ g, ⟪indicatorConstLp 2 hs hfin.ne (1 : ℂ), R g f⟫_ℂ =
        ∫ x in s, f0 (r (x * g)) ∂(μ.restrict D) := by
      intro g
      rw [L2.inner_indicatorConstLp_one]
      refine integral_congr_ae (ae_restrict_of_ae ?_)
      filter_upwards [hR g f, ae_restrict_of_ae (s := D) (rr_rep_ae_eq h hr g)] with x a1 a2
      rw [a1, a2]
    simp only [e]
    have hsw := integral_integral_swap (f := fun g x => φ g * f0 (r (x * g))) (μ := μ)
      (ν := (μ.restrict D).restrict s) (hInt s hs hfin)
    rw [← hsw]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    exact (integral_const_mul _ _).symm
end Formalism.MainNotions.LeviCoordinates
