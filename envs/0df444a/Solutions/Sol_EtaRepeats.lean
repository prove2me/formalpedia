-- Prove2me | solution 1 for EtaRepeats
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:57:09.757732+00:00
-- url     : https://prove2.me/submissions/41f43652-4e4f-4abe-b30f-135b58f21135

import Definitions.Def_Tablet_psi
import Definitions.Def_Tablet_PSFamily
import Definitions.Def_Tablet_CurveLenMeasurable
import Definitions.Def_Tablet_CurveRestrictTotAgrees
import Definitions.Def_Tablet_CurveScaledEvalMeasurable
import Definitions.Def_Tablet_CurveRestrictTotMeasurable
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_PsiReindex
import Definitions.Def_Tablet_PsiMeasurable
import Definitions.Def_Tablet_EtaRepeats
import Theorems.Thm_CurveLenMeasurable
import Theorems.Thm_CurveRestrictTotAgrees
import Theorems.Thm_CurveRestrictTotMeasurable
import Theorems.Thm_CurveScaledEvalMeasurable
import Theorems.Thm_PsiMeasurable
import Theorems.Thm_PsiReindex


set_option autoImplicit false
open MeasureTheory
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : Form1 E → ℝ) (F : PSFamily T)
    (m : ℕ) (hm : 0 < m) (Q : Finset E) (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C)
    (l : ℕ) (hl : 0 < l) :
    ∫ γ, (l : ℝ)⁻¹ * psi (m * l) Q ε C γ ∂(F.eta l)
      = ∫ γ, psi m Q ε C γ ∂(F.eta 1) := by
-- BODY
  have := F.finite l
  have := F.finite 1
  have hlR : (0:ℝ) < (l:ℝ) := by exact_mod_cast hl
  have hlne : (l:ℝ) ≠ 0 := ne_of_gt hlR
  -- Step 1: measurability of `ψ_{m,Q,ε,C}`.
  have hmeas : Measurable (fun γ : Curve E => psi m Q ε C γ) := PsiMeasurable m Q ε C
  -- Step 2: the a priori bound (psi-bound).
  have hbound : ∀ N : ℕ, 0 < N → ∀ g : Curve E,
      0 ≤ psi N Q ε C g ∧ psi N Q ε C g ≤ 2 * C ^ 2 * g.len + 2 * C ^ 2 * g.len ^ 2 / (N : ℝ) := by
    intro N hN g
    have hNR : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hgl : (0:ℝ) ≤ g.len := g.len_nonneg
    have hfst : (0:ℝ) ≤ 2 * C * g.len / (N : ℝ) :=
      div_nonneg (by nlinarith [mul_nonneg hC.le hgl]) hNR.le
    have htail : (0:ℝ) ≤ 2 * C ^ 2 * g.len ^ 2 / (N : ℝ) := by positivity
    unfold psi
    constructor
    · refine le_add_of_nonneg_of_le (mul_nonneg hC.le (Finset.sum_nonneg ?_)) htail
      intro i _
      refine le_min hfst ?_
      have h1 : (0:ℝ) ≤ Metric.infDist (g.toFun ((i : ℝ) * g.len / (N : ℝ))) (Q : Set E) :=
        Metric.infDist_nonneg
      have h2 : (0:ℝ) ≤ Metric.infDist (g.toFun (((i : ℝ) - 1) * g.len / (N : ℝ))) (Q : Set E) :=
        Metric.infDist_nonneg
      nlinarith
    · have hsum := Finset.sum_le_sum (f := fun i : ℕ =>
        min (2 * C * g.len / (N : ℝ))
          (2 * ε + 2 * C * (Metric.infDist (g.toFun ((i : ℝ) * g.len / (N : ℝ))) (Q : Set E)
            + Metric.infDist (g.toFun (((i : ℝ) - 1) * g.len / (N : ℝ))) (Q : Set E))))
        (g := fun _ : ℕ => 2 * C * g.len / (N : ℝ)) (s := Finset.Icc 1 N)
        (fun i _ => min_le_left _ _)
      rw [Finset.sum_const, Nat.card_Icc] at hsum
      simp only [nsmul_eq_mul, Nat.add_sub_cancel] at hsum
      have hNc : (N : ℝ) * (2 * C * g.len / (N : ℝ)) = 2 * C * g.len := by
        field_simp
      rw [hNc] at hsum
      nlinarith [mul_le_mul_of_nonneg_left hsum hC.le]
  -- almost-everywhere length facts from `PSFamily.lengthExactly`
  have hlen_ae : ∀ᵐ γ ∂(F.eta l), γ.len = (l : ℝ) := F.lengthExactly l hl
  -- The `j`-th unit subcurve has length `1` for `η_l`-a.e. `γ`.
  have hrest_len : ∀ j : ℕ, 1 ≤ j → j ≤ l →
      ∀ᵐ γ ∂(F.eta l), (curveRestrictTot γ ((j : ℝ) - 1) (j : ℝ)).len = 1 := by
    intro j hj1 hjl
    filter_upwards [hlen_ae] with γ hγ
    have hj1R : (1:ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    have hjlR : (j : ℝ) ≤ (l : ℝ) := by exact_mod_cast hjl
    have ha : (0:ℝ) ≤ (j : ℝ) - 1 := by linarith
    have hab : (j : ℝ) - 1 ≤ (j : ℝ) := by linarith
    have hb : (j : ℝ) ≤ γ.len := by rw [hγ]; exact hjlR
    rw [CurveRestrictTotAgrees γ _ _ ha hab hb]
    show (j : ℝ) - ((j : ℝ) - 1) = 1
    ring
  -- Step 3 (integrability): each restricted summand is `η_l`-integrable.
  have hintj : ∀ j : ℕ, 1 ≤ j → j ≤ l →
      Integrable (fun γ : Curve E => psi m Q ε C (curveRestrictTot γ ((j : ℝ) - 1) (j : ℝ)))
        (F.eta l) := by
    intro j hj1 hjl
    refine Integrable.mono'
      (integrable_const (2 * C ^ 2 * (1:ℝ) + 2 * C ^ 2 * (1:ℝ) ^ 2 / (m : ℝ)))
      ((hmeas.comp (CurveRestrictTotMeasurable ((j : ℝ) - 1) (j : ℝ))).aestronglyMeasurable) ?_
    filter_upwards [hrest_len j hj1 hjl] with γ hγ
    obtain ⟨h0, hu⟩ := hbound m hm (curveRestrictTot γ ((j : ℝ) - 1) (j : ℝ))
    rw [hγ] at hu
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact hu
  -- Step 4: the marginal identity, transported through `ENNReal.ofReal`/`toReal`.
  have hmarg : ∀ j : ℕ, 1 ≤ j → j ≤ l →
      ∫ γ, psi m Q ε C (curveRestrictTot γ ((j : ℝ) - 1) (j : ℝ)) ∂(F.eta l)
        = ∫ γ, psi m Q ε C γ ∂(F.eta 1) := by
    intro j hj1 hjl
    rw [integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall (fun γ => (hbound m hm
          (curveRestrictTot γ ((j : ℝ) - 1) (j : ℝ))).1))
        ((hmeas.comp (CurveRestrictTotMeasurable ((j : ℝ) - 1) (j : ℝ))).aestronglyMeasurable),
      integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall (fun γ => (hbound m hm γ).1))
        hmeas.aestronglyMeasurable]
    congr 1
    exact F.marginal l j hj1 hjl (fun γ => ENNReal.ofReal (psi m Q ε C γ))
      (ENNReal.measurable_ofReal.comp hmeas)
  -- Step 5: assemble.
  rw [integral_const_mul]
  have hstep3 : ∫ γ, psi (m * l) Q ε C γ ∂(F.eta l)
      = ∑ j ∈ Finset.Icc 1 l,
          ∫ γ, psi m Q ε C (curveRestrictTot γ ((j : ℝ) - 1) (j : ℝ)) ∂(F.eta l) := by
    rw [← MeasureTheory.integral_finsetSum _
      (fun j hj => hintj j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2)]
    refine integral_congr_ae ?_
    filter_upwards [hlen_ae] with γ hγ
    exact PsiReindex m l hm hl Q ε C γ hγ
  rw [hstep3, Finset.sum_congr rfl
      (fun j hj => hmarg j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2),
    Finset.sum_const, Nat.card_Icc]
  simp only [nsmul_eq_mul, Nat.add_sub_cancel]
  rw [← mul_assoc, inv_mul_cancel₀ hlne, one_mul]
