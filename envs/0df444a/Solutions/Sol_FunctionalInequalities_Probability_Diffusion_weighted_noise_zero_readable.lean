-- Prove2me | solution 1 for FunctionalInequalities.Probability.Diffusion.weighted_noise_zero_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:18:00.660792+00:00
-- url     : https://prove2.me/submissions/b2b8c125-8519-4691-b01f-e421ff0fe682

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraAssociativity
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoZero
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Dynkin
import Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_stochasticIntegralBrownian_finsetSum_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_sq_bounded_mul_lt_top_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_ae_zero_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_const_mul_readable

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- The `L²` Itô integral depends on the integrand only through the function itself. -/
theorem LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {F₁ F₂ : Ω → ℝ → ℝ} (hEq : F₁ = F₂)
    (hm₁ : Measurable (Function.uncurry F₁))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ F₁)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry F₂))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ F₂)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (t : ℝ) :
    stochasticIntegralBrownian W ℱ hℱ F₁ hm₁ hp₁ hq₁ t
      = stochasticIntegralBrownian W ℱ hℱ F₂ hm₂ hp₂ hq₂ t := by
  subst hEq; rfl
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoZero.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
/-- A constant process is progressively measurable for any filtration. -/
theorem LevyStochCalc.Probability.progressivelyMeasurable_const {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    [TopologicalSpace E] [Zero E] (ℱ : Filtration ℝ mΩ) (c : E) :
    Probability.ProgressivelyMeasurable ℱ (fun (_ : Ω) (_ : ℝ) => c) := fun _ =>
  stronglyMeasurable_const.indicator
    (measurableSet_preimage measurable_snd measurableSet_Iic)
/-- The zero process is progressively measurable for any filtration. -/
theorem LevyStochCalc.Probability.progressivelyMeasurable_zero {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    [TopologicalSpace E] [Zero E] (ℱ : Filtration ℝ mΩ) :
    Probability.ProgressivelyMeasurable ℱ (fun (_ : Ω) (_ : ℝ) => (0 : E)) :=
  Probability.progressivelyMeasurable_const ℱ 0
end
end

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
  LevyStochCalc.Brownian.Ito
section Diffusion
variable {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure P] {N d : ℕ}
 theorem solution
    (W : LevyStochCalc.Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (H : Fin N → Ω → ℝ → ℝ)
    (hm : ∀ p, Measurable (Function.uncurry (H p)))
    (hp : ∀ p, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H p))
    (hq : ∀ p (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (c : Fin N → ℝ) (hz : ∀ ω s, ∑ p, c p * H p ω s = 0)
    {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∑ p, c p * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hW
      (H p) (hm p) (hp p) (hq p) T ω = 0 := by
  classical
  let K : Fin N → Ω → ℝ → ℝ := fun p ω s => c p * H p ω s
  have hkm (p : Fin N) : Measurable (Function.uncurry (K p)) :=
    measurable_const.mul (hm p)
  have hkp (p : Fin N) : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (K p) :=
    (LevyStochCalc.Probability.progressivelyMeasurable_const ℱ (c p)).mul (hp p)
  have hkq (p : Fin N) :
      ∀ T : ℝ, 0 < T →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖K p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    LevyStochCalc.Brownian.Ito.lintegral_sq_bounded_mul_lt_top_readable (hq p) (abs_nonneg (c p)) (fun _ _ => le_rfl)
  obtain ⟨hsm, hsp, hsq, hsum⟩ :=
    LevyStochCalc.Brownian.Ito.exists_stochasticIntegralBrownian_finsetSum_readable W ℱ hW K hkm hkp hkq Finset.univ hT
  have heq : (fun ω s => ∑ p, K p ω s) = fun (_ : Ω) (_ : ℝ) => (0 : ℝ) := by
    funext ω s
    exact hz ω s
  have hzm : Measurable (Function.uncurry fun (_ : Ω) (_ : ℝ) => (0 : ℝ)) :=
    measurable_const
  have hzp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) (_ : ℝ) => (0 : ℝ) :=
    LevyStochCalc.Probability.progressivelyMeasurable_zero ℱ
  have hzq : ∀ T : ℝ, 0 < T →
      ∫⁻ _ω : Ω, ∫⁻ _s in Set.Icc (0 : ℝ) T,
        (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro T _
    simp
  have hzero : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hW
      (fun ω s => ∑ p, K p ω s) hsm hsp hsq T =ᵐ[P] 0 := by
    rw [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hW heq hsm hsp hsq hzm hzp hzq T]
    exact LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_readable W ℱ hW hzm hzp hzq T
  have hscale : ∀ᵐ ω ∂P, ∀ p : Fin N,
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hW (K p) (hkm p) (hkp p) (hkq p) T ω =
        c p * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hW (H p) (hm p) (hp p) (hq p) T ω :=
    ae_all_iff.mpr fun p =>
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_const_mul_readable W ℱ hW (hm p) (hp p) (hq p) (c p)
        (hkm p) (hkp p) (hkq p) hT
  filter_upwards [hsum, hzero, hscale] with ω hs h0 hc
  calc
    ∑ p, c p * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hW (H p) (hm p) (hp p) (hq p) T ω =
        ∑ p, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hW (K p) (hkm p) (hkp p) (hkq p) T ω :=
      Finset.sum_congr rfl fun p _ => (hc p).symm
    _ = 0 := hs.symm.trans h0
