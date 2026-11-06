-- Prove2me | solution 2 for AvramDividend.Classical.avram_p3_2_original_physical_lefttag_C1_nonlinear_jump_source_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:20:39.861813+00:00
-- url     : https://prove2.me/submissions/f3de46dd-597d-4af0-bd70-af4a47fd21c6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_controlled_left_prestate_tendsto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (w : ℝ → ℝ) (U : Set ℝ)
    (hw : ContDiffOn ℝ 1 w U) (hU : IsOpen U)
    (T : Finset ℝ≥0) (hT : ∀ t ∈ T, 0 < t)
    (lefttag : ℕ → ℝ≥0 → ℝ≥0)
    (hTag : ∀ t ∈ T,
      Tendsto (fun k => lefttag k t) atTop (𝓝[<] t))
    (discount : ℝ≥0 → ℝ)
    (hInside : ∀ t ∈ T,
      Function.leftLim
        (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t ∈ U ∧
      (Function.leftLim
        (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t) + (X.X t ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) t) ∈ U) :
    Tendsto
      (fun k => T.sum (fun t =>
        discount t *
          (w ((x + X.X (lefttag k t) ω - rightLimit D (lefttag k t) ω) + (X.X t ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) t)) -
           w (x + X.X (lefttag k t) ω - rightLimit D (lefttag k t) ω)))) atTop
      (nhds (T.sum (fun t =>
        discount t *
          (w ((Function.leftLim
        (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t) + (X.X t ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) t)) -
           w (Function.leftLim
        (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t))))) := by
  apply tendsto_finset_sum T
  intro t ht
  let p : ℝ := Function.leftLim
    (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t
  let d : ℝ := X.X t ω -
    Function.leftLim (fun v : ℝ≥0 => X.X v ω) t
  have hz : Tendsto
      (fun k => x + X.X (lefttag k t) ω -
        rightLimit D (lefttag k t) ω)
      atTop (nhds p) :=
    (avram_p3_2_original_controlled_left_prestate_tendsto
      X x D hD ω t (hT t ht)).comp (hTag t ht)
  have hc1 : ContinuousAt w p :=
    hw.continuousOn.continuousAt (hU.mem_nhds (hInside t ht).1)
  have hc2 : ContinuousAt w (p + d) :=
    hw.continuousOn.continuousAt (hU.mem_nhds (hInside t ht).2)
  have hzplus : Tendsto
      (fun k => (x + X.X (lefttag k t) ω -
        rightLimit D (lefttag k t) ω) + d)
      atTop (nhds (p + d)) := hz.add tendsto_const_nhds
  have hwa : Tendsto
      (fun k => w ((x + X.X (lefttag k t) ω -
        rightLimit D (lefttag k t) ω) + d))
      atTop (nhds (w (p + d))) :=
    hc2.tendsto.comp hzplus
  have hwb : Tendsto
      (fun k => w (x + X.X (lefttag k t) ω -
        rightLimit D (lefttag k t) ω))
      atTop (nhds (w p)) :=
    hc1.tendsto.comp hz
  change Tendsto
    (fun k => discount t *
      (w ((x + X.X (lefttag k t) ω -
        rightLimit D (lefttag k t) ω) + d) -
       w (x + X.X (lefttag k t) ω -
        rightLimit D (lefttag k t) ω)))
    atTop (nhds (discount t * (w (p + d) - w p)))
  exact tendsto_const_nhds.mul (hwa.sub hwb)
