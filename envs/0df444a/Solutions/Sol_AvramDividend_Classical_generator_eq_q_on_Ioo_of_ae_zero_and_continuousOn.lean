-- Prove2me | solution 1 for AvramDividend.Classical.generator_eq_q_on_Ioo_of_ae_zero_and_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T13:03:53.452639+00:00
-- url     : https://prove2.me/submissions/3605e3cc-3753-4047-afe8-672539c2d93f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_continuousOn_zero_of_ae_zero_restrict_open

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (a : ℝ)
    (hcont : ContinuousOn (fun x : ℝ => X.generator W x - q * W x)
      (Ioo 0 a))
    (hae : ∀ᵐ x ∂(volume.restrict (Ioo 0 a)),
      X.generator W x - q * W x = 0) :
    ∀ x ∈ Ioo 0 a, X.generator W x - q * W x = 0 := by
  exact continuousOn_zero_of_ae_zero_restrict_open
    volume (Ioo 0 a) isOpen_Ioo
    (fun x : ℝ => X.generator W x - q * W x)
    hcont hae
