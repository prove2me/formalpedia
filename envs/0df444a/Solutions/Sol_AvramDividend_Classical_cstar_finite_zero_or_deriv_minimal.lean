-- Prove2me | solution 1 for AvramDividend.Classical.cstar_finite_zero_or_deriv_minimal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T08:23:30.206116+00:00
-- url     : https://prove2.me/submissions/2299b9a9-3fc1-492d-9900-efae0b712221
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_inf_attained
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_continuous
import Theorems.Thm_AvramDividend_Classical_continuous_argmin_sInf_zero_or_minimal

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    cstar W < ⊤ ∧
      ((cstar W).toReal = 0 ∨
        (0 < (cstar W).toReal ∧
          ∀ x : ℝ, 0 < x → deriv W (cstar W).toReal ≤ deriv W x)) := by
  have hfin := cstar_lt_top X hX q hq W hW
  refine ⟨hfin, ?_⟩
  by_cases hne : (cstarSet W).Nonempty
  · have hcont := scaleDeriv_continuous X hX q hq W hW
    have harg :=
      continuous_argmin_sInf_zero_or_minimal (deriv W) hcont (by simpa [cstarSet] using hne)
    have hto :
        (⨅ a ∈ cstarSet W, ENNReal.ofReal a).toReal = sInf (cstarSet W) := by
      rw [iInf_subtype', ENNReal.toReal_iInf]
      · calc
          (⨅ a : cstarSet W, (ENNReal.ofReal (a : ℝ)).toReal)
              = ⨅ a : cstarSet W, (a : ℝ) := by
                  apply iInf_congr
                  intro a
                  rw [ENNReal.toReal_ofReal]
                  exact le_of_lt (by simpa [cstarSet] using a.property.1)
          _ = sInf (cstarSet W) := (sInf_eq_iInf' _).symm
      · intro a
        exact ENNReal.ofReal_ne_top
    rw [cstar, if_pos hne, hto]
    simpa [cstarSet] using harg
  · have hzero :
        ∀ x : ℝ, 0 < x →
          derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal) := by
      rcases scaleDeriv_inf_attained X hX q hq W hW with hmin | hz
      · exfalso
        exact hne ⟨hmin.choose, hmin.choose_spec.1, hmin.choose_spec.2⟩
      · exact hz
    rw [cstar, if_neg hne, if_pos hzero]
    exact Or.inl rfl
