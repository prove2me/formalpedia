-- Prove2me | solution 3 for AvramDividend.Classical.cstar_finite_zero_or_deriv_minimal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-18T18:38:32.558449+00:00
-- url     : https://prove2.me/submissions/99144bf2-3ae2-4277-b601-c23b081a352b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Topology.Order.Monotone
import Mathlib.Order.LiminfLimsup
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_continuous
import Theorems.Thm_AvramDividend_Classical_continuous_argmin_sInf_zero_or_minimal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exact published cstar_finite_zero_or_deriv_minimal target.
    Depends on cstar_lt_top and scaleDeriv_continuous (both Open
    in the last checked Formalpedia snapshot), and on an already-Proved
    generic continuous-argmin closure theorem. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    cstar W < ⊤ ∧
      ((cstar W).toReal = 0 ∨
        (0 < (cstar W).toReal ∧
          ∀ x : ℝ, 0 < x →
            deriv W (cstar W).toReal ≤ deriv W x)) := by
  classical
  have hfinite := cstar_lt_top X hX q hq W hW
  refine ⟨hfinite, ?_⟩
  by_cases hne : (cstarSet W).Nonempty
  · have hto :
        (⨅ a ∈ cstarSet W, ENNReal.ofReal a).toReal =
          sInf (cstarSet W) := by
      rw [iInf_subtype', ENNReal.toReal_iInf]
      · calc
          (⨅ a : cstarSet W, (ENNReal.ofReal (a : ℝ)).toReal) =
              ⨅ a : cstarSet W, (a : ℝ) := by
                apply iInf_congr
                intro a
                rw [ENNReal.toReal_ofReal]
                exact le_of_lt a.property.1
          _ = sInf (cstarSet W) := (sInf_eq_iInf' _).symm
      · intro a
        exact ENNReal.ofReal_ne_top
    have hcTo : (cstar W).toReal = sInf (cstarSet W) := by
      rw [cstar, if_pos hne]
      exact hto
    have hcont := scaleDeriv_continuous X hX q hq W hW
    have harg := continuous_argmin_sInf_zero_or_minimal
      (deriv W) hcont hne
    change sInf (cstarSet W) = 0 ∨
      (0 < sInf (cstarSet W) ∧
        ∀ x : ℝ, 0 < x →
          deriv W (sInf (cstarSet W)) ≤ deriv W x) at harg
    rw [hcTo]
    exact harg
  · by_cases hzero : ∀ x : ℝ, 0 < x →
        derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal)
    · left
      rw [cstar, if_neg hne, if_pos hzero]
      rfl
    · have htop : cstar W = ⊤ := by
        rw [cstar, if_neg hne, if_neg hzero]
      rw [htop] at hfinite
      exact False.elim (lt_irrefl _ hfinite)
