-- Prove2me | solution 2 for AvramDividend.Classical.valueFunctionLe_above_cap_of_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T19:18:48.327011+00:00
-- url     : https://prove2.me/submissions/90a9dbfc-ef22-48a9-9dd7-a9b8d622bdc7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_add_initial_excess_admissible_value
import Theorems.Thm_AvramDividend_Classical_strip_initial_excess_admissible_value

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x c : ℝ)
    (hc : 0 ≤ c) (hcx : c < x)
    (hne : ∃ E : ℝ≥0 → Ω → ℝ,
      IsAdmissibleLe X c (ENNReal.ofReal c) E) :
    valueFunctionLe X q (ENNReal.ofReal c) x =
      ENNReal.ofReal (x - c) + valueFunctionLe X q (ENNReal.ofReal c) c := by
  classical
  let C : ℝ≥0∞ := ENNReal.ofReal c
  let A : ℝ≥0∞ := ENNReal.ofReal (x - c)
  have hleft : valueFunctionLe X q C x ≤
      A + valueFunctionLe X q C c := by
    change (⨆ (D : ℝ≥0 → Ω → ℝ) (_ : IsAdmissibleLe X x C D),
      dividendValue X q x D) ≤ A + valueFunctionLe X q C c
    refine iSup_le fun D => iSup_le fun hD => ?_
    obtain ⟨hE, hval⟩ :=
      strip_initial_excess_admissible_value X q x c hc hcx D hD
    let E : ℝ≥0 → Ω → ℝ :=
      fun t ω => if t = 0 then 0 else D t ω - (x - c)
    calc
      dividendValue X q x D =
          A + dividendValue X q c E := hval
      _ ≤ A + valueFunctionLe X q C c := by
          apply add_le_add_right
          exact le_iSup_of_le E (le_iSup_of_le hE le_rfl)
  have hrepr :
      valueFunctionLe X q C c =
        ⨆ E : { E : ℝ≥0 → Ω → ℝ // IsAdmissibleLe X c C E },
          dividendValue X q c E.val := by
    unfold valueFunctionLe
    exact iSup_subtype'
  letI : Nonempty { E : ℝ≥0 → Ω → ℝ // IsAdmissibleLe X c C E } :=
    ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have hright : A + valueFunctionLe X q C c ≤
      valueFunctionLe X q C x := by
    rw [hrepr, ENNReal.add_iSup]
    refine iSup_le fun E => ?_
    obtain ⟨hD, hval⟩ :=
      add_initial_excess_admissible_value X q x c hc hcx E.val E.property
    calc
      A + dividendValue X q c E.val =
        dividendValue X q x
          (fun t ω => if t = 0 then 0 else (x - c) + E.val t ω) := hval.symm
      _ ≤ valueFunctionLe X q C x := by
        exact le_iSup_of_le
          (fun t ω => if t = 0 then 0 else (x - c) + E.val t ω)
          (le_iSup_of_le hD le_rfl)
  exact le_antisymm hleft hright

