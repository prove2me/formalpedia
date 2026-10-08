-- Prove2me | solution 1 for AvramDividend.Classical.valueFunctionLe_above_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T14:31:05.596228+00:00
-- url     : https://prove2.me/submissions/81abfb69-2486-424f-b129-132689f633a7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_above_cap_of_nonempty
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_reserve_cap_bound
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_monotone
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_adapted
import Theorems.Thm_AvramDividend_Classical_rightLimit_eq_of_monotone_right_continuous
import Theorems.Thm_AvramDividend_Classical_admissible_of_no_right_dividend_jumps
import Theorems.Thm_AvramDividend_Classical_one_sided_limits_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_runningSup_left_continuous_of_no_upward_jump
import Theorems.Thm_AvramDividend_Classical_runningSup_right_continuous_of_right_continuous

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

private theorem samplePath_bddAbove_Icc_direct
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (u : ℝ≥0) :
    BddAbove (Set.range
      (fun s : Set.Icc (0 : ℝ≥0) u => X.X s.1 ω)) := by
  refine one_sided_limits_bddAbove_Icc (fun v => X.X v ω) ?_ ?_ u
  · intro v
    exact X.rightCont ω v
  · intro v
    by_cases hv : v = 0
    · subst v
      refine ⟨0, ?_⟩
      have hb : (𝓝[<] (0 : ℝ≥0)) = ⊥ :=
        nhdsLT_eq_bot_iff.mpr (.inl
          (fun z => (zero_le : (0 : ℝ≥0) ≤ z)))
      rw [hb]
      exact tendsto_bot
    · have hvpos : 0 < v :=
        lt_of_le_of_ne
          (zero_le : (0 : ℝ≥0) ≤ v) (Ne.symm hv)
      exact X.leftLim ω v hvpos

private theorem barrierStrategy_right_continuous_direct
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ) :
    ∀ ω (t : ℝ≥0),
      ContinuousWithinAt
        (fun s => barrierStrategy X c c s ω) (Ici t) t := by
  intro ω t
  have heq (s : ℝ≥0) :
      barrierStrategy X c c s ω = runningSup X s ω :=
    barrierStrategy_self_eq_runningSup X c ω s
  have hmono : Monotone (fun s => runningSup X s ω) := by
    intro s u hsu
    change runningSup X s ω ≤ runningSup X u ω
    rw [← heq s, ← heq u]
    exact barrierStrategy_monotone X c ω hsu
  have hdom (u : ℝ≥0) : X.X u ω ≤ runningSup X u ω := by
    have hraw := runningSup_eq_rawSup_nonneg X u ω
    rw [hraw.1]
    exact le_ciSup (samplePath_bddAbove_Icc_direct X ω u)
      ⟨u, ⟨(zero_le : (0 : ℝ≥0) ≤ u), le_rfl⟩⟩
  have hrepr (u : ℝ≥0) :
      runningSup X u ω =
        ⨆ s : Set.Icc (0 : ℝ≥0) u, X.X s.1 ω :=
    (runningSup_eq_rawSup_nonneg X u ω).1
  have hcont :
      ContinuousWithinAt (fun s => runningSup X s ω) (Ici t) t :=
    runningSup_right_continuous_of_right_continuous
      (fun u => X.X u ω) (fun u => runningSup X u ω)
      hmono hdom hrepr (fun u => X.rightCont ω u) t
  exact hcont.congr (fun s _ => heq s) (heq t)

private theorem barrierStrategy_left_continuous_direct
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ) :
    ∀ ω (t : ℝ≥0),
      ContinuousWithinAt
        (fun s => barrierStrategy X c c s ω) (Iic t) t := by
  intro ω t
  have heq (s : ℝ≥0) :
      barrierStrategy X c c s ω = runningSup X s ω :=
    barrierStrategy_self_eq_runningSup X c ω s
  have hmono : Monotone (fun s => runningSup X s ω) := by
    intro s u hsu
    change runningSup X s ω ≤ runningSup X u ω
    rw [← heq s, ← heq u]
    exact barrierStrategy_monotone X c ω hsu
  have hdom (u : ℝ≥0) : X.X u ω ≤ runningSup X u ω := by
    have hraw := runningSup_eq_rawSup_nonneg X u ω
    rw [hraw.1]
    exact le_ciSup (samplePath_bddAbove_Icc_direct X ω u)
      ⟨u, ⟨(zero_le : (0 : ℝ≥0) ≤ u), le_rfl⟩⟩
  have hrepr (u : ℝ≥0) :
      runningSup X u ω =
        ⨆ s : Set.Icc (0 : ℝ≥0) u, X.X s.1 ω :=
    (runningSup_eq_rawSup_nonneg X u ω).1
  have hcont :
      ContinuousWithinAt (fun s => runningSup X s ω) (Iic t) t := by
    by_cases ht : t = 0
    · subst t
      have hconst :
          ContinuousWithinAt
            (fun _ : ℝ≥0 => runningSup X 0 ω)
            (Iic (0 : ℝ≥0)) 0 :=
        continuousWithinAt_const
      refine hconst.congr ?_ rfl
      intro s hs
      have hs0 : s = 0 :=
        le_antisymm hs (zero_le : (0 : ℝ≥0) ≤ s)
      subst s
      rfl
    · have htpos : 0 < t :=
        lt_of_le_of_ne
          (zero_le : (0 : ℝ≥0) ≤ t) (Ne.symm ht)
      obtain ⟨ℓ, hleft⟩ := X.leftLim ω t htpos
      have hnoup : X.X t ω ≤ ℓ :=
        X.noPosJumps ω t ℓ htpos hleft
      exact continuousWithinAt_Iio_iff_Iic.mp
        (runningSup_left_continuous_of_no_upward_jump
          (fun u => X.X u ω) (fun u => runningSup X u ω)
          hmono hdom hrepr t htpos ℓ hleft hnoup)
  exact hcont.congr (fun s _ => heq s) (heq t)

private theorem barrierStrategy_capped_admissible_direct
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ) (hc : 0 ≤ c) :
    IsAdmissibleLe X c (ENNReal.ofReal c) (barrierStrategy X c c) := by
  have hm : ∀ ω, Monotone (fun t => barrierStrategy X c c t ω) :=
    barrierStrategy_monotone X c
  have hleft :
      ∀ ω (t : ℝ≥0),
        ContinuousWithinAt
          (fun s => barrierStrategy X c c s ω) (Iic t) t :=
    barrierStrategy_left_continuous_direct X c
  have hright :
      ∀ ω (t : ℝ≥0),
        ContinuousWithinAt
          (fun s => barrierStrategy X c c s ω) (Ici t) t :=
    barrierStrategy_right_continuous_direct X c
  have hadapt : Adapted 𝓕 (barrierStrategy X c c) :=
    barrierStrategy_adapted X c
  have hs : IsDividendStrategy 𝓕 (barrierStrategy X c c) := by
    refine ⟨?_, hm, hleft, hadapt⟩
    intro ω
    simp [barrierStrategy]
  have hrl : ∀ ω (t : ℝ≥0),
      rightLimit (barrierStrategy X c c) t ω =
        barrierStrategy X c c t ω := by
    intro ω t
    exact rightLimit_eq_of_monotone_right_continuous
      (barrierStrategy X c c) ω t (hm ω) (hright ω t)
  have ha : IsAdmissible X c (barrierStrategy X c c) :=
    admissible_of_no_right_dividend_jumps
      X c hc (barrierStrategy X c c) hs hrl
  exact ⟨ha, barrierStrategy_reserve_cap_bound X c⟩

end AvramDividend.Classical

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x c : ℝ)
    (hc : 0 ≤ c) (hcx : c < x) :
    valueFunctionLe X q (ENNReal.ofReal c) x =
      ENNReal.ofReal (x - c) +
        valueFunctionLe X q (ENNReal.ofReal c) c := by
  apply valueFunctionLe_above_cap_of_nonempty X q x c hc hcx
  exact ⟨barrierStrategy X c c,
    barrierStrategy_capped_admissible_direct X c hc⟩
