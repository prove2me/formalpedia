-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_left_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:54:46.721194+00:00
-- url     : https://prove2.me/submissions/178d3d83-d240-4c39-9a4f-688e4f8bca4b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option autoImplicit false

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

open MeasureTheory Filter Set Topology in
theorem p61a2636f_bdd {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0) :
    ∃ B, ∀ v ∈ Icc (0 : ℝ≥0) t, X.X v ω ≤ B := by
  have key : BddAbove ((fun s => X.X s ω) '' Icc 0 t) := by
    refine (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).induction_on
      (p := fun S => BddAbove ((fun s => X.X s ω) '' S)) ?_ ?_ ?_ ?_
    · simp
    · intro s u hsu hu
      exact hu.mono (image_mono hsu)
    · intro s u hs hu
      rw [image_union]
      exact hs.union hu
    · intro x _
      obtain ⟨B1, h1⟩ : ∃ B1, ∀ᶠ s in 𝓝[<] x, X.X s ω ≤ B1 := by
        rcases eq_or_ne x 0 with rfl | hx
        · refine ⟨0, ?_⟩
          have : Iio (0 : ℝ≥0) = ∅ := by ext; simp
          rw [this, nhdsWithin_empty]
          exact Filter.eventually_bot
        · obtain ⟨l, hl⟩ := X.leftLim ω x (pos_iff_ne_zero.2 hx)
          exact ⟨l + 1, hl.eventually (eventually_le_nhds (by linarith))⟩
      have h2 : ∀ᶠ s in 𝓝[≥] x, X.X s ω ≤ X.X x ω + 1 :=
        (X.rightCont ω x).eventually (eventually_le_nhds (by linarith))
      refine ⟨{s | X.X s ω ≤ max B1 (X.X x ω + 1)}, nhdsWithin_le_nhds ?_, ?_⟩
      · rw [← nhdsLT_sup_nhdsGE]
        exact Filter.eventually_sup.2 ⟨h1.mono fun s hs => le_max_of_le_left hs,
          h2.mono fun s hs => le_max_of_le_right hs⟩
      · exact ⟨max B1 (X.X x ω + 1), by rintro _ ⟨s, hs, rfl⟩; exact hs⟩
  obtain ⟨B, hB⟩ := key
  exact ⟨B, fun v hv => hB ⟨v, hv, rfl⟩⟩

open MeasureTheory Filter Set Topology NNReal ENNReal AvramDividend.Classical in
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ) :
    ∀ ω (t : ℝ≥0),
      ContinuousWithinAt (fun s => barrierStrategy X c c s ω) (Iic t) t := by
  intro ω t
  rcases eq_or_ne t 0 with rfl | ht
  · have : Iic (0 : ℝ≥0) = {0} := by ext; simp
    rw [this]
    exact continuousWithinAt_singleton
  obtain ⟨B, hB⟩ := p61a2636f_bdd X ω t
  set M : ℝ≥0 → ℝ := fun s => ⨆ v : Icc (0 : ℝ≥0) s, X.X v ω with hMdef
  have hne : ∀ s : ℝ≥0, Nonempty (Icc (0 : ℝ≥0) s) := fun s => ⟨⟨0, le_rfl, zero_le⟩⟩
  have bddS : ∀ s ≤ t, BddAbove (range fun v : Icc (0 : ℝ≥0) s => X.X v ω) := by
    intro s hs
    refine ⟨B, ?_⟩
    rintro _ ⟨v, rfl⟩
    exact hB v ⟨v.2.1, v.2.2.trans hs⟩
  have Mle : ∀ s ≤ t, M s ≤ M t := by
    intro s hs
    have := hne s
    exact ciSup_le fun v => le_ciSup (bddS t le_rfl) (⟨v, v.2.1, v.2.2.trans hs⟩ : Icc (0 : ℝ≥0) t)
  have fval : ∀ s : ℝ≥0, s ≠ 0 → barrierStrategy X c c s ω = max 0 (M s) := by
    intro s hs
    simp [barrierStrategy, hs, M]
  have f0 : barrierStrategy X c c 0 ω = 0 := by simp [barrierStrategy]
  have fnn : ∀ s, 0 ≤ barrierStrategy X c c s ω := by
    intro s
    rcases eq_or_ne s 0 with rfl | hs
    · rw [f0]
    · rw [fval s hs]; exact le_max_left _ _
  have fle : ∀ s ≤ t, barrierStrategy X c c s ω ≤ max 0 (M t) := by
    intro s hs
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [f0]; exact le_max_left _ _
    · rw [fval s hs0]; exact max_le_max le_rfl (Mle s hs)
  rw [ContinuousWithinAt, fval t ht]
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rcases lt_max_iff.1 ha with h0 | hM
    · exact Filter.Eventually.of_forall fun s => lt_of_lt_of_le h0 (fnn s)
    · have := hne t
      obtain ⟨u, hu⟩ := exists_lt_of_lt_ciSup hM
      obtain ⟨w, hwt, hw⟩ : ∃ w < t, a < X.X w ω := by
        rcases lt_or_eq_of_le u.2.2 with h | h
        · exact ⟨u, h, hu⟩
        · have htpos : 0 < t := pos_iff_ne_zero.2 ht
          obtain ⟨l, hl⟩ := X.leftLim ω t htpos
          have hXl := X.noPosJumps ω t l htpos hl
          have hu' : a < X.X t ω := by rw [← h]; exact hu
          have : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
          have hev : ∀ᶠ s in 𝓝[<] t, a < X.X s ω :=
            hl.eventually (eventually_gt_nhds (by linarith))
          obtain ⟨w, hw1, hw2⟩ := (hev.and self_mem_nhdsWithin).exists
          exact ⟨w, hw2, hw1⟩
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hwt), self_mem_nhdsWithin]
        with s hs hst
      have hs0 : s ≠ 0 := ne_of_gt (lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ w) hs)
      rw [fval s hs0]
      refine lt_of_lt_of_le hw (le_trans ?_ (le_max_right _ _))
      exact le_ciSup (bddS s hst) (⟨w, zero_le, le_of_lt hs⟩ : Icc (0 : ℝ≥0) s)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact lt_of_le_of_lt (fle s hs) hb
