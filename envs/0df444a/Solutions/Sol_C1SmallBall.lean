-- Prove2me | solution 1 for C1SmallBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:10:47.581501+00:00
-- url     : https://prove2.me/submissions/1402d94b-f20a-4721-ad36-8bf35596d37d

import Definitions.Def_Tablet_MorreySubadditive
import Definitions.Def_Tablet_MorreyResolutionAdditive
import Definitions.Def_Tablet_GeodesicMorreyLeTwo
import Definitions.Def_Tablet_IsPiecewiseGeodesicWith
import Definitions.Def_Tablet_C1SmallBall
import Theorems.Thm_GeodesicMorreyLeTwo
import Theorems.Thm_MorreyResolutionAdditive
import Theorems.Thm_MorreySubadditive


set_option autoImplicit false
open MeasureTheory Set ENNReal
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (γ : Curve E) (k : ℕ) (hpw : IsPiecewiseGeodesicWith γ k) :
    morreyNorm (curveMeasure γ) ≤ 2 * (k : ℝ≥0∞) := by
-- BODY
  obtain ⟨s, hmono, h0, hk, hgeo⟩ := hpw
  have hadd := MorreyResolutionAdditive γ k s hmono h0 hk
  rw [hadd]
  have hsub := MorreySubadditive (Finset.range k)
    (fun i => Measure.map γ.toFun (volume.restrict (Set.Icc (s i) (s (i + 1)))))
  refine hsub.trans ?_
  have hterm : ∀ i ∈ Finset.range k,
      morreyNorm (Measure.map γ.toFun (volume.restrict (Set.Icc (s i) (s (i + 1))))) ≤ 2 := by
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have hi1k : i + 1 ≤ k := hik
    have hab : s i ≤ s (i + 1) :=
      hmono ⟨Nat.zero_le i, hik.le⟩ ⟨Nat.zero_le (i + 1), hi1k⟩ (Nat.le_succ i)
    have hbnd : s (i + 1) ≤ γ.len :=
      hk ▸ hmono ⟨Nat.zero_le (i + 1), hi1k⟩ ⟨Nat.zero_le k, le_refl k⟩ hi1k
    exact GeodesicMorreyLeTwo γ (s i) (s (i + 1)) hab hbnd (hgeo i hik)
  calc ∑ i ∈ Finset.range k,
        morreyNorm (Measure.map γ.toFun (volume.restrict (Set.Icc (s i) (s (i + 1)))))
      ≤ ∑ _i ∈ Finset.range k, (2 : ℝ≥0∞) := Finset.sum_le_sum hterm
    _ = 2 * (k : ℝ≥0∞) := by rw [Finset.sum_const, Finset.card_range]; ring
