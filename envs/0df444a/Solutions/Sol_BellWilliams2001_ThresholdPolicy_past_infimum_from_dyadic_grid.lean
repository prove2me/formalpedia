-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.past_infimum_from_dyadic_grid
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:40:52.490848+00:00
-- url     : https://prove2.me/submissions/36a4697d-0f75-483d-a7c2-5fe0faf2b754

import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_ge_nnreal

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

theorem solution (f : ℝ → ℝ) (t : ℝ≥0)
    (hRight : ∀ s : ℝ, 0 ≤ s → ContinuousWithinAt f (Ici s) s)
    (hBound : BddBelow (range (fun s : Icc (0 : ℝ) (t : ℝ) => f s))) :
    ENNReal.ofReal (f t - ⨅ s : Icc (0 : ℝ) (t : ℝ), f s) =
      ⨆ p : ℕ × ℕ, ENNReal.ofReal (f t - f (min t ((p.2 : ℝ≥0) / (2 : ℝ≥0)^p.1))) := by
  letI : Nonempty (Icc (0:ℝ) (t:ℝ)) := ⟨⟨0,le_rfl,t.2⟩⟩
  let g (s : ℝ) := ENNReal.ofReal (f t - f s)
  let infVal := ⨅ s : Icc (0:ℝ) (t:ℝ), f s
  let grid (p : ℕ × ℕ) : ℝ≥0 := min t ((p.2 : ℝ≥0) / (2 : ℝ≥0)^p.1)
  let A := ⨆ p, g (grid p)
  have hUpper : A ≤ ENNReal.ofReal (f t - infVal) := by
    refine iSup_le fun p => ENNReal.ofReal_le_ofReal (sub_le_sub_left ?_ _)
    exact ciInf_le hBound (⟨grid p, (grid p).2, by exact_mod_cast min_le_left t _⟩ :
      Icc (0:ℝ) (t:ℝ))
  have hDense (s : Icc (0 : ℝ) (t : ℝ)) : g s ≤ A := by
    let u : ℝ≥0 := ⟨s,s.2.1⟩
    have hut : u ≤ t := s.2.2
    let idx (n : ℕ) := (n, Nat.ceil ((u:ℝ) * (2:ℝ)^n))
    have hLimN : Tendsto (fun n => grid (idx n)) atTop (𝓝 u) := by
      have h := (tendsto_const_nhds (x := t)).min (AvramDividend.Classical.dyadic_ceiling_nnreal_tendsto u)
      simpa [grid,idx,min_eq_right hut] using h
    have hLim : Tendsto (fun n => (grid (idx n) : ℝ)) atTop (𝓝 (s:ℝ)) :=
      (NNReal.continuous_coe.tendsto u).comp hLimN
    have hFrom : ∀ᶠ n in atTop, (grid (idx n) : ℝ) ∈ Ici (s:ℝ) := by
      refine Eventually.of_forall fun n => ?_
      have h : u ≤ grid (idx n) := le_min hut
        (AvramDividend.Classical.dyadic_ceiling_time_ge_nnreal u n)
      exact mem_Ici.mpr (by exact_mod_cast h)
    have hF := (hRight s s.2.1).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hLim,hFrom⟩)
    have hG := (ENNReal.continuous_ofReal.tendsto (f t - f s)).comp (tendsto_const_nhds.sub hF)
    exact le_of_tendsto hG (Eventually.of_forall fun n => le_iSup (fun p => g (grid p)) (idx n))
  refine le_antisymm ?_ hUpper
  change ENNReal.ofReal (f t - infVal) ≤ A
  by_cases hTop : A = ⊤
  · simp [hTop]
  have hOrd : ∀ s : Icc (0:ℝ) (t:ℝ), f t - A.toReal ≤ f s := by
    intro s
    have hh := ENNReal.toReal_mono hTop (hDense s)
    change (ENNReal.ofReal (f t - f s)).toReal ≤ A.toReal at hh
    rw [ENNReal.toReal_ofReal'] at hh
    linarith [le_max_right 0 (f t - f s), le_max_left (f t-f s) 0]
  have hh := le_ciInf hOrd
  have hc : f t - infVal ≤ A.toReal := by
    change f t - A.toReal ≤ infVal at hh
    linarith
  exact (ENNReal.ofReal_le_ofReal hc).trans_eq (ENNReal.ofReal_toReal hTop)
