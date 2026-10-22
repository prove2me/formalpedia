-- Prove2me | solution 1 for AvramDividend.Classical.drawdown_after_firstUpcrossing_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T23:24:09.335291+00:00
-- url     : https://prove2.me/submissions/454994bf-5649-4bbd-b552-b09d82f9ac9c

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_prethreshold_le
import Theorems.Thm_AvramDividend_Classical_one_sided_limits_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_runningSup_excess_after_peak
import Theorems.Thm_AvramDividend_Classical_runningSup_interval_shift
import Theorems.Thm_AvramDividend_Classical_runningSup_split_at

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The drawdown of the process after its first up-crossing of a level is the
shifted drawdown plus the drawdown attained at the crossing.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))
    (hb : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u)) :
    ∀ (t : ℝ≥0),
      runningSup X (u + t) ω - X.X (u + t) ω =
        (runningSup X u ω - X.X u ω) +
          (sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
            X.X (u + t) ω) := by
  intro t
  obtain ⟨hlevel, hpeak⟩ :=
    firstUpcrossing_attains_peak X (a - x) (sub_nonneg.mpr hxa) ω u hu
  -- `runningSup` is the raw supremum of the path over the window.
  have hsup : ∀ (s : ℝ≥0),
      runningSup X s ω = ⨆ v : Set.Icc (0 : ℝ≥0) s, X.X v.1 ω :=
    fun s => (runningSup_eq_rawSup_nonneg X s ω).1
  -- The raw supremum over a window is the `sSup` of the image of the window.
  have htoSup : ∀ (s : ℝ≥0),
      (⨆ v : Set.Icc (0 : ℝ≥0) s, X.X v.1 ω) =
        sSup ((fun v : ℝ≥0 => X.X v ω) '' Set.Icc (0 : ℝ≥0) s) := by
    intro s
    rw [sSup_image']
  -- The path is bounded above on every compact window.
  have hpathBdd : ∀ (T : ℝ≥0),
      BddAbove ((fun v : ℝ≥0 => X.X v ω) '' Set.Icc (0 : ℝ≥0) T) := by
    intro T
    obtain ⟨M, hM⟩ :
        BddAbove (Set.range (fun s : Set.Icc (0 : ℝ≥0) T => X.X s.1 ω)) :=
      one_sided_limits_bddAbove_Icc (fun v => X.X v ω)
        (fun v => X.rightCont ω v)
        (fun v => by
          by_cases hv : v = 0
          · subst v
            refine ⟨0, ?_⟩
            have hb : (𝓝[<] (0 : ℝ≥0)) = ⊥ :=
              nhdsLT_eq_bot_iff.mpr (.inl (fun z => (zero_le : (0 : ℝ≥0) ≤ z)))
            rw [hb]
            exact tendsto_bot
          · have hvpos : 0 < v :=
              lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ v) (Ne.symm hv)
            exact X.leftLim ω v hvpos)
        T
    refine ⟨M, ?_⟩
    rintro y ⟨v, hv, rfl⟩
    exact hM ⟨⟨v, hv⟩, rfl⟩
  -- The path is bounded above on the shifted window as well.
  have hshBdd : BddAbove ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) := by
    have hb : BddAbove ((fun v : ℝ≥0 => X.X v ω) '' Set.Icc (0 : ℝ≥0) (u + t)) :=
      hpathBdd (u + t)
    refine ⟨sSup ((fun v : ℝ≥0 => X.X v ω) '' Set.Icc (0 : ℝ≥0) (u + t)), ?_⟩
    rintro y ⟨r, hr, rfl⟩
    exact le_csSup hb ⟨u + r, Set.mem_Icc.mpr
      ⟨(zero_le : (0 : ℝ≥0) ≤ u + r), add_le_add_right hr.2 u⟩, rfl⟩
  -- The peak dominates the part before `u`, so the whole-window supremum is
  -- the supremum of the shifted window.
  have hsplit :
      sSup ((fun v : ℝ≥0 => X.X v ω) '' Set.Icc (0 : ℝ≥0) (u + t)) =
        sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) := by
    have hsplit' :
        sSup ((fun v : ℝ≥0 => X.X v ω) '' Set.Icc (0 : ℝ≥0) (u + t)) =
          max (sSup ((fun v : ℝ≥0 => X.X v ω) '' Set.Icc (0 : ℝ≥0) u))
            (sSup ((fun v : ℝ≥0 => X.X v ω) '' Set.Icc u (u + t))) :=
      runningSup_split_at (fun v : ℝ≥0 => X.X v ω) u t (hpathBdd (u + t))
    have htail :
        sSup ((fun v : ℝ≥0 => X.X v ω) '' Set.Icc u (u + t)) =
          sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) :=
      runningSup_interval_shift (fun v : ℝ≥0 => X.X v ω) u t
    -- The peak is at most the shifted supremum: it is the value at `u + 0`.
    have hmem0 : X.X (u + 0) ω ∈ ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) :=
      Set.mem_image_of_mem (fun r : ℝ≥0 => X.X (u + r) ω) (Set.mem_Icc.mpr
        ⟨(zero_le : (0 : ℝ≥0) ≤ 0), (zero_le : (0 : ℝ≥0) ≤ t)⟩)
    have hle0 : X.X (u + 0) ω ≤ sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) := by
      refine le_csSup ?_ hmem0
      refine ⟨sSup ((fun v : ℝ≥0 => X.X v ω) '' Set.Icc (0 : ℝ≥0) (u + t)), ?_⟩
      rintro y ⟨r, hr, rfl⟩
      exact le_csSup (hpathBdd (u + t)) (Set.mem_image_of_mem
        (fun v : ℝ≥0 => X.X v ω) (Set.mem_Icc.mpr
          ⟨(zero_le : (0 : ℝ≥0) ≤ u + r), add_le_add_right hr.2 u⟩))
    have hle : X.X u ω ≤ sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) := by
      simpa only [AddZeroClass.add_zero] using hle0
    rw [hsplit', htail, hpeak, max_eq_right hle]
  -- Now assemble the stated identity.
  rw [hsup (u + t), htoSup (u + t)]
  -- The supremum over `[0, u]` is the peak, so it is the value at `u`.
  have hpre :
      sSup ((fun v : ℝ≥0 => X.X v ω) '' Set.Icc (0 : ℝ≥0) u) = X.X u ω :=
    hpeak
  -- After `htoSup u` the running supremum over `[0, u]` is the `sSup` of the
  -- image, which the peak identifies with the value at `u`.
  rw [hsup u, htoSup u, hpre]
  rw [hsplit]
  linarith
