-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_finite_seam_leftcontinuous_residual_constant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:52:45.910276+00:00
-- url     : https://prove2.me/submissions/b9bc3b82-2171-4079-b060-2a4a2602c8bd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_leftLim_affine_of_eventuallyEq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal Topology
noncomputable section

theorem solution
    (g : ℝ≥0 → ℝ) (S : Finset ℝ≥0) (T : ℝ≥0)
    (hTime : ∀ u ∈ S, 0 < u ∧ u ≤ T)
    (hFlat : ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      (∀ u ∈ S, ¬ (s < u ∧ u ≤ t)) → g t = g s)
    (hLeft : ∀ u ∈ S, Function.leftLim g u = g u) :
    g T = g 0 := by
  classical
  let F : ℝ≥0 → Finset ℝ≥0 := fun t => S.filter (fun u => u ≤ t)
  have hRec : ∀ n : ℕ, ∀ t : ℝ≥0, t ≤ T →
      (F t).card = n → g t = g 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro t ht hn
      by_cases hne : (F t).Nonempty
      · let r : ℝ≥0 := (F t).max' hne
        let hrFt : r ∈ F t := Finset.max'_mem (F t) hne
        let hr : r ∈ S ∧ r ≤ t := Finset.mem_filter.mp hrFt
        let hrPos : 0 < r := (hTime r hr.1).1
        have hPrev : ∀ s : ℝ≥0, s < r → g s = g 0 := by
          intro s hs
          let hsT : s ≤ T :=
            le_trans (le_of_lt hs) (le_trans hr.2 ht)
          let hsub : F s ⊆ F t := by
            intro u hu
            let hv : u ∈ S ∧ u ≤ s := Finset.mem_filter.mp hu
            exact Finset.mem_filter.mpr
              ⟨hv.1, le_trans hv.2 (le_trans (le_of_lt hs) hr.2)⟩
          let hrnot : r ∉ F s := by
            intro hre
            let hre' : r ≤ s := (Finset.mem_filter.mp hre).2
            exact (not_le_of_gt hs) hre'
          let hproper : F s ⊂ F t := by
            apply Finset.ssubset_iff_subset_ne.mpr
            refine ⟨hsub, ?_⟩
            intro heq
            apply hrnot
            rw [heq]
            exact hrFt
          let hcard : (F s).card < n := by
            let hlt := Finset.card_lt_card hproper
            rwa [hn] at hlt
          exact ih (F s).card hcard s hsT rfl
        haveI : (𝓝[<] r).NeBot :=
          nhdsLT_neBot_of_exists_lt ⟨0, hrPos⟩
        have hEvent : g =ᶠ[𝓝[<] r]
            (fun s : ℝ≥0 => (g 0 : ℝ) + 0 * (s : ℝ)) := by
          filter_upwards [self_mem_nhdsWithin] with s hs
          simp [hPrev s hs]
        let hLeftConst : Function.leftLim g r = g 0 := by
          simpa using
            (avram_bv_leftLim_affine_of_eventuallyEq
              g r (g 0) 0 hEvent)
        let hrVal : g r = g 0 :=
          (hLeft r hr.1).symm.trans hLeftConst
        let hNo : ∀ u ∈ S, ¬ (r < u ∧ u ≤ t) := by
          intro u hu hx
          let huf : u ∈ F t :=
            Finset.mem_filter.mpr ⟨hu, hx.2⟩
          let hmax : u ≤ r := Finset.le_max' (F t) u huf
          exact (not_lt_of_ge hmax) hx.1
        exact (hFlat r t hr.2 ht hNo).trans hrVal
      · have hNo : ∀ u ∈ S, ¬ (0 < u ∧ u ≤ t) := by
          intro u hu hx
          apply hne
          exact ⟨u, Finset.mem_filter.mpr ⟨hu, hx.2⟩⟩
        exact hFlat 0 t zero_le ht hNo
  exact hRec (F T).card T le_rfl rfl
