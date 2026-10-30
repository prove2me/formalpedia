-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_cstar_nonzero_of_vcstar_C2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T23:58:05.720441+00:00
-- url     : https://prove2.me/submissions/b3b6ffa4-b3f4-4b73-bc8a-aeb1e79827db

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_contDiffOn

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

/-- C2 smooth fit rules out a zero scale derivative at a positive finite barrier. -/
theorem solution
    (W : ℝ → ℝ)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hsmooth : ContDiffOn ℝ 2 (vcstar W) (Ioi (0 : ℝ))) :
    deriv W (cstar W).toReal ≠ 0 := by
  let a : ℝ := (cstar W).toReal
  have ha : 0 < a := (ENNReal.toReal_pos_iff).mpr ⟨hcpos, hc⟩
  by_contra hne
  have hd0 : deriv W a = 0 := by simpa [a] using hne
  have hzero : ∀ y : ℝ, 0 ≤ y → y ≤ a → vcstar W y = 0 := by
    intro y hy hya
    have hyneg : ¬ y < 0 := not_lt.mpr hy
    change barrierValue W a y = 0
    simp [barrierValue, hyneg, hya, scaleDeriv, ne_of_gt ha, hd0, divE]
  have hfa0 : vcstar W a = 0 := hzero a (le_of_lt ha) le_rfl
  have hposAt : ∀ᶠ y : ℝ in 𝓝 a, 0 < y := by
    filter_upwards [isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr ha)] with y hy
    exact hy
  have hposEv : ∀ᶠ y : ℝ in 𝓝[Iic a] a, 0 < y :=
    hposAt.filter_mono nhdsWithin_le_nhds
  have hleEv : ∀ᶠ y : ℝ in 𝓝[Iic a] a, y ≤ a := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hy
  have hevent : (vcstar W) =ᶠ[𝓝[Iic a] a] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [hposEv, hleEv] with y hy hya
    exact hzero y (le_of_lt hy) hya
  have hzeroWithin : HasDerivWithinAt (vcstar W) 0 (Iic a) a := by
    have hconst : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Iic a) a :=
      (hasDerivAt_const (x := a) (c := (0 : ℝ))).hasDerivWithinAt
    exact hconst.congr_of_eventuallyEq hevent hfa0
  have hdiff : DifferentiableAt ℝ (vcstar W) a :=
    (hsmooth.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr ha))
  have hfit : deriv (vcstar W) a = 1 := by
    simpa [a] using vcstar_deriv_one_of_contDiffOn W hc hcpos hsmooth
  have hfitAt : HasDerivAt (vcstar W) 1 a := hfit ▸ hdiff.hasDerivAt
  have huni : UniqueDiffWithinAt ℝ (Iic a) a := uniqueDiffWithinAt_Iic a
  have hzeroSlope : derivWithin (vcstar W) (Iic a) a = 0 :=
    hzeroWithin.derivWithin huni
  have honeSlope : derivWithin (vcstar W) (Iic a) a = 1 :=
    hfitAt.hasDerivWithinAt.derivWithin huni
  have hfalse : (0 : ℝ) = 1 := hzeroSlope.symm.trans honeSlope
  norm_num at hfalse
