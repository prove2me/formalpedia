-- Prove2me | solution 1 for Eden.antitone_dist_le_of_matched_dist_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:09:19.170443+00:00
-- url     : https://prove2.me/submissions/c8b02d56-afa1-42c1-9053-cb2de26f59ca

import Definitions.Def_Eden_OrderedStationarySpectrum
import Mathlib.Data.Multiset.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Topology.MetricSpace.Lipschitz
import Definitions.Def_Eden_Sorting
import Theorems.Thm_Eden_antitone_le_of_matched_le
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialAmplitude_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {n : ℕ} {a b f g : Fin n → ℝ} {δ : ℝ}
    (ha : Antitone a) (hb : Antitone b)
    (haf : Finset.univ.val.map a = Finset.univ.val.map f)
    (hbg : Finset.univ.val.map b = Finset.univ.val.map g)
    (hfg : ∀ j, dist (f j) (g j) ≤ δ) (i : Fin n) : dist (a i) (b i) ≤ δ := by
  have hf : ∀ j, f j ≤ g j + δ := by
    intro j
    have := (abs_le.mp (show |f j - g j| ≤ δ by simpa [Real.dist_eq] using hfg j)).2
    linarith
  have hg : ∀ j, g j ≤ f j + δ := by
    intro j
    have := (abs_le.mp (show |f j - g j| ≤ δ by simpa [Real.dist_eq] using hfg j)).1
    linarith
  rw [Real.dist_eq, abs_le]
  constructor
  · have := antitone_le_of_matched_le hb ha hbg haf hg i
    linarith
  · have := antitone_le_of_matched_le ha hb haf hbg hf i
    linarith
end Eden
