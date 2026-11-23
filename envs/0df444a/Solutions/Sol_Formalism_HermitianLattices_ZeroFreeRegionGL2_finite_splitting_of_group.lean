-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.finite_splitting_of_group
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:39.632368+00:00
-- url     : https://prove2.me/submissions/471c89bc-207e-4fc9-ad00-cdbbc208d087

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightedVonMangoldtSumIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : GFiniteSplit := by
  intro q _ χ x z hx hxz
  unfold Gchi Sz tailL cN
  have hsub : Icc 1 ⌊x⌋₊ ⊆ Icc 1 ⌊z⌋₊ := Icc_subset_Icc le_rfl (Nat.floor_le_floor hxz)
  have e1 : (∑ n ∈ Icc 1 ⌊x⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((x / n - 1 : ℝ) : ℂ)) =
      ∑ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((x / n - min 1 (x / n) : ℝ) : ℂ) := by
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [mem_Icc] at hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
      have hle : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).1 hn.2
      rw [min_eq_left ((one_le_div hn0).2 hle)]
    · intro n hn hn'
      rw [mem_Icc] at hn hn'
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
      have : x < n := by
        by_contra hc
        exact hn' ⟨hn.1, Nat.le_floor (not_lt.1 hc)⟩
      rw [min_eq_right ((div_le_one hn0).2 this.le)]; simp
  rw [e1]
  have : ∀ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((x / n - min 1 (x / n) : ℝ) : ℂ) =
      (x : ℂ) * (((Λ n : ℝ) : ℂ) * χ (n : ZMod q) / (n : ℂ)) - ((Λ n * min 1 (x / n) : ℝ) : ℂ) * χ (n : ZMod q) := by
    intro n _; push_cast; ring
  rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring
end Formalism.HermitianLattices.ZeroFreeRegionGL2
