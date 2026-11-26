-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.dense_iterated_preimages_real_axis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:17:38.019503+00:00
-- url     : https://prove2.me/submissions/43b8763a-d8a9-4a71-bfce-b0450a9b062c

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_RealAxis
import Definitions.Def_ExpChaotic_Covering
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_dense_iterated_preimages_nonzero
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero



set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution :
    Dense {z : ℂ | ∃ n : ℕ, OnRealAxis (expIterate n z)} := by
  apply (dense_iterated_preimages_nonzero (w := 1) one_ne_zero).mono
  rintro z ⟨n, hn⟩
  exact ⟨n, by simp [hn, OnRealAxis]⟩
end ExponentialJuliaSetMisiurewicz
