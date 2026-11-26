-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.lemma4_exists_im_far_apart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:55.031959+00:00
-- url     : https://prove2.me/submissions/ffbf1284-29d0-4e8d-b201-26a949a7658b

import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_Expansion
import Definitions.Def_ExpChaotic_StripGeometry
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma4_exists_im_far_apart_two_pi

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution
    {V : Set ℂ} (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hinf : {n : ℕ | Disjoint (expIterate n '' V) centralStrip}.Infinite) :
    ∃ (n : ℕ) (w z : ℂ), w ∈ V ∧ z ∈ V ∧
      Real.pi ≤ |(expIterate n w).im - (expIterate n z).im| := by
  obtain ⟨n, w, z, hw, hz, hsep⟩ := lemma4_exists_im_far_apart_two_pi hVopen hVne hinf
  exact ⟨n, w, z, hw, hz, le_trans (by linarith [Real.pi_pos]) hsep⟩
end ExponentialJuliaSetMisiurewicz
