-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.lemma4_eventually_meets_centralStrip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:31.611712+00:00
-- url     : https://prove2.me/submissions/492b1b16-9d53-4b36-8c76-bd098aa1a414

import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_Expansion
import Definitions.Def_ExpChaotic_StripGeometry
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_im_eq_zero_of_le
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_im_succ_eq_zero_of_int
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma4_exists_im_far_apart
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma4_exists_im_int_mul_pi

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution
    {V : Set ℂ} (hVopen : IsOpen V) (hVconn : IsConnected V) (hVne : V.Nonempty) :
    ∃ N : ℕ, ∀ n ≥ N, (expIterate n '' V ∩ centralStrip).Nonempty := by
  by_contra hcon
  push Not at hcon
  have hinf : {n : ℕ | Disjoint (expIterate n '' V) centralStrip}.Infinite := by
    apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hN⟩
    obtain ⟨n, hn, hempty⟩ := hcon (N + 1)
    have hmem : n ∈ {n : ℕ | Disjoint (expIterate n '' V) centralStrip} := by
      exact Set.disjoint_iff_inter_eq_empty.mpr hempty
    have := hN hmem
    omega
  obtain ⟨n, y, k, hy, hk⟩ :=
    lemma4_exists_im_int_mul_pi hVconn (lemma4_exists_im_far_apart hVopen hVne hinf)
  obtain ⟨M, hM, hempty⟩ := hcon (n + 1)
  have h0 : (expIterate (n + 1) y).im = 0 := expIterate_im_succ_eq_zero_of_int hk
  have hM0 : (expIterate M y).im = 0 := expIterate_im_eq_zero_of_le h0 M hM
  have hmem : expIterate M y ∈ expIterate M '' V ∩ centralStrip := by
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    show |(expIterate M y).im| ≤ Real.pi / 3
    rw [hM0, abs_zero]
    positivity
  rw [hempty] at hmem
  exact hmem
end ExponentialJuliaSetMisiurewicz
