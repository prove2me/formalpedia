-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.lemma6_every_domain_eventually_meets_real_axis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:14:04.699614+00:00
-- url     : https://prove2.me/submissions/5fdda88e-6f68-4ff3-bf4c-73f6537bb4f8

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_ExpChaotic_HalfPlane
import Definitions.Def_ExpChaotic_RealAxis
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_isOpen_conj_image
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_nonempty_conj_image
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_noreal_conj_image
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_conj_image_up_of_down
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma6_contradiction_up
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_image_in_half_plane


set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution
    {V : Set ℂ} (hVopen : IsOpen V) (hVconn : IsConnected V) (hVne : V.Nonempty) :
    EventuallyMeetsRealAxis V := by
  by_contra hcon
  have hnoreal : ∀ (n : ℕ), ∀ z ∈ V, (expIterate n z).im ≠ 0 := by
    intro n z hz hval
    exact hcon ⟨n, z, hz, hval⟩
  by_cases hup : {n : ℕ | ∀ z ∈ V, 0 < (expIterate n z).im}.Infinite
  · exact lemma6_contradiction_up hVopen hVne hnoreal hup (fun n hn z hz => hn z hz)
  · rw [Set.not_infinite] at hup
    have hdowninf : {n : ℕ | ∀ z ∈ V, (expIterate n z).im < 0}.Infinite := by
      refine Set.Infinite.mono ?_ (Set.infinite_univ.sdiff hup)
      intro n hn
      rcases image_in_half_plane hVconn hnoreal n with h | h
      · exact absurd h hn.2
      · exact h
    exact lemma6_contradiction_up (isOpen_conj_image hVopen) (nonempty_conj_image hVne)
      (noreal_conj_image hnoreal) hdowninf
      (fun n hn z hz => conj_image_up_of_down (fun u hu => hn u hu) z hz)
end ExponentialJuliaSetMisiurewicz
