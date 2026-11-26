-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.lemma6_accumulation_up
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:12:16.183353+00:00
-- url     : https://prove2.me/submissions/4dcc46a6-54f1-4795-b0fb-9f3d3acc78b6

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_ExpChaotic_HalfPlane
import Definitions.Def_ExpChaotic_RealAxis
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_exists_double_subseq
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_exists_disc_points
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_add_I_ne_zero
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_equicontinuous_cayleyUp
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_norm_sub_lt_of_cayley_close
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero



set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution
    {V : Set ℂ} (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hnoreal : ∀ (n : ℕ), ∀ z ∈ V, (expIterate n z).im ≠ 0)
    {T : Set ℕ} (hTinf : T.Infinite)
    (hTup : ∀ n ∈ T, ∀ z ∈ V, 0 < (expIterate n z).im) :
    ∃ p y : ℂ, 0 ≤ p.im ∧
      ∀ η > 0, ∃ δ > 0, ball y δ ⊆ V ∧
        ∀ K : ℕ, ∃ n, K ≤ n ∧ ∀ z ∈ ball y δ, ‖expIterate n z - p‖ < η := by
  classical
  obtain ⟨w, hw⟩ := hVne
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hVopen w hw
  set ρ : ℝ := r / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hball2 : ball w (2 * ρ) ⊆ V := by
    have h2 : 2 * ρ = r := by rw [hρdef]; ring
    rw [h2]; exact hrsub
  have hballρ : ball w ρ ⊆ V := fun z hz => hball2 (by
    rw [Metric.mem_ball] at hz ⊢; linarith)
  have hballσ : ball w (ρ / 2) ⊆ V := fun z hz => hballρ (by
    rw [Metric.mem_ball] at hz ⊢; linarith)
  obtain ⟨N0, hN0⟩ := exists_disc_points hnoreal (by positivity : (0 : ℝ) < ρ / 2) hballσ
  -- enumerate the useful times
  set P : ℕ → Prop := fun n => n ∈ T ∧ N0 ≤ n with hPdef
  have hPinf : (Set.ofPred P).Infinite := by
    have hdiff : (T \ {n : ℕ | n < N0}).Infinite := hTinf.sdiff (Set.finite_Iio N0)
    refine Set.Infinite.mono ?_ hdiff
    intro n hn
    obtain ⟨hnT, hnlt⟩ := hn
    simp only [Set.mem_ofPred_eq] at hnlt
    exact ⟨hnT, by omega⟩
  set rr : ℕ → ℕ := fun k => Nat.nth P k with hrrdef
  have hrrP : ∀ k, P (rr k) := fun k => Nat.nth_mem_of_infinite hPinf k
  have hrrmono : StrictMono rr := fun a b hab => (Nat.nth_lt_nth hPinf).mpr hab
  have hchoice : ∀ k, ∃ y ∈ ball w (ρ / 2), ‖expIterate (rr k) y‖ ≤ Real.exp 4 :=
    fun k => hN0 (rr k) (hrrP k).2
  choose Y hYmem hYnorm using hchoice
  -- extract a common subsequence
  obtain ⟨ystar, hystar, p, hp, φ, hφ, hlimY, hlimB⟩ :=
    exists_double_subseq (isCompact_closedBall w (ρ / 2))
      (isCompact_closedBall (0 : ℂ) (Real.exp 4))
      (fun k => ball_subset_closedBall (hYmem k))
      (fun k => by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hYnorm k)
  have hpim : 0 ≤ p.im := by
    refine ge_of_tendsto ((Complex.continuous_im.tendsto p).comp hlimB) ?_
    refine Filter.Eventually.of_forall (fun k => le_of_lt ?_)
    exact hTup _ (hrrP (φ k)).1 _ (hballσ (hYmem (φ k)))
  have hpI : p + Complex.I ≠ 0 := by
    intro hc
    have him : (p + Complex.I).im = 0 := by rw [hc, Complex.zero_im]
    simp only [Complex.add_im, Complex.I_im] at him
    linarith
  have hystarball : ystar ∈ closedBall w (ρ / 2) := hystar
  refine ⟨p, ystar, hpim, ?_⟩
  intro η hη
  -- Invert the Cayley transform near the finite accumulation point.
  obtain ⟨ε, hε, hpush⟩ := norm_sub_lt_of_cayley_close hpI hη
  obtain ⟨δ0, hδ0, hequi⟩ :=
    equicontinuous_cayleyUp (c := w) (ρ := ρ) hρ (T := T)
      (fun n hn z hz => hTup n hn z (hball2 hz)) (half_pos hε)
  -- One fixed source disk works for arbitrarily late times along the selected subsequence.
  set δ : ℝ := min (δ0 / 2) (ρ / 2) with hδdef
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  have hδsub : ball ystar δ ⊆ ball w ρ := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    have h1 : dist ystar w ≤ ρ / 2 := by
      rwa [Metric.mem_closedBall] at hystarball
    have h2 : δ ≤ ρ / 2 := min_le_right _ _
    calc dist z w ≤ dist z ystar + dist ystar w := dist_triangle _ _ _
      _ < ρ := by linarith
  refine ⟨δ, hδpos, fun z hz => hballρ (hδsub hz), ?_⟩
  -- the two "eventually" facts
  have hMcont : ContinuousAt (fun u : ℂ => (u - Complex.I) / (u + Complex.I)) p := by
    refine ContinuousAt.div ?_ ?_ hpI
    · exact (continuous_id.sub continuous_const).continuousAt
    · exact (continuous_id.add continuous_const).continuousAt
  have hev1 : ∀ᶠ k in Filter.atTop, ‖Y (φ k) - ystar‖ < δ0 / 2 := by
    rw [Metric.tendsto_atTop] at hlimY
    obtain ⟨K1, hK1⟩ := hlimY (δ0 / 2) (by positivity)
    filter_upwards [Filter.eventually_ge_atTop K1] with k hk
    have := hK1 k hk
    rwa [dist_eq_norm] at this
  have hev2 : ∀ᶠ k in Filter.atTop,
      ‖(expIterate (rr (φ k)) (Y (φ k)) - Complex.I)
          / (expIterate (rr (φ k)) (Y (φ k)) + Complex.I)
        - (p - Complex.I) / (p + Complex.I)‖ < ε / 2 := by
    have hcomp := hMcont.tendsto.comp hlimB
    rw [Metric.tendsto_atTop] at hcomp
    obtain ⟨K2, hK2⟩ := hcomp (ε / 2) (by positivity)
    filter_upwards [Filter.eventually_ge_atTop K2] with k hk
    have := hK2 k hk
    rwa [dist_eq_norm] at this
  intro K
  obtain ⟨k, ⟨hk1, hk2⟩, hkK⟩ := ((hev1.and hev2).and (Filter.eventually_ge_atTop K)).exists
  refine ⟨rr (φ k), ?_, ?_⟩
  · calc K ≤ k := hkK
      _ ≤ φ k := hφ.le_apply
      _ ≤ rr (φ k) := hrrmono.le_apply
  · intro z hz
    have hzρ : z ∈ ball w ρ := hδsub hz
    have hYρ : Y (φ k) ∈ ball w ρ := by
      have := hYmem (φ k)
      rw [Metric.mem_ball] at this ⊢
      linarith
    have hclose : ‖z - Y (φ k)‖ < δ0 := by
      have hz1 : ‖z - ystar‖ < δ := by rwa [Metric.mem_ball, dist_eq_norm] at hz
      have hz2 : δ ≤ δ0 / 2 := min_le_left _ _
      calc ‖z - Y (φ k)‖ = ‖(z - ystar) + (ystar - Y (φ k))‖ := by ring_nf
        _ ≤ ‖z - ystar‖ + ‖ystar - Y (φ k)‖ := norm_add_le _ _
        _ < δ0 := by
            rw [← norm_neg (ystar - Y (φ k))] at *
            simp only [neg_sub] at *
            linarith
    have hstep1 := hequi ⟨rr (φ k), (hrrP (φ k)).1⟩ z hzρ (Y (φ k)) hYρ hclose
    have hzI : expIterate (rr (φ k)) z + Complex.I ≠ 0 :=
      add_I_ne_zero (hTup _ (hrrP (φ k)).1 _ (hballρ hzρ))
    refine hpush _ hzI ?_
    calc ‖(expIterate (rr (φ k)) z - Complex.I) / (expIterate (rr (φ k)) z + Complex.I)
            - (p - Complex.I) / (p + Complex.I)‖
        ≤ ‖(expIterate (rr (φ k)) z - Complex.I) / (expIterate (rr (φ k)) z + Complex.I)
              - (expIterate (rr (φ k)) (Y (φ k)) - Complex.I)
                / (expIterate (rr (φ k)) (Y (φ k)) + Complex.I)‖
          + ‖(expIterate (rr (φ k)) (Y (φ k)) - Complex.I)
                / (expIterate (rr (φ k)) (Y (φ k)) + Complex.I)
              - (p - Complex.I) / (p + Complex.I)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε := by linarith
end ExponentialJuliaSetMisiurewicz
