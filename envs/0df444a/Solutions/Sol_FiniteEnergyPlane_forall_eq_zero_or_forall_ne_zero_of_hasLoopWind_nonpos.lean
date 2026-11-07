-- Prove2me | solution 1 for FiniteEnergyPlane.forall_eq_zero_or_forall_ne_zero_of_hasLoopWind_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-06T19:29:53.559743+00:00
-- url     : https://prove2.me/submissions/363b4cae-6cec-4115-bb87-870c88aeb95b

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_unique
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_ccwLoop_eq_sum
import Theorems.Thm_FiniteEnergyPlane_exists_hasLoopWind_of_norm_dbar_le
import Theorems.Thm_FiniteEnergyPlane_eventually_eq_zero_of_norm_dbar_le
import Theorems.Thm_JHolomorphic_eq_zero_of_norm_dbar_le_of_eqOn_zero



namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff Real

/-- Let `ζ : ℂ → ℂ` be smooth with `|∂ₛζ + i ∂ₜζ| ≤ M |ζ|` locally, without zeros on `‖z‖ ≥ R`, and
with winding number `k ≤ 0` along the circle of radius `R`. Then `ζ` is identically zero or has no
zeros. -/
theorem forall_eq_zero_or_forall_ne_zero_of_hasLoopWind_nonpos_aux (ζ : ℂ → ℂ)
    (hζ : ContDiff ℝ ∞ ζ)
    (hM : ∀ z₀ : ℂ, ∃ ρ > (0 : ℝ), ∃ M : ℝ, ∀ z ∈ ball z₀ ρ,
      ‖fderiv ℝ ζ z 1 + Complex.I * fderiv ℝ ζ z Complex.I‖ ≤ M * ‖ζ z‖)
    (R : ℝ) (hR : 0 < R) (hnon : ∀ z, R ≤ ‖z‖ → ζ z ≠ 0) (k : ℤ) (hk0 : k ≤ 0)
    (hk : HasLoopWind (fun t => ζ (ccwLoop R t)) k) :
    (∀ z, ζ z = 0) ∨ ∀ z, ζ z ≠ 0 := by
  classical
  by_cases hall : ∀ z, ζ z = 0
  · exact Or.inl hall
  refine Or.inr ?_
  by_contra hex
  push_neg at hex
  obtain ⟨z₁, hz₁⟩ := hex
  have hopen : ∀ U : Set ℂ, IsOpen U → U.Nonempty → ¬ ∀ z ∈ U, ζ z = 0 := by
    intro U hU hne h0
    refine hall (JHolomorphic.eq_zero_of_norm_dbar_le_of_eqOn_zero
      (fun _ => ContinuousLinearMap.mul ℝ ℂ Complex.I) contDiff_const ?_ ζ hζ ?_ U hU hne h0)
    · intro _
      ext v
      simp [← mul_assoc]
    · intro z₀
      obtain ⟨ρ, hρ, M, hb⟩ := hM z₀
      exact ⟨ρ, hρ, M, fun z hz => by simpa using hb z hz⟩
  have hloop : HasLoopWind (fun t => ζ ((0 : ℂ) + ccwLoop R t)) k := by
    simpa using hk
  have hsub : {z | ζ z = 0} ⊆ closedBall (0 : ℂ) R := by
    intro z hz
    rw [mem_closedBall, dist_zero_right]
    by_contra hlt
    exact hnon z (le_of_lt (not_le.1 hlt)) hz
  have hfin : {z | ζ z = 0}.Finite := by
    by_contra hinf
    obtain ⟨x, -, hx⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf
      (isCompact_closedBall _ _) hsub
    obtain ⟨ρ, hρ, M, hb⟩ := hM x
    have hfreq : ∃ᶠ z in 𝓝[≠] x, ζ z = 0 := accPt_iff_frequently_nhdsNE.1 hx
    have hev := eventually_eq_zero_of_norm_dbar_le ζ (ball x ρ) isOpen_ball hζ.contDiffOn M hb x
      (mem_ball_self hρ) hfreq
    obtain ⟨U, hU0, hUo, hxU⟩ := _root_.eventually_nhds_iff.1 hev
    exact hopen U hUo ⟨x, hxU⟩ hU0
  set Q := hfin.toFinset with hQ
  have hQm : ∀ z, z ∈ Q ↔ ζ z = 0 := fun z => by simp [hQ]
  have hidx : ∀ p ∈ Q, ∃ m : ℕ, 1 ≤ m ∧ ∃ r > (0 : ℝ), ∀ ρ ∈ Set.Ioo 0 r,
      HasLoopWind (fun t => ζ (p + ccwLoop ρ t)) m := by
    intro p hp
    obtain ⟨ρ, hρ, M, hb⟩ := hM p
    have hcl : IsClosed ({z | ζ z = 0} \ {p}) := (hfin.subset Set.diff_subset).isClosed
    refine exists_hasLoopWind_of_norm_dbar_le ζ (ball p ρ ∩ ({z | ζ z = 0} \ {p})ᶜ)
      (isOpen_ball.inter hcl.isOpen_compl) hζ.contDiffOn M (fun z hz => hb z hz.1) p
      ⟨mem_ball_self hρ, fun h => h.2 rfl⟩ ((hQm p).1 hp) ?_
    intro z hz h0
    by_contra hzp
    exact hz.2 ⟨h0, hzp⟩
  choose! m hm1 hm2 using hidx
  have hsum := hasLoopWind_ccwLoop_eq_sum ζ Q 0 R hR
    (fun p hp => by
      rw [mem_ball, dist_zero_right]
      by_contra hlt
      exact hnon p (not_lt.1 hlt) ((hQm p).1 hp))
    hζ.continuous.continuousOn
    (fun z hz h0 => hz.2 (by simpa using (hQm z).2 h0))
    (fun p => (m p : ℤ)) (fun p hp => hm2 p hp)
  have hk' := hasLoopWind_unique hloop hsum
  have h1 : (m z₁ : ℤ) ≤ ∑ p ∈ Q, (m p : ℤ) :=
    Finset.single_le_sum (f := fun p => (m p : ℤ)) (fun p _ => Int.natCast_nonneg _)
      ((hQm z₁).2 hz₁)
  have h2 : (1 : ℤ) ≤ m z₁ := by exact_mod_cast hm1 z₁ ((hQm z₁).2 hz₁)
  omega

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric
open scoped ContDiff

theorem solution (ζ : ℂ → ℂ)
    (hζ : ContDiff ℝ ∞ ζ)
    (hM : ∀ z₀ : ℂ, ∃ ρ > (0 : ℝ), ∃ M : ℝ, ∀ z ∈ ball z₀ ρ,
      ‖fderiv ℝ ζ z 1 + Complex.I * fderiv ℝ ζ z Complex.I‖ ≤ M * ‖ζ z‖)
    (R : ℝ) (hR : 0 < R) (hnon : ∀ z, R ≤ ‖z‖ → ζ z ≠ 0) (k : ℤ) (hk0 : k ≤ 0)
    (hk : HasLoopWind (fun t => ζ (ccwLoop R t)) k) :
    (∀ z, ζ z = 0) ∨ ∀ z, ζ z ≠ 0 :=
  forall_eq_zero_or_forall_ne_zero_of_hasLoopWind_nonpos_aux ζ hζ hM R hR hnon k hk0 hk
