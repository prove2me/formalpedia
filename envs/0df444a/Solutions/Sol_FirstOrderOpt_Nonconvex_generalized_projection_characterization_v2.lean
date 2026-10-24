-- Prove2me | solution 1 for FirstOrderOpt.Nonconvex.generalized_projection_characterization_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T07:44:36.061997+00:00
-- url     : https://prove2.me/submissions/fd1a1685-0033-4949-815a-f67838ca0a27

import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

open scoped RealInnerProductSpace
open FirstOrderOpt.Prox Filter Topology

namespace GP88

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma three_point {X : Set E} (ν : DistanceGeneratingFunction X) (x xp u : E) :
    ν.V x u - ν.V xp u - ν.V x xp = ν.dω xp (u - xp) - ν.dω x (u - xp) := by
  simp only [DistanceGeneratingFunction.V]
  have : u - x = (u - xp) + (xp - x) := by abel
  rw [this, map_add]; ring

lemma slope_lim {X : Set E} (hXconv : Convex ℝ X) (ν : DistanceGeneratingFunction X)
    {xp u : E} (hxp : xp ∈ X) (hu : u ∈ X) :
    Tendsto (fun t : ℝ => t⁻¹ * (ν.ω (xp + t • (u - xp)) - ν.ω xp)) (𝓝[Set.Ioc 0 1] 0)
      (𝓝 (ν.dω xp (u - xp))) := by
  have hmap : Set.MapsTo (fun t : ℝ => xp + t • (u - xp)) (Set.Icc 0 1) X := by
    intro t ht
    have := hXconv.add_smul_sub_mem hxp hu ht
    simpa using this
  have hl : HasDerivWithinAt (fun t : ℝ => xp + t • (u - xp)) (u - xp) (Set.Icc 0 1) 0 := by
    have := ((hasDerivAt_id (0:ℝ)).smul_const (u - xp)).const_add xp
    simpa using this.hasDerivWithinAt
  have hd : HasDerivWithinAt (fun t : ℝ => ν.ω (xp + t • (u - xp))) (ν.dω xp (u - xp))
      (Set.Icc 0 1) 0 := by
    have h0 : HasFDerivWithinAt ν.ω (ν.dω xp) X (xp + (0:ℝ) • (u - xp)) := by
      simpa using ν.hasFDerivWithinAt xp hxp
    exact h0.comp_hasDerivWithinAt 0 hl hmap
  have := hasDerivWithinAt_iff_tendsto_slope.1 hd
  have hs : Set.Icc (0:ℝ) 1 \ {0} = Set.Ioc 0 1 := by
    ext t; simp only [Set.mem_diff, Set.mem_Icc, Set.mem_singleton_iff, Set.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨lt_of_le_of_ne h1 (Ne.symm h3), h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1.le, h2⟩, h1.ne'⟩
  rw [hs] at this
  refine this.congr (fun t => ?_)
  simp [slope_def_field, div_eq_inv_mul]

end GP88

theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (h : E → ℝ) (hhconv : ConvexOn ℝ X h)
    (ν : DistanceGeneratingFunction X)
    (x xPlus g : E) (γ : ℝ) (hγ : 0 < γ) (hx : x ∈ X) (hxPlus : xPlus ∈ X)
    (hmin : ∀ u ∈ X, ⟪g, xPlus⟫ + (1 / γ) * ν.V x xPlus + h xPlus ≤
      ⟪g, u⟫ + (1 / γ) * ν.V x u + h u) :
    ∀ u ∈ X, ⟪g, xPlus⟫ + h xPlus + (1 / γ) * ν.V x xPlus ≤
      ⟪g, u⟫ + h u + (1 / γ) * (ν.V x u - ν.V xPlus u) := by
  intro u hu
  set d := u - xPlus with hd
  -- key directional inequality
  have key : 0 ≤ ⟪g, d⟫ + (h u - h xPlus) + (1 / γ) * (ν.dω xPlus d - ν.dω x d) := by
    have hF : ∀ t ∈ Set.Ioc (0:ℝ) 1, 0 ≤ ⟪g, d⟫ + (h u - h xPlus) +
        (1 / γ) * (t⁻¹ * (ν.ω (xPlus + t • d) - ν.ω xPlus) - ν.dω x d) := by
      rintro t ⟨ht0, ht1⟩
      have hut : xPlus + t • d ∈ X := by
        have := hXconv.add_smul_sub_mem hxPlus hu ⟨ht0.le, ht1⟩; simpa [hd] using this
      have h1 := hmin _ hut
      have hconv : h (xPlus + t • d) ≤ (1 - t) * h xPlus + t * h u := by
        have := hhconv.2 hxPlus hu (by linarith : 0 ≤ 1 - t) ht0.le (by ring)
        have e : (1 - t) • xPlus + t • u = xPlus + t • d := by
          simp only [hd, smul_sub, sub_smul, one_smul]; abel
        simpa [e, smul_eq_mul] using this
      have hV : ν.V x (xPlus + t • d) - ν.V x xPlus =
          ν.ω (xPlus + t • d) - ν.ω xPlus - t * ν.dω x d := by
        simp only [DistanceGeneratingFunction.V]
        have : xPlus + t • d - x = (xPlus - x) + t • d := by abel
        rw [this, map_add, map_smul, smul_eq_mul]; ring
      have hinner : ⟪g, xPlus + t • d⟫ = ⟪g, xPlus⟫ + t * ⟪g, d⟫ := by
        rw [inner_add_right, inner_smul_right]
      have hmain : 0 ≤ t * ⟪g, d⟫ + t * (h u - h xPlus) +
          (1 / γ) * (ν.ω (xPlus + t • d) - ν.ω xPlus - t * ν.dω x d) := by
        rw [← hV]; rw [hinner] at h1
        have : (1 / γ) * ν.V x (xPlus + t • d) - (1 / γ) * ν.V x xPlus
            = (1 / γ) * (ν.V x (xPlus + t • d) - ν.V x xPlus) := by ring
        nlinarith
      have e : ⟪g, d⟫ + (h u - h xPlus) +
          (1 / γ) * (t⁻¹ * (ν.ω (xPlus + t • d) - ν.ω xPlus) - ν.dω x d) =
          t⁻¹ * (t * ⟪g, d⟫ + t * (h u - h xPlus) +
            (1 / γ) * (ν.ω (xPlus + t • d) - ν.ω xPlus - t * ν.dω x d)) := by
        field_simp
      rw [e]; exact mul_nonneg (inv_nonneg.2 ht0.le) hmain
    have hlim : Tendsto (fun t : ℝ => ⟪g, d⟫ + (h u - h xPlus) +
        (1 / γ) * (t⁻¹ * (ν.ω (xPlus + t • d) - ν.ω xPlus) - ν.dω x d)) (𝓝[Set.Ioc 0 1] 0)
        (𝓝 (⟪g, d⟫ + (h u - h xPlus) + (1 / γ) * (ν.dω xPlus d - ν.dω x d))) := by
      have := GP88.slope_lim hXconv ν hxPlus hu
      exact tendsto_const_nhds.add ((this.sub tendsto_const_nhds).const_mul _)
    have : (𝓝[Set.Ioc (0:ℝ) 1] 0).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioc (by norm_num)]
      exact ⟨le_rfl, zero_le_one⟩
    exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall hF)
  have htp := GP88.three_point ν x xPlus u
  rw [← hd] at htp
  have hγ' : 0 < 1 / γ := by positivity
  have e : (1 / γ) * (ν.V x u - ν.V xPlus u) =
      (1 / γ) * ν.V x xPlus + (1 / γ) * (ν.dω xPlus d - ν.dω x d) := by
    rw [← htp]; ring
  have hgi : ⟪g, d⟫ = ⟪g, u⟫ - ⟪g, xPlus⟫ := by rw [hd, inner_sub_right]
  rw [e]; linarith
