-- Prove2me | solution 1 for EthierKurtz.oblique_semigroup_conservative
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:31:02.34397+00:00
-- url     : https://prove2.me/submissions/d347f99d-56d7-4c50-b0d9-cd900b89fb03

import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

theorem aux_osc_telescope {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ → E →L[ℝ] E) (hT : IsStronglyContinuousContractionSemigroup T)
    (x : E) (h : ℝ) (hh : 0 ≤ h) :
    ∀ k : ℕ, ‖T (k * h) x - x‖ ≤ k * ‖T h x - x‖ := by
  intro k
  induction k with
  | zero => simp [hT.1]
  | succ k ih =>
    have e : ((k + 1 : ℕ) : ℝ) * h = k * h + h := by push_cast; ring
    rw [e, hT.2.1 _ _ (by positivity) hh, ContinuousLinearMap.comp_apply]
    have hsplit : T (k * h) (T h x) - x = T (k * h) (T h x - x) + (T (k * h) x - x) := by
      rw [map_sub]; abel
    rw [hsplit]
    calc ‖T (k * h) (T h x - x) + (T (k * h) x - x)‖
        ≤ ‖T (k * h) (T h x - x)‖ + ‖T (k * h) x - x‖ := norm_add_le _ _
      _ ≤ ‖T h x - x‖ + k * ‖T h x - x‖ := by
          gcongr
          calc ‖T (k * h) (T h x - x)‖ ≤ ‖T (k * h)‖ * ‖T h x - x‖ := (T (k * h)).le_opNorm _
            _ ≤ 1 * ‖T h x - x‖ := by gcongr; exact hT.2.2.1 _ (by positivity)
            _ = _ := one_mul _
      _ = _ := by push_cast; ring

theorem aux_osc_fixed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ → E →L[ℝ] E) (hT : IsStronglyContinuousContractionSemigroup T)
    (x : E) (hx : Tendsto (fun t : ℝ => t⁻¹ • (T t x - x)) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∀ t : ℝ, 0 ≤ t → T t x = x := by
  intro t ht
  rcases ht.eq_or_lt with rfl | ht
  · simp [hT.1]
  have hlim : Tendsto (fun N : ℕ => t / ((N : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul t
      simp only [mul_one_div, mul_zero] at this
      exact this
    · exact Eventually.of_forall fun N => by
        show 0 < t / ((N : ℝ) + 1)
        positivity
  have h2 := (hx.comp hlim).norm
  have h3 : Tendsto (fun N : ℕ => t * ‖(t / ((N : ℝ) + 1))⁻¹ •
      (T (t / ((N : ℝ) + 1)) x - x)‖) atTop (𝓝 0) := by
    have h4 := h2.const_mul t
    simp only [Function.comp_def, norm_zero, mul_zero] at h4
    exact h4
  have key : ∀ N : ℕ, ‖T t x - x‖ ≤ t * ‖(t / ((N : ℝ) + 1))⁻¹ •
      (T (t / ((N : ℝ) + 1)) x - x)‖ := by
    intro N
    have := aux_osc_telescope T hT x (t / ((N : ℝ) + 1)) (by positivity) (N + 1)
    have e : ((N + 1 : ℕ) : ℝ) * (t / ((N : ℝ) + 1)) = t := by
      push_cast; field_simp
    rw [e] at this
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc ‖T t x - x‖ ≤ ((N + 1 : ℕ) : ℝ) * ‖T (t / ((N : ℝ) + 1)) x - x‖ := this
      _ = t * ((t / ((N : ℝ) + 1))⁻¹ * ‖T (t / ((N : ℝ) + 1)) x - x‖) := by
          push_cast; field_simp
  have hle : ‖T t x - x‖ ≤ 0 := ge_of_tendsto' h3 key
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)

theorem aux_osc_mem_graph {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hopen : IsOpen Ω) (μ : ℝ)
    (a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (b c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    ((1 : (closure Ω) →ᵇ ℝ), (0 : (closure Ω) →ᵇ ℝ)) ∈ obliqueDiffusionGraph Ω μ a b c := by
  have hf1 : ∀ x ∈ Ω, closedRegionRestriction (1 : (closure Ω) →ᵇ ℝ) x = 1 := by
    intro x hx
    simp [closedRegionRestriction, subset_closure hx]
  have hfev : ∀ x ∈ Ω, closedRegionRestriction (1 : (closure Ω) →ᵇ ℝ) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    intro x hx
    filter_upwards [hopen.mem_nhds hx] with y hy using hf1 y hy
  have hd1 : ∀ x ∈ Ω, fderiv ℝ (closedRegionRestriction (1 : (closure Ω) →ᵇ ℝ)) x = 0 := by
    intro x hx
    rw [(hfev x hx).fderiv_eq]
    simp
  have hd2 : ∀ x ∈ Ω, ∀ i j : Fin d,
      fderiv ℝ (fun y => fderiv ℝ (closedRegionRestriction (1 : (closure Ω) →ᵇ ℝ)) y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1) = 0 := by
    intro x hx i j
    have hev : (fun y => fderiv ℝ (closedRegionRestriction (1 : (closure Ω) →ᵇ ℝ)) y (EuclideanSpace.single j 1)) =ᶠ[𝓝 x]
        fun _ => (0 : ℝ) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      rw [hd1 y hy]; rfl
    rw [hev.fderiv_eq]
    simp
  have hg0 : ∀ x, closedRegionRestriction (0 : (closure Ω) →ᵇ ℝ) x = 0 := by
    intro x
    simp [closedRegionRestriction]
  simp only [obliqueDiffusionGraph, Set.mem_ofPred_eq]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact (contDiffOn_const (c := (1 : ℝ))).congr hf1
  · intro i j
    refine ⟨?_, 1, 0, one_pos, le_refl 0, ?_⟩
    · exact (continuousOn_const (c := (0 : ℝ))).congr (fun x hx => hd2 x hx i j)
    · intro ρ _ _ x z _ y hy w hw
      have hy' := connectedComponentIn_subset _ _ hy
      have hw' := connectedComponentIn_subset _ _ hw
      dsimp only
      rw [hd2 y hy'.1 i j, hd2 w hw'.1 i j]
      simp
  · intro x hx
    rw [hg0 x, hd1 x hx]
    simp [hd2 x hx]
  · refine ⟨fun _ => 0, continuous_const, ?_, ?_⟩
    · intro x hx
      rw [hd1 _ hx]
    · intro x _
      rfl

end EthierKurtz

open EthierKurtz

theorem solution (n : ℕ) (hd : 2 ≤ n + 1)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω) (hconnected : IsConnected Ω)
    (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (hboundary : BoundaryCTwiceHolder Ω μ)
    (a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (ha : ∀ x ∈ Ω, (a x).PosSemidef)
    (haHolder : ∀ i j, ComponentHolder Ω μ (fun x => a x i j))
    (hbHolder : ∀ i, ComponentHolder Ω μ (fun x => b x i))
    (helliptic : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Ω,
      ∀ θ : EuclideanSpace ℝ (Fin (n + 1)), ‖θ‖ = 1 →
        ε ≤ ∑ i, ∑ j, θ i * a x i j * θ j)
    (hc : ∀ i, BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x))
    (hoblique : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω,
      ε ≤ ∑ i, c x i * normal x i)
    (T : ℝ → ((closure Ω) →ᵇ ℝ) →L[ℝ] ((closure Ω) →ᵇ ℝ))
    (hT : IsStronglyContinuousContractionSemigroup T)
    (hgen : ∀ f g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f))
      (𝓝[>] (0 : ℝ)) (𝓝 g) ↔
        (f, g) ∈ closure (obliqueDiffusionGraph Ω μ a b c)) :
    ∀ t : ℝ, 0 ≤ t → T t 1 = 1 := by
  apply aux_osc_fixed T hT 1
  exact (hgen 1 0).2 (subset_closure (aux_osc_mem_graph Ω hopen μ a b c))
