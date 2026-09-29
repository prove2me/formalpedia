-- Prove2me | solution 1 for EthierKurtz.oblique_resolvent_positive
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-27T21:26:56.253361+00:00
-- url     : https://prove2.me/submissions/210c17ea-9cbb-4937-9d63-31352f3d1ecf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup
import Theorems.Thm_EthierKurtz_hessian_posSemidef_of_isLocalMin_on
import Theorems.Thm_EthierKurtz_resolvent_positive_interior_step
import Theorems.Thm_EthierKurtz_resolvent_positive_boundary_step
import Theorems.Thm_EthierKurtz_oblique_boundary_differentiability_step

open Filter
open scoped Topology BoundedContinuousFunction

open EthierKurtz

/-- Reduction of resolvent positivity to the maximum principle: a negative
value forces a global minimum over the compact closure; at an interior
minimum the Hessian sign (proved) contradicts the resolvent inequality via
the interior step, and at a frontier minimum the boundary step applies via
the boundary differentiability step. -/
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
      ε ≤ ∑ i, c x i * normal x i) :
    ∀ fg ∈ obliqueDiffusionGraph Ω μ a b c, ∀ lam : ℝ, 0 < lam →
      (∀ x, 0 ≤ (lam • fg.1 - fg.2) x) → ∀ x, 0 ≤ fg.1 x := by
  intro fg hmem lam hlam h x
  by_contra hxneg
  push Not at hxneg
  have hmem' : CTwiceHolder Ω μ (closedRegionRestriction fg.1) ∧
      (∀ x ∈ Ω, closedRegionRestriction fg.2 x = (1 / 2 : ℝ) *
        (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        a x i j * fderiv ℝ
          (fun y => fderiv ℝ (closedRegionRestriction fg.1) y
            (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single i 1)) +
        fderiv ℝ (closedRegionRestriction fg.1) x (b x)) ∧
      (∃ J : (closure Ω) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ),
        Continuous J ∧
        (∀ x : closure Ω, (x : EuclideanSpace ℝ (Fin (n + 1))) ∈ Ω →
          J x = fderiv ℝ (closedRegionRestriction fg.1) x) ∧
        ∀ x : closure Ω, (x : EuclideanSpace ℝ (Fin (n + 1))) ∈ frontier Ω →
          J x (c x) = 0) := hmem
  obtain ⟨hfC, hgId, hJ⟩ := hmem'
  obtain ⟨J, hJc, hJid, hJb⟩ := hJ
  have e1 : closedRegionRestriction fg.1
      (x : EuclideanSpace ℝ (Fin (n + 1))) = fg.1 x := by
    obtain ⟨v, hv⟩ := x
    show closedRegionRestriction fg.1 v = fg.1 ⟨v, hv⟩
    unfold closedRegionRestriction
    rw [dif_pos hv]
  have hcont : ContinuousOn (closedRegionRestriction fg.1) (closure Ω) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (closure Ω).domRestrict (closedRegionRestriction fg.1) =
        (fun y : (closure Ω) => fg.1 y) := by
      funext y
      obtain ⟨v, hv⟩ := y
      show closedRegionRestriction fg.1 v = fg.1 ⟨v, hv⟩
      unfold closedRegionRestriction
      rw [dif_pos hv]
    rw [heq]
    exact fg.1.continuous
  have hcontG : ContinuousOn (closedRegionRestriction fg.2) (closure Ω) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (closure Ω).domRestrict (closedRegionRestriction fg.2) =
        (fun y : (closure Ω) => fg.2 y) := by
      funext y
      obtain ⟨v, hv⟩ := y
      show closedRegionRestriction fg.2 v = fg.2 ⟨v, hv⟩
      unfold closedRegionRestriction
      rw [dif_pos hv]
    rw [heq]
    exact fg.2.continuous
  have hcomp : IsCompact (closure Ω) := hbounded.isCompact_closure
  have hne : (closure Ω).Nonempty := hconnected.nonempty.closure
  obtain ⟨x₀, hx₀mem, hx₀min⟩ := hcomp.exists_isMinOn hne hcont
  have hle : ∀ y ∈ closure Ω,
      closedRegionRestriction fg.1 x₀ ≤ closedRegionRestriction fg.1 y :=
    isMinOn_iff.mp hx₀min
  have hx₀neg : closedRegionRestriction fg.1 x₀ < 0 := by
    have h2 : closedRegionRestriction fg.1 x₀ ≤
        closedRegionRestriction fg.1 (x : EuclideanSpace ℝ (Fin (n + 1))) :=
      hle _ x.property
    rw [e1] at h2
    exact lt_of_le_of_lt h2 hxneg
  have hop0 : 0 ≤ lam * closedRegionRestriction fg.1 x₀ -
      closedRegionRestriction fg.2 x₀ := by
    have h0 := h ⟨x₀, hx₀mem⟩
    rw [BoundedContinuousFunction.sub_apply,
      BoundedContinuousFunction.smul_apply, smul_eq_mul] at h0
    have r1 : fg.1 ⟨x₀, hx₀mem⟩ = closedRegionRestriction fg.1 x₀ := by
      unfold closedRegionRestriction
      rw [dif_pos hx₀mem]
    have r2 : fg.2 ⟨x₀, hx₀mem⟩ = closedRegionRestriction fg.2 x₀ := by
      unfold closedRegionRestriction
      rw [dif_pos hx₀mem]
    rw [r1, r2] at h0
    exact h0
  by_cases hxΩ : x₀ ∈ Ω
  · -- Interior minimum: the Hessian sign contradicts the resolvent inequality.
    have hnbhd : Ω ∈ 𝓝 x₀ := hopen.mem_nhds hxΩ
    have hminloc : IsLocalMin (closedRegionRestriction fg.1) x₀ :=
      Filter.mem_of_superset hnbhd (fun y hy => hle y (subset_closure hy))
    have hH : ∀ v, 0 ≤ (fderiv ℝ
        (fun y => fderiv ℝ (closedRegionRestriction fg.1) y v) x₀) v :=
      fun v => hessian_posSemidef_of_isLocalMin_on hfC.1 hnbhd hminloc v
    have hId : closedRegionRestriction fg.2 x₀ = (1 / 2 : ℝ) *
        (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        a x₀ i j * fderiv ℝ
          (fun y => fderiv ℝ (closedRegionRestriction fg.1) y
            (EuclideanSpace.single j 1)) x₀
          (EuclideanSpace.single i 1)) +
        fderiv ℝ (closedRegionRestriction fg.1) x₀ (b x₀) :=
      hgId x₀ hxΩ
    exact resolvent_positive_interior_step hopen hxΩ hfC.1 hminloc hH
      (ha x₀ hxΩ) hId hlam hx₀neg hop0
  · -- Frontier minimum: the Hopf-type boundary step applies.
    have hxfr : x₀ ∈ frontier Ω := by
      show x₀ ∈ closure Ω \ interior Ω
      exact ⟨hx₀mem, fun h => hxΩ (interior_subset h)⟩
    have hD := oblique_boundary_differentiability_step hxfr hx₀mem
      hfC.1 hcont hJc hJid
    obtain ⟨ε, hε, hob⟩ := hoblique
    exact resolvent_positive_boundary_step hxfr hboundary hμ hfC.1 hcont
      hcontG hD (hJb ⟨x₀, hx₀mem⟩ hxfr) (hnormal x₀ hxfr)
      ⟨ε, hε, hob x₀ hxfr⟩ hgId ha helliptic hle hx₀neg hlam hop0
