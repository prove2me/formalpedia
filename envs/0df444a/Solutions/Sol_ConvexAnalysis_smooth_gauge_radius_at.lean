-- Prove2me | solution 1 for ConvexAnalysis.smooth_gauge_radius_at
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T01:12:20.017266+00:00
-- url     : https://prove2.me/submissions/a5a44475-30d0-476e-ad62-d8cfc55b17ac

import Mathlib
import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel

set_option autoImplicit false
set_option maxHeartbeats 800000

open BirkhoffGlobalSection Filter Set ContDiff Topology in
theorem solution (K : Set Phase) (hK : Convex ℝ K)
    (h0 : K ∈ nhds (0 : Phase)) (hb : Bornology.IsVonNBounded ℝ K)
    (F : Phase → ℝ) (hzero : ∀ x ∈ frontier K, F x = 0)
    (u : Phase) (hu : u ∈ frontier K) (hc : ContDiffAt ℝ ∞ F u)
    (hrad : fderiv ℝ F u u ≠ 0) :
    ContDiffAt ℝ ∞ (fun x => (gauge K x)⁻¹) u := by
  let f : Phase × ℝ → ℝ := fun p => F (p.2 • p.1)
  have hsm : ContDiffAt ℝ ∞ (fun p : Phase × ℝ => p.2 • p.1) (u, (1:ℝ)) := by fun_prop
  have hc' : ContDiffAt ℝ ∞ F ((fun p : Phase × ℝ => p.2 • p.1) (u, (1:ℝ))) := by
    simpa using hc
  have cdf : ContDiffAt ℝ ∞ f (u, (1:ℝ)) := hc'.comp (u, (1:ℝ)) hsm
  have pn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hF : HasFDerivAt F (fderiv ℝ F u) u :=
    (hc.differentiableAt (by simp)).hasFDerivAt
  have hS := (hasFDerivAt_snd (𝕜 := ℝ) (p := (u, (1:ℝ)))).smul (hasFDerivAt_fst (𝕜 := ℝ) (p := (u, (1:ℝ))))
  have hF' : HasFDerivAt F (fderiv ℝ F u) ((u, (1:ℝ)).2 • (u, (1:ℝ)).1) := by simpa using hF
  have hfd : HasFDerivAt f _ (u, (1:ℝ)) := hF'.comp (u, (1:ℝ)) hS
  have hinv : (fderiv ℝ f (u, (1:ℝ)) ∘L ContinuousLinearMap.inr ℝ Phase ℝ).IsInvertible := by
    rw [hfd.fderiv]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ hrad), ?_⟩
    apply ContinuousLinearMap.ext_ring
    simp
  have hu0 : f (u, (1:ℝ)) = 0 := by simp [f, hzero u hu]
  have hev := cdf.eventually_apply_eq_iff_implicitFunction pn hinv
  have hψ := cdf.contDiffAt_implicitFunction pn hinv
  have hg1 : gauge K u = 1 := (gauge_eq_one_iff_mem_frontier hK h0).2 hu
  have hgc : Continuous (gauge K) := continuous_gauge hK h0
  have htend : Tendsto (fun x => (x, (gauge K x)⁻¹)) (𝓝 u) (𝓝 (u, (1:ℝ))) := by
    have : Tendsto (fun x => (gauge K x)⁻¹) (𝓝 u) (𝓝 ((gauge K u)⁻¹)) :=
      (hgc.tendsto u).inv₀ (by rw [hg1]; norm_num)
    rw [hg1, inv_one] at this
    exact tendsto_id.prodMk_nhds this
  have hpos : ∀ᶠ x in 𝓝 u, 0 < gauge K x :=
    (hgc.tendsto u).eventually (lt_mem_nhds (by rw [hg1]; norm_num))
  have hev2 := htend.eventually hev
  refine hψ.congr_of_eventuallyEq ?_
  filter_upwards [hev2, hpos] with x hx hxp
  rw [hu0] at hx
  have hfr : (gauge K x)⁻¹ • x ∈ frontier K := by
    rw [← gauge_eq_one_iff_mem_frontier hK h0, gauge_smul_of_nonneg (inv_nonneg.2 hxp.le),
      smul_eq_mul, inv_mul_cancel₀ hxp.ne']
  exact (hx.1 (by simp [f, hzero _ hfr])).symm
