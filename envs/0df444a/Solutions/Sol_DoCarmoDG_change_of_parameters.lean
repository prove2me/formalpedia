-- Prove2me | solution 1 for DoCarmoDG.change_of_parameters
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T12:43:54.656388+00:00
-- url     : https://prove2.me/submissions/a1ab1f38-03cd-4723-b18d-f5d9a37d86af

import Mathlib
import Definitions.Def_DoCarmo_regular_surface

/-! 0f98a50f DoCarmoDG.change_of_parameters (do Carmo §2-3 Prop 1).
Route (no ℝ³ extension, no cross product): do Carmo's local factorization `x⁻¹ = (L ∘ x)⁻¹ ∘ L`.
* `dc4_local_left_inverse`: a linear left inverse `L` of the injective `dx_p` makes `L ∘ x` have
  derivative `id` at `p`; `ContDiffAt.localInverse` gives a smooth `Φ := (L ∘ x)⁻¹ ∘ L` near `x p`
  with `Φ ∘ x = id` near `p`.
* `dc4_chart_transport`: continuity of the given left inverse `g` of a chart `z` makes `g ∘ f`
  agree with the smooth `Φ ∘ f` near any point where `f` lands in `z '' Uz`.
* `dc4_overlap_open`: at `y q0 = x p0` take the chart `z` from `IsRegularSurface S` (its image is
  `W ∩ S`, so both `x` and `y` land in it nearby). `α := g_z ∘ x` is smooth, `z ∘ α = x`, so
  `dz ∘ dα = dx` is injective, hence `dα` is invertible and `α` maps neighbourhoods of `p0` onto
  neighbourhoods of `a0` (`map_nhds_eq_of_equiv`); `β := g_z ∘ y → a0`, so `y q = z (β q) = z (α w) = x w`.
* `dc4_overlap_smooth`: `h := g_x ∘ y` equals `Φ_x ∘ y` near each point of the open overlap. -/

set_option autoImplicit false

namespace DoCarmo4Build

open Filter Topology Set DoCarmoDG

/-- Local smooth left inverse of an immersion `ℝ² → ℝ³` (do Carmo's `x⁻¹ = (π ∘ x)⁻¹ ∘ π`):
a linear left inverse `L` of `dx_p` makes `L ∘ x` a local diffeomorphism at `p`. -/
theorem dc4_local_left_inverse (x : ℝ × ℝ → EuclideanSpace ℝ (Fin 3)) (p : ℝ × ℝ)
    (hx : ContDiffAt ℝ (⊤ : ℕ∞) x p) (hinj : Function.Injective (fderiv ℝ x p)) :
    ∃ Φ : EuclideanSpace ℝ (Fin 3) → ℝ × ℝ,
      ContDiffAt ℝ (⊤ : ℕ∞) Φ (x p) ∧ ∀ᶠ w in 𝓝 p, Φ (x w) = w := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective
    ((fderiv ℝ x p : (ℝ × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
      (ℝ × ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) (LinearMap.ker_eq_bot.2 hinj)
  let L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ × ℝ := LinearMap.toContinuousLinearMap g
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hdiff : DifferentiableAt ℝ x p := hx.differentiableAt hn
  have hf : ContDiffAt ℝ (⊤ : ℕ∞) (L ∘ x) p := L.contDiff.contDiffAt.comp p hx
  have hf' : HasFDerivAt (L ∘ x)
      ((ContinuousLinearEquiv.refl ℝ (ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ × ℝ)) p := by
    have h1 := L.hasFDerivAt.comp p hdiff.hasFDerivAt
    have heq : L.comp (fderiv ℝ x p) =
        ((ContinuousLinearEquiv.refl ℝ (ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ × ℝ)) := by
      refine ContinuousLinearMap.ext fun v => ?_
      have h2 := LinearMap.congr_fun hg v
      simpa [L] using h2
    exact heq ▸ h1
  refine ⟨hf.localInverse hf' hn ∘ L, ?_, ?_⟩
  · exact (hf.to_localInverse hf' hn).comp (x p) L.contDiff.contDiffAt
  · exact (hf.hasStrictFDerivAt' hf' hn).eventually_left_inverse

/-- Transport through a chart `z`: if `f` lands (near `p`) in `z '' Uz` and `f p = z a`, then the
continuous left inverse `g` of `z` composed with `f` agrees near `p` with `Φ ∘ f`, `Φ` smooth. -/
theorem dc4_chart_transport (Uz : Set (ℝ × ℝ)) (z : ℝ × ℝ → EuclideanSpace ℝ (Fin 3))
    (hUz : IsOpen Uz) (hz : ContDiffOn ℝ (⊤ : ℕ∞) z Uz)
    (hzd : ∀ q ∈ Uz, Function.Injective (fderiv ℝ z q))
    (g : EuclideanSpace ℝ (Fin 3) → ℝ × ℝ) (hg : ContinuousOn g (z '' Uz))
    (hgz : ∀ q ∈ Uz, g (z q) = q)
    (f : ℝ × ℝ → EuclideanSpace ℝ (Fin 3)) (p a : ℝ × ℝ) (ha : a ∈ Uz) (hfp : f p = z a)
    (hfc : ContinuousAt f p) (hev : ∀ᶠ w in 𝓝 p, f w ∈ z '' Uz) :
    ∃ Φ : EuclideanSpace ℝ (Fin 3) → ℝ × ℝ, ContDiffAt ℝ (⊤ : ℕ∞) Φ (z a) ∧
      Tendsto (g ∘ f) (𝓝 p) (𝓝 a) ∧
      ∀ᶠ w in 𝓝 p, Φ (f w) = g (f w) ∧ z (g (f w)) = f w ∧ g (f w) ∈ Uz := by
  obtain ⟨Φ, hΦ, hΦev⟩ :=
    dc4_local_left_inverse z a (hz.contDiffAt (hUz.mem_nhds ha)) (hzd a ha)
  have htend : Tendsto (g ∘ f) (𝓝 p) (𝓝 a) := by
    have h1 : Tendsto f (𝓝 p) (𝓝[z '' Uz] (z a)) := by
      rw [← hfp]; exact tendsto_nhdsWithin_iff.2 ⟨hfc.tendsto, hev⟩
    have h2 : ContinuousWithinAt g (z '' Uz) (z a) := hg (z a) (mem_image_of_mem z ha)
    rw [ContinuousWithinAt, hgz a ha] at h2
    exact h2.comp h1
  refine ⟨Φ, hΦ, htend, ?_⟩
  filter_upwards [hev, htend.eventually hΦev] with w hw hw2
  obtain ⟨c, hc, hcw⟩ := hw
  have hgc : g (f w) = c := by rw [← hcw, hgz c hc]
  simp only [Function.comp_apply] at hw2
  rw [hgc] at hw2 ⊢
  refine ⟨?_, hcw, hc⟩
  rw [← hcw]; exact hw2

/-- Openness of the overlap `V ∩ y⁻¹(x(U))`; this is where `IsRegularSurface S` is used. -/
theorem dc4_overlap_open (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : IsRegularSurface S)
    (U V : Set (ℝ × ℝ)) (x y : ℝ × ℝ → EuclideanSpace ℝ (Fin 3))
    (hx : IsSurfaceParametrization U x S) (hy : IsSurfaceParametrization V y S) :
    IsOpen (V ∩ y ⁻¹' (x '' U)) := by
  obtain ⟨hUo, hxs, -, hxS, -, hxd⟩ := hx
  obtain ⟨hVo, hys, -, hyS, -, -⟩ := hy
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  rw [isOpen_iff_mem_nhds]
  rintro q0 ⟨hq0V, p0, hp0U, hxp0⟩
  have hsS : y q0 ∈ S := hyS (mem_image_of_mem y hq0V)
  obtain ⟨W, Uz, z, hWo, hsW, ⟨hUzo, hzs, -, -, ⟨gz, hgzc, hgz⟩, hzd⟩, hzW⟩ := hS (y q0) hsS
  have hsz : y q0 ∈ z '' Uz := by rw [hzW]; exact ⟨hsW, hsS⟩
  obtain ⟨a0, ha0, hza0⟩ := hsz
  have hxcd : ContDiffAt ℝ (⊤ : ℕ∞) x p0 := hxs.contDiffAt (hUo.mem_nhds hp0U)
  have hycd : ContDiffAt ℝ (⊤ : ℕ∞) y q0 := hys.contDiffAt (hVo.mem_nhds hq0V)
  have hxc : ContinuousAt x p0 := hxcd.continuousAt
  have hyc : ContinuousAt y q0 := hycd.continuousAt
  have hevx : ∀ᶠ w in 𝓝 p0, x w ∈ z '' Uz := by
    have h1 : ∀ᶠ w in 𝓝 p0, x w ∈ W :=
      hxc.preimage_mem_nhds (hWo.mem_nhds (by rw [hxp0]; exact hsW))
    filter_upwards [h1, hUo.mem_nhds hp0U] with w hw hwU
    rw [hzW]; exact ⟨hw, hxS (mem_image_of_mem x hwU)⟩
  have hevy : ∀ᶠ q in 𝓝 q0, y q ∈ z '' Uz := by
    have h1 : ∀ᶠ q in 𝓝 q0, y q ∈ W := hyc.preimage_mem_nhds (hWo.mem_nhds hsW)
    filter_upwards [h1, hVo.mem_nhds hq0V] with q hq hqV
    rw [hzW]; exact ⟨hq, hyS (mem_image_of_mem y hqV)⟩
  obtain ⟨Φ, hΦ, -, hαev⟩ := dc4_chart_transport Uz z hUzo hzs hzd gz hgzc hgz x p0 a0 ha0
    (by rw [hxp0, hza0]) hxc hevx
  obtain ⟨Ψ, -, hβt, hβev⟩ := dc4_chart_transport Uz z hUzo hzs hzd gz hgzc hgz y q0 a0 ha0
    hza0.symm hyc hevy
  have hΦx : ContDiffAt ℝ (⊤ : ℕ∞) (Φ ∘ x) p0 := by
    refine ContDiffAt.comp p0 ?_ hxcd
    rw [hxp0, ← hza0]; exact hΦ
  have hα : ContDiffAt ℝ (⊤ : ℕ∞) (gz ∘ x) p0 :=
    hΦx.congr_of_eventuallyEq (by filter_upwards [hαev] with w hw; exact hw.1.symm)
  have hα0 : (gz ∘ x) p0 = a0 := by
    simp only [Function.comp_apply]; rw [hxp0, ← hza0, hgz a0 ha0]
  have hzeq : (z ∘ (gz ∘ x)) =ᶠ[𝓝 p0] x := by
    filter_upwards [hαev] with w hw; exact hw.2.1
  have hzcd : ContDiffAt ℝ (⊤ : ℕ∞) z a0 := hzs.contDiffAt (hUzo.mem_nhds ha0)
  have hder : fderiv ℝ x p0 = (fderiv ℝ z a0).comp (fderiv ℝ (gz ∘ x) p0) := by
    rw [← hzeq.fderiv_eq, fderiv_comp p0 (by rw [hα0]; exact hzcd.differentiableAt hn)
      (hα.differentiableAt hn), hα0]
  have hαinj : Function.Injective (fderiv ℝ (gz ∘ x) p0) := by
    have h1 := hxd p0 hp0U
    rw [hder, ContinuousLinearMap.coe_comp] at h1
    exact h1.of_comp
  let e : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
    (LinearEquiv.ofInjectiveEndo
      ((fderiv ℝ (gz ∘ x) p0 : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)
      hαinj).toContinuousLinearEquiv
  have hstrict : HasStrictFDerivAt (gz ∘ x) (e : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) p0 :=
    hα.hasStrictFDerivAt hn
  have hmap := hstrict.map_nhds_eq_of_equiv
  rw [hα0] at hmap
  have hA : {w | w ∈ U ∧ z ((gz ∘ x) w) = x w} ∈ 𝓝 p0 := by
    filter_upwards [hUo.mem_nhds hp0U, hzeq] with w hw1 hw2
    exact ⟨hw1, hw2⟩
  have himg : (gz ∘ x) '' {w | w ∈ U ∧ z ((gz ∘ x) w) = x w} ∈ 𝓝 a0 := by
    rw [← hmap]; exact image_mem_map hA
  filter_upwards [hβt himg, hβev, hVo.mem_nhds hq0V] with q hq hq2 hqV
  obtain ⟨w, ⟨hwU, hw⟩, hwq⟩ := hq
  refine ⟨hqV, w, hwU, ?_⟩
  rw [← hw, ← hq2.2.1]
  simp only [Function.comp_apply] at hwq ⊢
  rw [hwq]

/-- Smoothness of `g_x ∘ y` on the (open) overlap. -/
theorem dc4_overlap_smooth (U V : Set (ℝ × ℝ)) (x y : ℝ × ℝ → EuclideanSpace ℝ (Fin 3))
    (hUo : IsOpen U) (hxs : ContDiffOn ℝ (⊤ : ℕ∞) x U)
    (hxd : ∀ q ∈ U, Function.Injective (fderiv ℝ x q))
    (gx : EuclideanSpace ℝ (Fin 3) → ℝ × ℝ) (hgxc : ContinuousOn gx (x '' U))
    (hgx : ∀ q ∈ U, gx (x q) = q)
    (hVo : IsOpen V) (hys : ContDiffOn ℝ (⊤ : ℕ∞) y V)
    (hD : IsOpen (V ∩ y ⁻¹' (x '' U))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (gx ∘ y) (V ∩ y ⁻¹' (x '' U)) := by
  intro q0 hq0
  obtain ⟨hq0V, p0, hp0U, hxp0⟩ := hq0
  have hycd : ContDiffAt ℝ (⊤ : ℕ∞) y q0 := hys.contDiffAt (hVo.mem_nhds hq0V)
  have hev : ∀ᶠ q in 𝓝 q0, y q ∈ x '' U := by
    filter_upwards [hD.mem_nhds ⟨hq0V, p0, hp0U, hxp0⟩] with q hq
    exact hq.2
  obtain ⟨Φ, hΦ, -, hΦev⟩ := dc4_chart_transport U x hUo hxs hxd gx hgxc hgx y q0 p0 hp0U
    hxp0.symm hycd.continuousAt hev
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (Φ ∘ y) q0 := by
    refine ContDiffAt.comp q0 ?_ hycd
    rw [← hxp0]; exact hΦ
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (gx ∘ y) q0 :=
    h1.congr_of_eventuallyEq (by filter_upwards [hΦev] with q hq; exact hq.1.symm)
  exact h2.contDiffWithinAt

end DoCarmo4Build

set_option maxHeartbeats 4000000 in
open DoCarmoDG in
theorem solution
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : IsRegularSurface S)
    (U V : Set (ℝ × ℝ)) (x y : ℝ × ℝ → EuclideanSpace ℝ (Fin 3))
    (hx : IsSurfaceParametrization U x S) (hy : IsSurfaceParametrization V y S) :
    IsOpen (V ∩ y ⁻¹' (x '' U)) ∧ IsOpen (U ∩ x ⁻¹' (y '' V)) ∧
      ∃ h hinv : ℝ × ℝ → ℝ × ℝ,
        (∀ q ∈ V ∩ y ⁻¹' (x '' U),
            h q ∈ U ∩ x ⁻¹' (y '' V) ∧ x (h q) = y q ∧ hinv (h q) = q) ∧
        (∀ q ∈ U ∩ x ⁻¹' (y '' V),
            hinv q ∈ V ∩ y ⁻¹' (x '' U) ∧ y (hinv q) = x q ∧ h (hinv q) = q) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) h (V ∩ y ⁻¹' (x '' U)) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) hinv (U ∩ x ⁻¹' (y '' V)) := by
  have hDo := DoCarmo4Build.dc4_overlap_open S hS U V x y hx hy
  have hEo := DoCarmo4Build.dc4_overlap_open S hS V U y x hy hx
  obtain ⟨hUo, hxs, -, -, ⟨gx, hgxc, hgx⟩, hxd⟩ := hx
  obtain ⟨hVo, hys, -, -, ⟨gy, hgyc, hgy⟩, hyd⟩ := hy
  refine ⟨hDo, hEo, gx ∘ y, gy ∘ x, ?_, ?_,
    DoCarmo4Build.dc4_overlap_smooth U V x y hUo hxs hxd gx hgxc hgx hVo hys hDo,
    DoCarmo4Build.dc4_overlap_smooth V U y x hVo hys hyd gy hgyc hgy hUo hxs hEo⟩
  · rintro q ⟨hqV, p, hpU, hxp⟩
    have hh : gx (y q) = p := by rw [← hxp, hgx p hpU]
    simp only [Function.comp_apply, hh]
    refine ⟨⟨hpU, q, hqV, hxp.symm⟩, hxp, ?_⟩
    rw [hxp, hgy q hqV]
  · rintro p ⟨hpU, q, hqV, hyq⟩
    have hh : gy (x p) = q := by rw [← hyq, hgy q hqV]
    simp only [Function.comp_apply, hh]
    refine ⟨⟨hqV, p, hpU, hyq.symm⟩, hyq, ?_⟩
    rw [hyq, hgx p hpU]
