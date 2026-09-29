-- Prove2me | solution 1 for DoCarmoDG.injective_parametrization_has_continuous_inverse
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T16:37:56.770815+00:00
-- url     : https://prove2.me/submissions/236e7896-50d8-4c80-a91b-d4d632966d67

import Mathlib
import Definitions.Def_DoCarmo_regular_surface

/-! 42f3c65a DoCarmoDG.injective_parametrization_has_continuous_inverse (do Carmo §2-3, Prop. 4).
Take `g := invFunOn x U`. At `p = x q`, pick a chart `y : W → V ∩ S` of `S` with continuous
inverse `h`, and a continuous left inverse `L` of `dy(w₀)`. By the inverse function theorem
`F = L ∘ y` has a local inverse `G` near `L p`, and near `q`, `h ∘ x = G ∘ L ∘ x =: φ`, so
`x = y ∘ φ` near `q`; hence `dx(q) = dy(w₀) ∘ dφ(q)` and `dφ(q)` is injective, i.e. invertible.
A second use of the inverse function theorem gives a local inverse `R` of `φ` near `w₀`, and
`g = R ∘ h` on `x(U)` near `p` (by injectivity of `x`), which is continuous at `p`. -/

set_option autoImplicit false

namespace ContInvBuild

open DoCarmoDG Filter Topology

theorem key (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : IsRegularSurface S)
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (x : ℝ × ℝ → EuclideanSpace ℝ (Fin 3))
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) x U)
    (hreg : ∀ q ∈ U, Function.Injective (fderiv ℝ x q))
    (hsub : x '' U ⊆ S) (hinj : Set.InjOn x U) (q : ℝ × ℝ) (hq : q ∈ U) :
    ContinuousWithinAt (Function.invFunOn x U) (x '' U) (x q) := by
  have hpS : x q ∈ S := hsub ⟨q, hq, rfl⟩
  obtain ⟨V, W, y, hV, hpV, ⟨hW, hys, hyinj, hyS, ⟨h, hhc, hhy⟩, hyreg⟩, hVS⟩ := hS (x q) hpS
  have hyh : ∀ s ∈ V ∩ S, y (h s) = s ∧ h s ∈ W := by
    intro s hs
    rw [← hVS] at hs
    obtain ⟨w, hw, rfl⟩ := hs
    rw [hhy w hw]; exact ⟨rfl, hw⟩
  have hpVS : x q ∈ V ∩ S := ⟨hpV, hpS⟩
  set w₀ := h (x q) with hw₀def
  obtain ⟨hyw₀, hw₀⟩ := hyh (x q) hpVS
  -- continuous left inverse of dy(w₀)
  have hL := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional (hyreg w₀ hw₀)
  set L := hL.leftInverse
  have hLy : ∀ v, L (fderiv ℝ y w₀ v) = v := hL.leftInverse_leftInverse
  have hyd : HasStrictFDerivAt y (fderiv ℝ y w₀) w₀ :=
    (hys.contDiffAt (hW.mem_nhds hw₀)).hasStrictFDerivAt (by simp)
  have hxd : HasStrictFDerivAt x (fderiv ℝ x q) q :=
    (hsmooth.contDiffAt (hU.mem_nhds hq)).hasStrictFDerivAt (by simp)
  have hF0 : HasStrictFDerivAt (fun w => L (y w)) (L.comp (fderiv ℝ y w₀)) w₀ :=
    L.hasStrictFDerivAt.comp w₀ hyd
  have hcomp : L.comp (fderiv ℝ y w₀) =
      ((ContinuousLinearEquiv.refl ℝ (ℝ × ℝ) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) :
        (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp [hLy]
  rw [hcomp] at hF0
  set G := hF0.localInverse (fun w => L (y w)) _ w₀
  have hGd := hF0.to_localInverse
  have hGF := hF0.eventually_left_inverse
  have hyw₀' : y w₀ = x q := hyw₀
  have hFw : L (y w₀) = L (x q) := by rw [hyw₀']
  rw [hFw] at hGd
  -- φ = G ∘ L ∘ x
  set φ : ℝ × ℝ → ℝ × ℝ := fun q' => G (L (x q')) with hφdef
  have hφd0 := hGd.comp q (L.hasStrictFDerivAt.comp q hxd)
  set D' := ((ContinuousLinearEquiv.refl ℝ (ℝ × ℝ)).symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)).comp
    (L.comp (fderiv ℝ x q)) with hD'def
  have hφd : HasStrictFDerivAt φ D' q := hφd0
  -- h ∘ x → w₀
  have hxc : ContinuousAt x q := hxd.hasFDerivAt.continuousAt
  have hxev : ∀ᶠ q' in 𝓝 q, q' ∈ U ∧ x q' ∈ V ∩ S := by
    filter_upwards [hU.mem_nhds hq, hxc.preimage_mem_nhds (hV.mem_nhds hpV)] with q' h1 h2
    exact ⟨h1, h2, hsub ⟨q', h1, rfl⟩⟩
  have hxt : Tendsto x (𝓝 q) (𝓝[V ∩ S] (x q)) :=
    tendsto_nhdsWithin_iff.2 ⟨hxc, hxev.mono fun _ h => h.2⟩
  have hhc' : ContinuousWithinAt h (V ∩ S) (x q) := by
    have := hhc (x q) (by rw [hVS]; exact hpVS)
    rwa [hVS] at this
  have hhx : Tendsto (fun q' => h (x q')) (𝓝 q) (𝓝 w₀) := hhc'.tendsto.comp hxt
  have hN : ∀ᶠ q' in 𝓝 q, q' ∈ U ∧ x q' ∈ V ∩ S ∧ φ q' = h (x q') := by
    filter_upwards [hxev, hhx.eventually hGF] with q' h1 h2
    refine ⟨h1.1, h1.2, ?_⟩
    obtain ⟨e1, _⟩ := hyh (x q') h1.2
    show G (L (x q')) = h (x q')
    have e2 : L (x q') = L (y (h (x q'))) := by rw [e1]
    rw [e2]; exact h2
  have hφq : φ q = w₀ := (hN.self_of_nhds).2.2
  -- dφ(q) is injective
  have hxeq : x =ᶠ[𝓝 q] fun q' => y (φ q') := by
    filter_upwards [hN] with q' h1
    rw [h1.2.2]; exact ((hyh (x q') h1.2.1).1).symm
  have hyd' : HasFDerivAt y (fderiv ℝ y w₀) (φ q) := by rw [hφq]; exact hyd.hasFDerivAt
  have hcompd : HasFDerivAt (fun q' => y (φ q')) ((fderiv ℝ y w₀).comp D') q :=
    hyd'.comp q hφd.hasFDerivAt
  have hdx : fderiv ℝ x q = (fderiv ℝ y w₀).comp D' :=
    hxd.hasFDerivAt.unique (hcompd.congr_of_eventuallyEq hxeq)
  have hD'inj : Function.Injective D' := by
    intro a b hab
    apply hreg q hq
    rw [hdx]; simp [hab]
  set De : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
    (LinearEquiv.ofInjectiveEndo (D' : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) hD'inj).toContinuousLinearEquiv
  have hDe : (De : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = D' := ContinuousLinearMap.ext fun v => rfl
  have hΦ : HasStrictFDerivAt φ (De : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) q := by rw [hDe]; exact hφd
  set R := hΦ.localInverse φ _ q
  have hRt : Tendsto R (𝓝 (φ q)) (𝓝 q) := hΦ.localInverse_tendsto
  have hRinv := hΦ.eventually_right_inverse
  rw [hφq] at hRt hRinv
  -- the neighbourhood filter of p inside x(U)
  have hle : 𝓝[x '' U] (x q) ≤ 𝓝[V ∩ S] (x q) := by
    rw [← nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hpV))]
    apply nhdsWithin_mono
    rintro s ⟨hs1, hs2⟩
    exact ⟨hs1, hsub hs2⟩
  have hht : Tendsto h (𝓝[x '' U] (x q)) (𝓝 w₀) := hhc'.tendsto.mono_left hle
  have hRh : Tendsto (fun s => R (h s)) (𝓝[x '' U] (x q)) (𝓝 q) := hRt.comp hht
  have hgq : Function.invFunOn x U (x q) = q := hinj.leftInvOn_invFunOn hq
  show Tendsto (Function.invFunOn x U) (𝓝[x '' U] (x q)) (𝓝 (Function.invFunOn x U (x q)))
  rw [hgq]
  refine hRh.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hle (self_mem_nhdsWithin), hht.eventually hRinv,
    hRh.eventually hN] with s hs1 hs2 hs3 hs4
  obtain ⟨q₁, hq₁, rfl⟩ := hs1
  obtain ⟨hU2, hV2, hφ2⟩ := hs4
  have e1 := (hyh (x (R (h (x q₁)))) hV2).1
  have e2 := (hyh (x q₁) hs2).1
  have hxx : x (R (h (x q₁))) = x q₁ := by
    rw [← e1, ← hφ2, hs3, e2]
  rw [hinj.leftInvOn_invFunOn hq₁]
  exact (hinj hU2 hq₁ hxx)

end ContInvBuild

open DoCarmoDG in
theorem solution
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : IsRegularSurface S)
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (x : ℝ × ℝ → EuclideanSpace ℝ (Fin 3))
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) x U)
    (hreg : ∀ q ∈ U, Function.Injective (fderiv ℝ x q))
    (hsub : x '' U ⊆ S) (hinj : Set.InjOn x U) :
    ∃ g : EuclideanSpace ℝ (Fin 3) → ℝ × ℝ,
      ContinuousOn g (x '' U) ∧ ∀ q ∈ U, g (x q) = q := by
  refine ⟨Function.invFunOn x U, ?_, fun q hq => hinj.leftInvOn_invFunOn hq⟩
  rintro _ ⟨q, hq, rfl⟩
  exact ContInvBuild.key S hS U hU x hsmooth hreg hsub hinj q hq
