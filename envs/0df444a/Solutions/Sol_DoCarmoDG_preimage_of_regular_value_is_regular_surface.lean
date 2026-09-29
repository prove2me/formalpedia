-- Prove2me | solution 1 for DoCarmoDG.preimage_of_regular_value_is_regular_surface
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T17:58:26.745809+00:00
-- url     : https://prove2.me/submissions/0e212900-7c34-44e4-9a2b-ef85d082e0b0

import Mathlib
import Definitions.Def_DoCarmo_regular_surface

/-! 5c757842 DoCarmoDG.preimage_of_regular_value_is_regular_surface (do Carmo §2-2, Prop. 2).
At `p` with `f p = a`, `df_p ≠ 0`, so `∂_k f(p) ≠ 0` for some coordinate `k`; let `i, j` be the
other two and `π = (proj i, proj j)`. The map `Fm s = (π s, f s)` has invertible derivative
`(π, df_s)` wherever `∂_k f(s) ≠ 0`. The inverse function theorem gives a partial homeomorphism
`Φ`, restricted to the open set `Ω = U ∩ {∂_k f ≠ 0}`, so `Φ.symm` is C^∞ on its target
(`contDiffAt_symm`). The parametrization is `X z = Φ.symm (z, a)` on
`U' = {z | (z, a) ∈ Φ.target}`, with inverse `π` and `X(U') = Φ.source ∩ S`; `π ∘ X = id` near
each point gives `π ∘ dX = id`, so `dX` is injective. -/

set_option autoImplicit false

namespace PreimBuild

open DoCarmoDG Filter Topology

theorem decomp (v : EuclideanSpace ℝ (Fin 3)) :
    v = v 0 • EuclideanSpace.single 0 1 + v 1 • EuclideanSpace.single 1 1 +
      v 2 • EuclideanSpace.single 2 1 := by
  ext n; fin_cases n <;> simp

theorem exists_coord (D : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) (hD : D ≠ 0) :
    ∃ k : Fin 3, D (EuclideanSpace.single k 1) ≠ 0 := by
  by_contra hc
  push Not at hc
  apply hD
  refine ContinuousLinearMap.ext fun v => ?_
  rw [decomp v]
  simp [hc]

theorem mkEquiv (i j k : Fin 3) (hijk : ∀ n : Fin 3, n = i ∨ n = j ∨ n = k)
    (hik : i ≠ k) (hjk : j ≠ k)
    (D : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) (hD : D (EuclideanSpace.single k 1) ≠ 0) :
    ∃ e : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] ((ℝ × ℝ) × ℝ),
      (e : EuclideanSpace ℝ (Fin 3) →L[ℝ] (ℝ × ℝ) × ℝ) =
        ((EuclideanSpace.proj i).prod (EuclideanSpace.proj j)).prod D := by
  set T := ((EuclideanSpace.proj i).prod (EuclideanSpace.proj j)).prod D with hT
  have hinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h1 : v i = 0 := by
      have := congrArg (fun z => z.1.1) hv; simpa [hT] using this
    have h2 : v j = 0 := by
      have := congrArg (fun z => z.1.2) hv; simpa [hT] using this
    have h3 : D v = 0 := by
      have := congrArg (fun z => z.2) hv; simpa [hT] using this
    have hv' : v = v k • EuclideanSpace.single k 1 := by
      ext n
      rcases hijk n with rfl | rfl | rfl
      · simp [h1, hik]
      · simp [h2, hjk]
      · simp
    rw [hv', map_smul, smul_eq_mul, mul_eq_zero] at h3
    have hk0 : v k = 0 := h3.resolve_right hD
    rw [hv', hk0, zero_smul]
  refine ⟨(LinearMap.linearEquivOfInjective
    (T : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] (ℝ × ℝ) × ℝ) hinj (by simp)).toContinuousLinearEquiv, ?_⟩
  exact ContinuousLinearMap.ext fun v => rfl

theorem local_param (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : IsOpen U)
    (f : EuclideanSpace ℝ (Fin 3) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (a : ℝ)
    (p : EuclideanSpace ℝ (Fin 3)) (hpU : p ∈ U)
    (i j k : Fin 3) (hijk : ∀ n : Fin 3, n = i ∨ n = j ∨ n = k)
    (hik : i ≠ k) (hjk : j ≠ k)
    (hk : fderiv ℝ f p (EuclideanSpace.single k 1) ≠ 0) :
    ∃ (V : Set (EuclideanSpace ℝ (Fin 3))) (U' : Set (ℝ × ℝ))
      (X : ℝ × ℝ → EuclideanSpace ℝ (Fin 3)),
      IsOpen V ∧ p ∈ V ∧ IsSurfaceParametrization U' X {q | q ∈ U ∧ f q = a} ∧
        X '' U' = V ∩ {q | q ∈ U ∧ f q = a} := by
  set π : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ × ℝ :=
    (EuclideanSpace.proj i).prod (EuclideanSpace.proj j) with hπ
  set Fm : EuclideanSpace ℝ (Fin 3) → (ℝ × ℝ) × ℝ := fun s => (π s, f s) with hFm
  have hfd : ∀ s ∈ U, ContDiffAt ℝ (⊤ : ℕ∞) f s := fun s hs => hf.contDiffAt (hU.mem_nhds hs)
  have hFc : ∀ s ∈ U, ContDiffAt ℝ (⊤ : ℕ∞) Fm s := fun s hs =>
    π.contDiff.contDiffAt.prodMk (hfd s hs)
  have hFd : ∀ s ∈ U, HasStrictFDerivAt Fm (π.prod (fderiv ℝ f s)) s := fun s hs =>
    π.hasStrictFDerivAt.prodMk ((hfd s hs).hasStrictFDerivAt (by simp))
  obtain ⟨e₀, he₀⟩ := mkEquiv i j k hijk hik hjk (fderiv ℝ f p) hk
  have hF : HasStrictFDerivAt Fm
      (e₀ : EuclideanSpace ℝ (Fin 3) →L[ℝ] (ℝ × ℝ) × ℝ) p := by
    rw [he₀]; exact hFd p hpU
  set Ω := U ∩ (fun s => fderiv ℝ f s (EuclideanSpace.single k 1)) ⁻¹' {0}ᶜ with hΩdef
  have hΩ : IsOpen Ω := by
    have hc : ContinuousOn (fun s => fderiv ℝ f s (EuclideanSpace.single k 1)) U :=
      (hf.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const
    exact hc.isOpen_inter_preimage hU isOpen_compl_singleton
  set Φ := (hF.toOpenPartialHomeomorph Fm).restrOpen Ω hΩ with hΦdef
  have hΦsrc : Φ.source = (hF.toOpenPartialHomeomorph Fm).source ∩ Ω :=
    OpenPartialHomeomorph.restrOpen_source _ _ _
  have hΦcoe : ∀ s, Φ s = (π s, f s) := fun s => rfl
  have hpΩ : p ∈ Ω := ⟨hpU, hk⟩
  have hpsrc : p ∈ Φ.source := by
    rw [hΦsrc]; exact ⟨hF.mem_toOpenPartialHomeomorph_source, hpΩ⟩
  have hsrcΩ : ∀ s ∈ Φ.source, s ∈ Ω := fun s hs => by rw [hΦsrc] at hs; exact hs.2
  set U' : Set (ℝ × ℝ) := (fun z : ℝ × ℝ => (z, a)) ⁻¹' Φ.target with hU'def
  have hU' : IsOpen U' := Φ.open_target.preimage (continuous_id.prodMk continuous_const)
  set X : ℝ × ℝ → EuclideanSpace ℝ (Fin 3) := fun z => Φ.symm (z, a) with hXdef
  have hXsrc : ∀ z ∈ U', X z ∈ Φ.source := fun z hz => Φ.map_target hz
  have hΦX : ∀ z ∈ U', Φ (X z) = (z, a) := fun z hz => Φ.right_inv hz
  have hπX : ∀ z ∈ U', π (X z) = z ∧ f (X z) = a := by
    intro z hz
    have h1 := hΦX z hz
    rw [hΦcoe] at h1
    exact Prod.mk.inj h1
  have hXc : ∀ z ∈ U', ContDiffAt ℝ (⊤ : ℕ∞) X z := by
    intro z hz
    have hs := hXsrc z hz
    obtain ⟨hsU, hsk⟩ := hsrcΩ _ hs
    obtain ⟨e, he⟩ := mkEquiv i j k hijk hik hjk (fderiv ℝ f (X z)) hsk
    have hΦd : HasFDerivAt Φ (e : EuclideanSpace ℝ (Fin 3) →L[ℝ] (ℝ × ℝ) × ℝ)
        (Φ.symm (z, a)) := by
      rw [he]; exact (hFd _ hsU).hasFDerivAt
    have hsymm : ContDiffAt ℝ (⊤ : ℕ∞) Φ.symm (z, a) := Φ.contDiffAt_symm hz hΦd (hFc _ hsU)
    exact hsymm.comp z ((contDiff_id.prodMk contDiff_const).contDiffAt)
  refine ⟨Φ.source, U', X, Φ.open_source, hpsrc,
    ⟨hU', ?_, ?_, ?_, ⟨π, π.continuous.continuousOn, fun z hz => (hπX z hz).1⟩, ?_⟩, ?_⟩
  · intro z hz; exact (hXc z hz).contDiffWithinAt
  · intro z1 hz1 z2 hz2 h12
    rw [← (hπX z1 hz1).1, ← (hπX z2 hz2).1]
    exact congrArg π h12
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨(hsrcΩ _ (hXsrc z hz)).1, (hπX z hz).2⟩
  · intro z hz
    have hev : (fun z' => π (X z')) =ᶠ[𝓝 z] fun z' => z' := by
      filter_upwards [hU'.mem_nhds hz] with z' hz'
      exact (hπX z' hz').1
    have hd1 : HasFDerivAt (fun z' => π (X z')) (π.comp (fderiv ℝ X z)) z :=
      π.hasFDerivAt.comp z ((hXc z hz).differentiableAt (by simp)).hasFDerivAt
    have hd2 : HasFDerivAt (fun z' : ℝ × ℝ => z') (ContinuousLinearMap.id ℝ (ℝ × ℝ)) z :=
      hasFDerivAt_id z
    have heq : π.comp (fderiv ℝ X z) = ContinuousLinearMap.id ℝ (ℝ × ℝ) :=
      hd1.unique (hd2.congr_of_eventuallyEq hev)
    intro v1 v2 hv
    have h3 := congrArg π hv
    have e1 := congrArg (fun L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) => L v1) heq
    have e2 := congrArg (fun L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) => L v2) heq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at e1 e2
    rw [← e1, ← e2]; exact h3
  · ext s
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hXsrc z hz, (hsrcΩ _ (hXsrc z hz)).1, (hπX z hz).2⟩
    · rintro ⟨hs, _, hfs⟩
      refine ⟨π s, ?_, ?_⟩
      · have h1 := Φ.map_source hs
        rw [hΦcoe, hfs] at h1
        exact h1
      · have h1 := Φ.left_inv hs
        rw [hΦcoe, hfs] at h1
        exact h1

end PreimBuild

open DoCarmoDG in
theorem solution
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : IsOpen U)
    (f : EuclideanSpace ℝ (Fin 3) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (a : ℝ) (ha : a ∈ f '' U) (hreg : IsRegularValue U f a) :
    IsRegularSurface {p | p ∈ U ∧ f p = a} := by
  clear ha
  intro p hp
  obtain ⟨hpU, hfp⟩ := hp
  obtain ⟨k, hk⟩ := PreimBuild.exists_coord _ (hreg p hpU hfp)
  have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk3 with rfl | rfl | rfl
  · exact PreimBuild.local_param U hU f hf a p hpU 1 2 0 (by decide) (by decide) (by decide) hk
  · exact PreimBuild.local_param U hU f hf a p hpU 0 2 1 (by decide) (by decide) (by decide) hk
  · exact PreimBuild.local_param U hU f hf a p hpU 0 1 2 (by decide) (by decide) (by decide) hk
