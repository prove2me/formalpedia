-- Prove2me | solution 1 for FiniteEnergyPlane.exists_contDiffOn_curve_of_fderiv_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-09T22:29:36.168448+00:00
-- url     : https://prove2.me/submissions/d237787b-04ff-47dc-8a6d-c258c4cb97c9

import Mathlib



/-!
# Q-IFT: a smooth curve of zeros through a regular zero (proof of the sorry'd child in
`Scratch/JWQ_Stmts.lean`, under the namespace `FiniteEnergyPlane.QIFT`).
-/

namespace FiniteEnergyPlane.QIFT

open Metric Filter Topology
open scoped ContDiff

theorem exists_contDiffOn_curve_of_fderiv_surjective {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E → F) (ε : ℝ) (hε : 0 < ε) (hf : ContDiffOn ℝ ∞ f (ball 0 ε)) (hf0 : f 0 = 0)
    (hsurj : Function.Surjective (fderiv ℝ f 0))
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K] [FiniteDimensional ℝ K] (π₀ : E →ₗ[ℝ] K)
    (hker : ∀ x, fderiv ℝ f 0 x = 0 → π₀ x = 0 → x = 0)
    (k : E) (hk : fderiv ℝ f 0 k = 0) :
    ∃ r > 0, ∃ γ : ℝ → E, ContDiffOn ℝ ∞ γ (Set.Ioo (-r) r) ∧ γ 0 = 0 ∧ HasDerivAt γ k 0 ∧
      ∀ t ∈ Set.Ioo (-r) r, γ t ∈ ball 0 ε ∧ f (γ t) = 0 := by
  classical
  -- the kernel of `Df(0)` and a continuous projection onto it
  let Kr : Submodule ℝ E := LinearMap.ker (fderiv ℝ f 0 : E →ₗ[ℝ] F)
  have hmemK : ∀ x : E, x ∈ Kr ↔ fderiv ℝ f 0 x = 0 := fun x => LinearMap.mem_ker
  haveI : FiniteDimensional ℝ Kr := by
    refine Module.Finite.of_injective (π₀.comp Kr.subtype) ?_
    intro a b hab
    have h1 : fderiv ℝ f 0 ((a : E) - b) = 0 := by
      rw [map_sub, (hmemK a).1 a.2, (hmemK b).1 b.2, sub_zero]
    have h2 : π₀ ((a : E) - b) = 0 := by
      simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hab
      rw [map_sub, hab, sub_self]
    exact Subtype.ext (sub_eq_zero.1 (hker _ h1 h2))
  obtain ⟨P, hP⟩ := Submodule.ClosedComplemented.of_finiteDimensional Kr
  have hPx : ∀ x : E, ((P x : Kr) : E) ∈ Kr := fun x => (P x).2
  let gL : E →L[ℝ] F × Kr := (fderiv ℝ f 0).prod P
  have hinj : gL.ker = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 ?_
    intro x hx
    have h1 : fderiv ℝ f 0 x = 0 := congrArg Prod.fst hx
    have h2 : P x = 0 := congrArg Prod.snd hx
    have := hP ⟨x, (hmemK x).2 h1⟩
    rw [h2] at this
    exact (congrArg Subtype.val this).symm
  have hsurjL : gL.range = ⊤ := by
    refine LinearMap.range_eq_top.2 ?_
    rintro ⟨y, κ⟩
    obtain ⟨x₀, hx₀⟩ := hsurj y
    refine ⟨x₀ - (P x₀ : E) + κ, ?_⟩
    have hk1 : fderiv ℝ f 0 (P x₀ : E) = 0 := (hmemK _).1 (hPx x₀)
    have hk2 : fderiv ℝ f 0 (κ : E) = 0 := (hmemK _).1 κ.2
    refine Prod.ext ?_ ?_
    · show fderiv ℝ f 0 (x₀ - (P x₀ : E) + κ) = y
      rw [map_add, map_sub, hk1, hk2, hx₀, sub_zero, add_zero]
    · show P (x₀ - (P x₀ : E) + κ) = κ
      rw [map_add, map_sub, hP (P x₀), hP κ, sub_self, zero_add]
  let e : E ≃L[ℝ] F × Kr := ContinuousLinearEquiv.ofBijective gL hinj hsurjL
  have he : (e : E →L[ℝ] F × Kr) = gL := ContinuousLinearEquiv.coe_ofBijective _ _ _
  -- the map `g = (f, P)`
  let g : E → F × Kr := fun x => (f x, P x)
  have hgc : ContDiffOn ℝ ∞ g (ball 0 ε) := hf.prodMk P.contDiff.contDiffOn
  have hgd : ∀ x ∈ ball (0 : E) ε, HasFDerivAt g ((fderiv ℝ f x).prod P) x := by
    intro x hx
    have hdf : DifferentiableAt ℝ f x :=
      (hf.differentiableOn (by simp) x hx).differentiableAt (isOpen_ball.mem_nhds hx)
    exact hdf.hasFDerivAt.prodMk P.hasFDerivAt
  have h0ball : (0 : E) ∈ ball (0 : E) ε := mem_ball_self hε
  have hg0' : HasFDerivAt g (e : E →L[ℝ] F × Kr) 0 := by rw [he]; exact hgd 0 h0ball
  have hgcAt : ∀ x ∈ ball (0 : E) ε, ContDiffAt ℝ ∞ g x :=
    fun x hx => hgc.contDiffAt (isOpen_ball.mem_nhds hx)
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  let Φ := (hgcAt 0 h0ball).toOpenPartialHomeomorph g hg0' hn
  have hΦ : (Φ : E → F × Kr) = g := rfl
  have hsrc : (0 : E) ∈ Φ.source := (hgcAt 0 h0ball).mem_toOpenPartialHomeomorph_source hg0' hn
  have htgt : g 0 ∈ Φ.target := (hgcAt 0 h0ball).image_mem_toOpenPartialHomeomorph_target hg0' hn
  have hg00 : g 0 = (0, 0) := by simp [g, hf0]
  have hsymm0 : Φ.symm (g 0) = 0 := Φ.left_inv hsrc
  -- near `0`, `Dg` is invertible
  let U : Set E := {x | x ∈ ball (0 : E) ε ∧ ∃ e' : E ≃L[ℝ] F × Kr,
    fderiv ℝ g x = (e' : E →L[ℝ] F × Kr)}
  have hU : U ∈ 𝓝 (0 : E) := by
    have hcont : ContinuousAt (fderiv ℝ g) 0 :=
      (hgc.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)).continuousAt
        (isOpen_ball.mem_nhds h0ball)
    have hfd0 : fderiv ℝ g 0 = (e : E →L[ℝ] F × Kr) := hg0'.fderiv
    have hnhd := hcont.preimage_mem_nhds (by rw [hfd0]; exact ContinuousLinearEquiv.nhds e)
    filter_upwards [hnhd, isOpen_ball.mem_nhds h0ball] with x hx hxb
    obtain ⟨e', he'⟩ := hx
    exact ⟨hxb, e', he'.symm⟩
  let V : Set (F × Kr) := Φ.target ∩ Φ.symm ⁻¹' U
  have hV : V ∈ 𝓝 (g 0) := by
    refine Filter.inter_mem (Φ.open_target.mem_nhds htgt) ?_
    exact (Φ.continuousAt_symm htgt).preimage_mem_nhds (by rw [hsymm0]; exact hU)
  -- the curve
  let κ : Kr := ⟨k, (hmemK k).2 hk⟩
  let c : ℝ → F × Kr := fun t => ((0 : F), t • κ)
  have hc0 : c 0 = g 0 := by rw [hg00]; simp [c]
  have hcV : c ⁻¹' V ∈ 𝓝 (0 : ℝ) := by
    have hcc : Continuous c := continuous_const.prodMk (continuous_id.smul continuous_const)
    exact hcc.continuousAt.preimage_mem_nhds (by rw [hc0]; exact hV)
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hcV
  have hIoo : ∀ t ∈ Set.Ioo (-r) r, c t ∈ V := by
    intro t ht
    apply hrV
    rw [Real.ball_eq_Ioo]
    simpa using ht
  refine ⟨r, hr, fun t => Φ.symm (c t), ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨htg, hU'⟩ := hIoo t ht
    obtain ⟨hxb, e', he'⟩ := hU'
    have hd : HasFDerivAt Φ (e' : E →L[ℝ] F × Kr) (Φ.symm (c t)) := by
      rw [hΦ, ← he']
      exact (hgd _ hxb).differentiableAt.hasFDerivAt
    have hsymm : ContDiffAt ℝ ∞ Φ.symm (c t) := Φ.contDiffAt_symm htg hd (by rw [hΦ]; exact hgcAt _ hxb)
    have hcd : ContDiff ℝ ∞ c := contDiff_const.prodMk (contDiff_id.smul contDiff_const)
    exact (hsymm.comp t hcd.contDiffAt).contDiffWithinAt
  · show Φ.symm (c 0) = 0
    rw [hc0, hsymm0]
  · have hd : HasFDerivAt Φ (e : E →L[ℝ] F × Kr) (Φ.symm (c 0)) := by
      rw [hc0, hsymm0]; exact hg0'
    have hsym := Φ.hasFDerivAt_symm (by rw [hc0]; exact htgt) hd
    have hcd : HasDerivAt c ((0 : F), (1 : ℝ) • κ) 0 :=
      (hasDerivAt_const (0 : ℝ) (0 : F)).prodMk ((hasDerivAt_id (0 : ℝ)).smul_const κ)
    have h := hsym.comp_hasDerivAt (0 : ℝ) hcd
    have hek : e k = ((0 : F), (1 : ℝ) • κ) := by
      rw [one_smul]
      show (e : E →L[ℝ] F × Kr) k = _
      rw [he]
      exact Prod.ext hk (hP κ)
    have : (e.symm : F × Kr →L[ℝ] E) ((0 : F), (1 : ℝ) • κ) = k := by
      rw [← hek]; exact e.symm_apply_apply k
    rw [this] at h
    exact h
  · intro t ht
    obtain ⟨htg, hxb, -⟩ := hIoo t ht
    refine ⟨hxb, ?_⟩
    have h := Φ.right_inv htg
    rw [hΦ] at h
    exact congrArg Prod.fst h

end FiniteEnergyPlane.QIFT

open FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff

theorem solution {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E → F) (ε : ℝ) (hε : 0 < ε) (hf : ContDiffOn ℝ ∞ f (ball 0 ε)) (hf0 : f 0 = 0)
    (hsurj : Function.Surjective (fderiv ℝ f 0))
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K] [FiniteDimensional ℝ K] (π₀ : E →ₗ[ℝ] K)
    (hker : ∀ x, fderiv ℝ f 0 x = 0 → π₀ x = 0 → x = 0)
    (k : E) (hk : fderiv ℝ f 0 k = 0) :
    ∃ r > 0, ∃ γ : ℝ → E, ContDiffOn ℝ ∞ γ (Set.Ioo (-r) r) ∧ γ 0 = 0 ∧ HasDerivAt γ k 0 ∧
      ∀ t ∈ Set.Ioo (-r) r, γ t ∈ ball 0 ε ∧ f (γ t) = 0 :=
  FiniteEnergyPlane.QIFT.exists_contDiffOn_curve_of_fderiv_surjective f ε hε hf hf0 hsurj π₀ hker k hk
