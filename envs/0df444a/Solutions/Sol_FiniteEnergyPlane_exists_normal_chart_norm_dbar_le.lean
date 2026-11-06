-- Prove2me | solution 1 for FiniteEnergyPlane.exists_normal_chart_norm_dbar_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-05T20:55:12.500071+00:00
-- url     : https://prove2.me/submissions/d1ffe704-3e8d-443d-b938-8a58e522508f

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open Metric Filter Topology
open scoped ContDiff

namespace FiniteEnergyPlane

section Linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The real-linear map `(a, b) ↦ D a + Re b • X + Im b • Y`. -/
noncomputable def nciN (D : ℂ →L[ℝ] E) (X Y : E) : ℂ × ℂ →L[ℝ] E :=
  D.comp (ContinuousLinearMap.fst ℝ ℂ ℂ) +
    (Complex.reCLM.smulRight X + Complex.imCLM.smulRight Y).comp (ContinuousLinearMap.snd ℝ ℂ ℂ)

lemma nciN_apply (D : ℂ →L[ℝ] E) (X Y : E) (q : ℂ × ℂ) :
    nciN D X Y q = D q.1 + q.2.re • X + q.2.im • Y := by
  simp [nciN, add_assoc]

lemma nci_map_I (J₀ : E →L[ℝ] E) (hJ2 : J₀.comp J₀ = -ContinuousLinearMap.id ℝ E) (D : ℂ →L[ℝ] E)
    (h : D 1 + J₀ (D Complex.I) = 0) (a : ℂ) : D (Complex.I * a) = J₀ (D a) := by
  have hJJ : ∀ x, J₀ (J₀ x) = -x := fun x => by
    have := congrArg (fun L => L x) hJ2
    simpa using this
  have h1 : J₀ (D 1) = D Complex.I := by
    have : D 1 = -J₀ (D Complex.I) := eq_neg_of_add_eq_zero_left h
    rw [this, map_neg, hJJ, neg_neg]
  have ha : ∀ b : ℂ, D b = b.re • D 1 + b.im • D Complex.I := fun b => by
    conv_lhs => rw [← Complex.re_add_im b]
    have : (b.re : ℂ) + (b.im : ℂ) * Complex.I = b.re • (1 : ℂ) + b.im • Complex.I := by
      simp [Complex.real_smul]
    rw [this, map_add, map_smul, map_smul]
  have h2 : J₀ (D Complex.I) = -D 1 := by rw [← h1, hJJ]
  rw [ha (Complex.I * a), ha a, map_add, map_smul, map_smul, h1, h2]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, Complex.mul_im,
    add_zero, zero_add, neg_smul, smul_neg]
  abel

lemma nciN_I (J₀ : E →L[ℝ] E) (hJ2 : J₀.comp J₀ = -ContinuousLinearMap.id ℝ E) (D : ℂ →L[ℝ] E)
    (h : D 1 + J₀ (D Complex.I) = 0) (X : E) (q : ℂ × ℂ) :
    nciN D X (J₀ X) (Complex.I • q) = J₀ (nciN D X (J₀ X) q) := by
  have hJJ : ∀ x, J₀ (J₀ x) = -x := fun x => by
    have := congrArg (fun L => L x) hJ2
    simpa using this
  rw [nciN_apply, nciN_apply, map_add, map_add, map_smul, map_smul, hJJ]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, nci_map_I J₀ hJ2 D h, Complex.mul_re,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, Complex.mul_im, add_zero, zero_add,
    neg_smul, smul_neg]
  abel

lemma nciN_injective (J₀ : E →L[ℝ] E) (hJ2 : J₀.comp J₀ = -ContinuousLinearMap.id ℝ E)
    (D : ℂ →L[ℝ] E) (h : D 1 + J₀ (D Complex.I) = 0) (hD : Function.Injective D) (X : E)
    (hX : X ∉ LinearMap.range (D : ℂ →ₗ[ℝ] E)) : Function.Injective (nciN D X (J₀ X)) := by
  have hJJ : ∀ x, J₀ (J₀ x) = -x := fun x => by
    have := congrArg (fun L => L x) hJ2
    simpa using this
  rw [injective_iff_map_eq_zero]
  rintro ⟨a, b⟩ hq
  rw [nciN_apply] at hq
  simp only at hq
  set n : E := b.re • X + b.im • J₀ X with hn
  have hna : n = D (-a) := by
    rw [map_neg]
    have : D a + n = 0 := by rw [hn, ← add_assoc]; exact hq
    exact eq_neg_of_add_eq_zero_right this
  have hJn : J₀ n = D (-(Complex.I * a)) := by
    rw [hna, map_neg, map_neg, map_neg, nci_map_I J₀ hJ2 D h]
  have hX2 : (b.re ^ 2 + b.im ^ 2) • X = b.re • n - b.im • J₀ n := by
    rw [hn, map_add, map_smul, map_smul, hJJ]
    module
  have hb0 : b.re ^ 2 + b.im ^ 2 = 0 := by
    by_contra hne
    apply hX
    have hmem : (b.re ^ 2 + b.im ^ 2) • X ∈ LinearMap.range (D : ℂ →ₗ[ℝ] E) := by
      rw [hX2, hJn, hna]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ ⟨_, rfl⟩) (Submodule.smul_mem _ _ ⟨_, rfl⟩)
    exact (Submodule.smul_mem_iff _ hne).1 hmem
  have hre : b.re = 0 := by nlinarith [sq_nonneg b.re, sq_nonneg b.im]
  have him : b.im = 0 := by nlinarith [sq_nonneg b.re, sq_nonneg b.im]
  have hb : b = 0 := Complex.ext hre him
  have haz : D a = 0 := by
    have := hq
    simpa [hre, him] using this
  have : a = 0 := hD (by rw [haz, map_zero])
  rw [this, hb]
  rfl

end Linear

theorem exists_normal_chart_norm_dbar_le_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hE : Module.finrank ℝ E = 4) (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (U W : Set ℂ) (hU : IsOpen U) (hW : IsOpen W)
    (u v : ℂ → E) (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v W)
    (huO : Set.MapsTo u U O) (hvO : Set.MapsTo v W O)
    (huh : JHolomorphic.IsJHolomorphicOn J U u) (hvh : JHolomorphic.IsJHolomorphicOn J W v)
    (z₀ w₀ : ℂ) (hz₀ : z₀ ∈ U) (hw₀ : w₀ ∈ W) (h₀ : u z₀ = v w₀)
    (hvi : Function.Injective (fderiv ℝ v w₀)) :
    ∃ (Ψ : ℂ × ℂ → E) (Ξ : E → ℂ × ℂ) (R M : ℝ), 0 < R ∧
      (∀ ζ, Ψ (ζ, 0) = v (w₀ + ζ)) ∧
      (∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)), Ξ (Ψ p) = p) ∧
      Ξ (u z₀) = (0, 0) ∧
      ContDiffOn ℝ ∞ (fun z => Ξ (u z)) (ball z₀ R) ∧
      ∀ z ∈ ball z₀ R, z ∈ U ∧ Ψ (Ξ (u z)) = u z ∧ w₀ + (Ξ (u z)).1 ∈ W ∧
        ‖fderiv ℝ (fun z => (Ξ (u z)).2) z 1 +
            Complex.I * fderiv ℝ (fun z => (Ξ (u z)).2) z Complex.I‖ ≤ M * ‖(Ξ (u z)).2‖ := by
  obtain ⟨hOo, hJs, hJ2⟩ := hJ
  have hw₀O : v w₀ ∈ O := hvO hw₀
  -- pick a normal direction
  have hrange : LinearMap.range ((fderiv ℝ v w₀ : ℂ →L[ℝ] E) : ℂ →ₗ[ℝ] E) ≠ ⊤ := by
    intro htop
    have h1 := LinearMap.finrank_range_of_inj (f := ((fderiv ℝ v w₀ : ℂ →L[ℝ] E) : ℂ →ₗ[ℝ] E)) hvi
    rw [htop, finrank_top, hE, Complex.finrank_real_complex] at h1
    norm_num at h1
  obtain ⟨X₀, hX₀⟩ := SetLike.exists_not_mem_of_ne_top _ hrange rfl
  set Ψ : ℂ × ℂ → E := fun p => v (w₀ + p.1) + p.2.re • X₀ + p.2.im • (J (v (w₀ + p.1)) X₀) with hΨdef
  have hvat : ∀ w ∈ W, ContDiffAt ℝ ∞ v w := fun w hw => hv.contDiffAt (hW.mem_nhds hw)
  have hJat : ∀ x ∈ O, ContDiffAt ℝ ∞ J x := fun x hx => hJs.contDiffAt (hOo.mem_nhds hx)
  have hshift : ∀ p : ℂ × ℂ, ContDiffAt ℝ ∞ (fun p : ℂ × ℂ => w₀ + p.1) p := fun p =>
    contDiffAt_const.add contDiffAt_fst
  have hVs : ∀ p : ℂ × ℂ, w₀ + p.1 ∈ W → ContDiffAt ℝ ∞ (fun p : ℂ × ℂ => v (w₀ + p.1)) p :=
    fun p hp => ContDiffAt.comp p (hvat _ hp) (hshift p)
  have hJVs : ∀ p : ℂ × ℂ, w₀ + p.1 ∈ W → ContDiffAt ℝ ∞ (fun p : ℂ × ℂ => J (v (w₀ + p.1))) p :=
    fun p hp => ContDiffAt.comp p (hJat _ (hvO hp)) (hVs p hp)
  have hreS : ∀ p : ℂ × ℂ, ContDiffAt ℝ ∞ (fun p : ℂ × ℂ => p.2.re) p := fun p =>
    (Complex.reCLM.contDiff.contDiffAt).comp p contDiffAt_snd
  have himS : ∀ p : ℂ × ℂ, ContDiffAt ℝ ∞ (fun p : ℂ × ℂ => p.2.im) p := fun p =>
    (Complex.imCLM.contDiff.contDiffAt).comp p contDiffAt_snd
  have hΨs : ∀ p : ℂ × ℂ, w₀ + p.1 ∈ W → ContDiffAt ℝ ∞ Ψ p := fun p hp =>
    ((hVs p hp).add ((hreS p).smul contDiffAt_const)).add
      ((himS p).smul ((hJVs p hp).clm_apply contDiffAt_const))
  have hΨd : ∀ ζ, w₀ + ζ ∈ W →
      HasFDerivAt Ψ (nciN (fderiv ℝ v (w₀ + ζ)) X₀ (J (v (w₀ + ζ)) X₀)) (ζ, (0 : ℂ)) := by
    intro ζ hζ
    have hvd : HasFDerivAt v (fderiv ℝ v (w₀ + ζ)) (w₀ + (ζ, (0 : ℂ)).1) :=
      ((hvat _ hζ).differentiableAt (by simp)).hasFDerivAt
    have hin : HasFDerivAt (fun p : ℂ × ℂ => w₀ + p.1) (ContinuousLinearMap.fst ℝ ℂ ℂ)
        (ζ, (0 : ℂ)) := hasFDerivAt_fst.const_add w₀
    have hV : HasFDerivAt (fun p : ℂ × ℂ => v (w₀ + p.1))
        ((fderiv ℝ v (w₀ + ζ)).comp (ContinuousLinearMap.fst ℝ ℂ ℂ)) (ζ, (0 : ℂ)) :=
      hvd.comp (ζ, (0 : ℂ)) hin
    have hre : HasFDerivAt (fun p : ℂ × ℂ => p.2.re • X₀)
        ((Complex.reCLM.smulRight X₀).comp (ContinuousLinearMap.snd ℝ ℂ ℂ)) (ζ, (0 : ℂ)) :=
      ((Complex.reCLM.smulRight X₀).comp (ContinuousLinearMap.snd ℝ ℂ ℂ)).hasFDerivAt
    have him : HasFDerivAt (fun p : ℂ × ℂ => p.2.im)
        (Complex.imCLM.comp (ContinuousLinearMap.snd ℝ ℂ ℂ)) (ζ, (0 : ℂ)) :=
      (Complex.imCLM.comp (ContinuousLinearMap.snd ℝ ℂ ℂ)).hasFDerivAt
    have hC : DifferentiableAt ℝ (fun p : ℂ × ℂ => J (v (w₀ + p.1)) X₀) (ζ, (0 : ℂ)) :=
      ((hJVs (ζ, (0 : ℂ)) hζ).clm_apply contDiffAt_const).differentiableAt (by simp)
    have hprod := him.smul hC.hasFDerivAt
    refine ((hV.add hre).add hprod).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun q => ?_
    rw [nciN_apply]
    simp
  have hJ₀ : ∀ w ∈ W, fderiv ℝ v w 1 + J (v w) (fderiv ℝ v w Complex.I) = 0 := fun w hw =>
    (hvh w hw).2
  have hNI : ∀ ζ, w₀ + ζ ∈ W → ∀ q : ℂ × ℂ,
      nciN (fderiv ℝ v (w₀ + ζ)) X₀ (J (v (w₀ + ζ)) X₀) (Complex.I • q) =
        J (v (w₀ + ζ)) (nciN (fderiv ℝ v (w₀ + ζ)) X₀ (J (v (w₀ + ζ)) X₀) q) := fun ζ hζ q =>
    nciN_I _ (hJ2 _ (hvO hζ)) _ (hJ₀ _ hζ) X₀ q
  have hw₀0 : w₀ + (0 : ℂ) ∈ W := by simpa using hw₀
  -- the invertible derivative at the origin
  have hLinj : Function.Injective (nciN (fderiv ℝ v (w₀ + 0)) X₀ (J (v (w₀ + 0)) X₀)) := by
    rw [add_zero]
    exact nciN_injective _ (hJ2 _ hw₀O) _ (hJ₀ _ hw₀) hvi X₀ hX₀
  have hfr : Module.finrank ℝ (ℂ × ℂ) = Module.finrank ℝ E := by
    rw [Module.finrank_prod, Complex.finrank_real_complex, hE]
  set L := nciN (fderiv ℝ v (w₀ + 0)) X₀ (J (v (w₀ + 0)) X₀) with hLdef
  set e : (ℂ × ℂ) ≃L[ℝ] E :=
    (LinearMap.linearEquivOfInjective (L : ℂ × ℂ →ₗ[ℝ] E) hLinj hfr).toContinuousLinearEquiv with hedef
  have heL : (e : ℂ × ℂ →L[ℝ] E) = L := by
    refine ContinuousLinearMap.ext fun q => ?_
    rfl
  have hΨ0 : w₀ + (0 : ℂ × ℂ).1 ∈ W := by simpa using hw₀
  have hd0 : HasFDerivAt Ψ (e : ℂ × ℂ →L[ℝ] E) (0 : ℂ × ℂ) := by
    rw [heL]
    exact hΨd 0 hw₀0
  have hs : HasStrictFDerivAt Ψ (e : ℂ × ℂ →L[ℝ] E) (0 : ℂ × ℂ) :=
    (hΨs 0 hΨ0).hasStrictFDerivAt' hd0 (by simp)
  set PH := hs.toOpenPartialHomeomorph Ψ with hPH
  have hPHc : ∀ p, PH p = Ψ p := fun _ => rfl
  have h0S : (0 : ℂ × ℂ) ∈ PH.source := hs.mem_toOpenPartialHomeomorph_source
  have hΨzero : Ψ 0 = u z₀ := by
    simp [hΨdef, h₀]
  have hx₀T : u z₀ ∈ PH.target := by
    rw [← hΨzero]
    exact PH.map_source h0S
  set Ξ : E → ℂ × ℂ := ⇑PH.symm with hΞdef
  have hΞ0 : Ξ (u z₀) = 0 := by
    rw [← hΨzero, ← hPHc]
    exact PH.left_inv h0S
  have hΞc : ContinuousAt Ξ (u z₀) := PH.continuousAt_symm hx₀T
  have hRI : ∀ x ∈ PH.target, Ψ (Ξ x) = x := fun x hx => PH.right_inv hx
  -- points where everything is invertible
  set Good : Set (ℂ × ℂ) := {p | p ∈ PH.source ∧ w₀ + p.1 ∈ W ∧
    ∃ e' : (ℂ × ℂ) ≃L[ℝ] E, fderiv ℝ Ψ p = (e' : ℂ × ℂ →L[ℝ] E)} with hGooddef
  have hGood : Good ∈ 𝓝 (0 : ℂ × ℂ) := by
    have h1 : PH.source ∈ 𝓝 (0 : ℂ × ℂ) := PH.open_source.mem_nhds h0S
    have h2 : {p : ℂ × ℂ | w₀ + p.1 ∈ W} ∈ 𝓝 (0 : ℂ × ℂ) :=
      ((continuous_const.add continuous_fst).isOpen_preimage W hW).mem_nhds hΨ0
    have h3 : ContinuousAt (fderiv ℝ Ψ) (0 : ℂ × ℂ) :=
      ((hΨs 0 hΨ0).fderiv_right (m := 0) (by simp)).continuousAt
    have h4 := h3.preimage_mem_nhds (by
      rw [hd0.fderiv]
      exact e.nhds)
    filter_upwards [h1, h2, h4] with p hp1 hp2 hp3
    obtain ⟨e', he'⟩ := hp3
    exact ⟨hp1, hp2, e', he'.symm⟩
  have hΞd : ∀ p ∈ Good, ∀ e' : (ℂ × ℂ) ≃L[ℝ] E, fderiv ℝ Ψ p = (e' : ℂ × ℂ →L[ℝ] E) →
      HasFDerivAt Ξ (e'.symm : E →L[ℝ] ℂ × ℂ) (Ψ p) ∧ ContDiffAt ℝ ∞ Ξ (Ψ p) := by
    intro p hp e' he'
    have hT : Ψ p ∈ PH.target := PH.map_source hp.1
    have hL : PH.symm (Ψ p) = p := PH.left_inv hp.1
    have hdiff : HasFDerivAt Ψ (e' : ℂ × ℂ →L[ℝ] E) p := by
      rw [← he']
      exact ((hΨs p hp.2.1).differentiableAt (by simp)).hasFDerivAt
    refine ⟨PH.hasFDerivAt_symm hT (by rw [hL]; exact hdiff), ?_⟩
    exact PH.contDiffAt_symm hT (f₀' := e') (by rw [hL]; exact hdiff)
      (by rw [hL]; exact hΨs p hp.2.1)
  obtain ⟨hΞd0, hΞs0⟩ := hΞd 0 (mem_of_mem_nhds hGood) e hd0.fderiv
  rw [hΨzero] at hΞd0 hΞs0
  -- the pulled back structure
  set C : ℂ × ℂ → (ℂ × ℂ →L[ℝ] ℂ × ℂ) := fun p =>
    (fderiv ℝ Ξ (Ψ p)).comp ((J (Ψ p)).comp (fderiv ℝ Ψ p)) with hCdef
  have hC1 : ContDiffAt ℝ 1 C (0 : ℂ × ℂ) := by
    have hΨ1 : ContDiffAt ℝ ∞ Ψ (0 : ℂ × ℂ) := hΨs 0 hΨ0
    have h1 : ContDiffAt ℝ 1 (fun p => fderiv ℝ Ξ (Ψ p)) (0 : ℂ × ℂ) := by
      have hh : ContDiffAt ℝ 1 (fderiv ℝ Ξ) (Ψ 0) := by
        rw [hΨzero]
        exact hΞs0.fderiv_right (m := 1) (by rw [one_add_one_eq_two]; exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
      exact hh.comp _ (hΨ1.of_le (by simp))
    have h2 : ContDiffAt ℝ 1 (fun p => J (Ψ p)) (0 : ℂ × ℂ) := by
      have hh : ContDiffAt ℝ 1 J (Ψ 0) := by
        rw [hΨzero, h₀]
        exact (hJat _ hw₀O).of_le (by simp)
      exact hh.comp _ (hΨ1.of_le (by simp))
    have h3 : ContDiffAt ℝ 1 (fderiv ℝ Ψ) (0 : ℂ × ℂ) :=
      hΨ1.fderiv_right (m := 1) (by rw [one_add_one_eq_two]; exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
    exact h1.clm_comp (h2.clm_comp h3)
  obtain ⟨K, t, ht, hLip⟩ := hC1.exists_lipschitzOnWith
  obtain ⟨τ, hτ, hτs⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem ht hGood)
  have hball : ∀ p ∈ ball (0 : ℂ × ℂ) τ, ((p.1, (0 : ℂ)) : ℂ × ℂ) ∈ ball (0 : ℂ × ℂ) τ := by
    intro p hp
    rw [mem_ball_zero_iff] at hp ⊢
    refine lt_of_le_of_lt ?_ hp
    rw [Prod.norm_def, Prod.norm_def]
    simp
  -- along the axis the structure is multiplication by `i`
  have hax : ∀ ζ, ((ζ, (0 : ℂ)) : ℂ × ℂ) ∈ ball (0 : ℂ × ℂ) τ → ∀ q : ℂ × ℂ,
      C (ζ, 0) q = Complex.I • q := by
    intro ζ hp q
    have hG := (hτs hp).2
    obtain ⟨-, hζW, e', he'⟩ := hG
    have hζW' : w₀ + ζ ∈ W := hζW
    have hder := (hΨd ζ hζW').fderiv
    obtain ⟨hΞe, -⟩ := hΞd _ (hτs hp).2 e' he'
    simp only [hCdef, ContinuousLinearMap.comp_apply]
    rw [hΞe.fderiv, he']
    have hval : Ψ (ζ, 0) = v (w₀ + ζ) := by simp [hΨdef]
    have hN := hNI ζ hζW' q
    rw [← hder, he'] at hN
    rw [hval, ← hN]
    simp
  -- the composite near `z₀`
  set G : ℂ → ℂ × ℂ := fun z => Ξ (u z) with hGdef
  have huat : ∀ z ∈ U, ContDiffAt ℝ ∞ u z := fun z hz => hu.contDiffAt (hU.mem_nhds hz)
  have hG0s : ContDiffAt ℝ ∞ G z₀ := hΞs0.comp z₀ (huat z₀ hz₀)
  have hGc : ContinuousAt G z₀ := hG0s.continuousAt
  have hG0 : G z₀ = 0 := hΞ0
  set B : ℝ := ‖fderiv ℝ G z₀ Complex.I‖ + 1 with hB
  have hBpos : 0 < B := by positivity
  have hdGc : ContinuousAt (fun z => ‖fderiv ℝ G z Complex.I‖) z₀ :=
    ((hG0s.fderiv_right (m := 0) (by simp)).continuousAt.clm_apply continuousAt_const).norm
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, 0 < ε := ⟨1, one_pos⟩
  have hE1 : ∀ᶠ z in 𝓝 z₀, z ∈ U := hU.mem_nhds hz₀
  have hE2 : ∀ᶠ z in 𝓝 z₀, u z ∈ PH.target :=
    (huat z₀ hz₀).continuousAt.preimage_mem_nhds (PH.open_target.mem_nhds hx₀T)
  have hE3 : ∀ᶠ z in 𝓝 z₀, G z ∈ ball (0 : ℂ × ℂ) (min τ ε) := by
    apply hGc.preimage_mem_nhds
    rw [hG0]
    exact ball_mem_nhds _ (lt_min hτ hε)
  have hE4 : ∀ᶠ z in 𝓝 z₀, ‖fderiv ℝ G z Complex.I‖ < B :=
    hdGc.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨r₁, hr₁, hr₁s⟩ := Metric.eventually_nhds_iff_ball.1 (hE1.and (hE2.and (hE3.and hE4)))
  set R := min r₁ ε with hRdef
  have hR : 0 < R := lt_min hr₁ hε
  have hRr : ball z₀ R ⊆ ball z₀ r₁ := ball_subset_ball (min_le_left _ _)
  have hRε : ball z₀ R ⊆ ball z₀ ε := ball_subset_ball (min_le_right _ _)
  have hbase : ∀ z ∈ ball z₀ R, z ∈ U ∧ u z ∈ PH.target ∧ G z ∈ ball (0 : ℂ × ℂ) τ ∧
      ‖G z‖ < ε ∧ ‖fderiv ℝ G z Complex.I‖ < B := by
    intro z hz
    obtain ⟨h1, h2, h3, h4⟩ := hr₁s z (hRr hz)
    refine ⟨h1, h2, ball_subset_ball (min_le_left _ _) h3, ?_, h4⟩
    have := mem_ball_zero_iff.1 (ball_subset_ball (min_le_right _ _) h3)
    exact this
  have hGval : ∀ z ∈ ball z₀ R, Ψ (G z) = u z := fun z hz => hRI _ (hbase z hz).2.1
  have hGdata : ∀ z ∈ ball z₀ R, ∃ e' : (ℂ × ℂ) ≃L[ℝ] E, fderiv ℝ Ψ (G z) = (e' : ℂ × ℂ →L[ℝ] E) ∧
      fderiv ℝ Ξ (u z) = (e'.symm : E →L[ℝ] ℂ × ℂ) ∧
      HasFDerivAt G ((e'.symm : E →L[ℝ] ℂ × ℂ).comp (fderiv ℝ u z)) z ∧ ContDiffAt ℝ ∞ G z := by
    intro z hz
    obtain ⟨hzU, hzT, hzτ, -, -⟩ := hbase z hz
    obtain ⟨-, -, e', he'⟩ := (hτs hzτ).2
    obtain ⟨h1, h2⟩ := hΞd _ (hτs hzτ).2 e' he'
    rw [hGval z hz] at h1 h2
    refine ⟨e', he', h1.fderiv, ?_, h2.comp z (huat z hzU)⟩
    exact h1.comp z ((huat z hzU).differentiableAt (by simp)).hasFDerivAt
  set g : ℂ → ℂ := fun z => (G z).2 with hgdef
  have hgs : ContDiffOn ℝ ∞ g (ball z₀ R) := fun z hz => by
    obtain ⟨e', -, -, -, h⟩ := hGdata z hz
    exact (contDiffAt_snd.comp z h).contDiffWithinAt
  have hbound : ∀ z ∈ ball z₀ R,
      ‖fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I‖ ≤ ((K : ℝ) * B) * ‖g z‖ := by
    intro z hz
    obtain ⟨e', he', hΞf, hGd, -⟩ := hGdata z hz
    obtain ⟨hzU, hzT, hzτ, -, hzB⟩ := hbase z hz
    have hgd : ∀ a, fderiv ℝ g z a = (fderiv ℝ G z a).2 := by
      intro a
      have : HasFDerivAt g ((ContinuousLinearMap.snd ℝ ℂ ℂ).comp (fderiv ℝ G z)) z :=
        (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp z hGd.differentiableAt.hasFDerivAt
      rw [this.fderiv]
      rfl
    set a := fderiv ℝ G z Complex.I with ha
    set p := G z with hp
    set p' : ℂ × ℂ := (p.1, 0) with hp'
    have hp'τ : p' ∈ ball (0 : ℂ × ℂ) τ := hball p hzτ
    have hax' := hax p.1 hp'τ a
    have hCp : C p a = -fderiv ℝ G z 1 := by
      have hh := (huh z hzU).2
      have hh' : fderiv ℝ u z 1 = -J (u z) (fderiv ℝ u z Complex.I) :=
        eq_neg_of_add_eq_zero_left hh
      have hΨp : Ψ p = u z := hGval z hz
      simp only [hCdef, ContinuousLinearMap.comp_apply, hΨp]
      rw [hΞf, he', ha, hGd.fderiv]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply]
      rw [hh', map_neg, neg_neg]
    have hkey : fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I = ((C p' - C p) a).2 := by
      rw [hgd, hgd, ContinuousLinearMap.sub_apply, hax', hCp]
      simp only [Prod.snd_sub, Prod.smul_snd, Prod.snd_neg, smul_eq_mul]
      ring
    rw [hkey]
    have h1 : ‖((C p' - C p) a).2‖ ≤ ‖(C p' - C p) a‖ := norm_snd_le _
    have h2 : ‖(C p' - C p) a‖ ≤ ‖C p' - C p‖ * ‖a‖ := (C p' - C p).le_opNorm a
    have h3 : ‖C p' - C p‖ ≤ K * ‖p' - p‖ := by
      have := hLip.dist_le_mul p' (hτs hp'τ).1 p (hτs hzτ).1
      simpa [dist_eq_norm] using this
    have h4 : ‖p' - p‖ = ‖g z‖ := by
      have : p' - p = (0, -p.2) := by
        ext <;> simp [hp']
      rw [this, Prod.norm_def]
      simp [hgdef, hp]
    rw [h4] at h3
    calc ‖((C p' - C p) a).2‖ ≤ ‖C p' - C p‖ * ‖a‖ := h1.trans h2
      _ ≤ ((K : ℝ) * ‖g z‖) * B := by
          exact mul_le_mul h3 hzB.le (norm_nonneg _) (by positivity)
      _ = ((K : ℝ) * B) * ‖g z‖ := by ring
  have hLI : ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)), Ξ (Ψ p) = p := by
    filter_upwards [PH.open_source.mem_nhds h0S] with p hp
    exact PH.left_inv hp
  refine ⟨Ψ, Ξ, R, (K : ℝ) * B, hR, fun ζ => by simp [hΨdef], hLI, hΞ0, ?_, ?_⟩
  · intro z hz
    obtain ⟨e', -, -, -, h⟩ := hGdata z hz
    exact h.contDiffWithinAt
  · intro z hz
    obtain ⟨hzU, -, hzτ, -, -⟩ := hbase z hz
    obtain ⟨-, hzW, -⟩ := (hτs hzτ).2
    exact ⟨hzU, hGval z hz, hzW, hbound z hz⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hE : Module.finrank ℝ E = 4) (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (U W : Set ℂ) (hU : IsOpen U) (hW : IsOpen W)
    (u v : ℂ → E) (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v W)
    (huO : Set.MapsTo u U O) (hvO : Set.MapsTo v W O)
    (huh : JHolomorphic.IsJHolomorphicOn J U u) (hvh : JHolomorphic.IsJHolomorphicOn J W v)
    (z₀ w₀ : ℂ) (hz₀ : z₀ ∈ U) (hw₀ : w₀ ∈ W) (h₀ : u z₀ = v w₀)
    (hvi : Function.Injective (fderiv ℝ v w₀)) :
    ∃ (Ψ : ℂ × ℂ → E) (Ξ : E → ℂ × ℂ) (R M : ℝ), 0 < R ∧
      (∀ ζ, Ψ (ζ, 0) = v (w₀ + ζ)) ∧
      (∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)), Ξ (Ψ p) = p) ∧
      Ξ (u z₀) = (0, 0) ∧
      ContDiffOn ℝ ∞ (fun z => Ξ (u z)) (ball z₀ R) ∧
      ∀ z ∈ ball z₀ R, z ∈ U ∧ Ψ (Ξ (u z)) = u z ∧ w₀ + (Ξ (u z)).1 ∈ W ∧
        ‖fderiv ℝ (fun z => (Ξ (u z)).2) z 1 +
            Complex.I * fderiv ℝ (fun z => (Ξ (u z)).2) z Complex.I‖ ≤ M * ‖(Ξ (u z)).2‖ :=
  exists_normal_chart_norm_dbar_le_aux hE J O hJ U W hU hW u v hu hv huO hvO huh hvh z₀ w₀ hz₀ hw₀ h₀ hvi
