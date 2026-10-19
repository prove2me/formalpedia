-- Prove2me | solution 1 for FlatlyFoliated.lemma1_symmetrization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T18:17:45.619008+00:00
-- url     : https://prove2.me/submissions/f7d26b9c-0602-4795-81ee-60aea61d8626

import Theorems.Thm_FlatlyFoliated_spherical_hessian_barycenter

open scoped ContDiff Topology
open FlatlyFoliated MeasureTheory Filter Set

namespace FFRSymmetrization

set_option backward.isDefEq.respectTransparency false
attribute [local instance] PiLp.normedAddCommGroup PiLp.normedSpace

private abbrev H := EuclideanSpace ℝ (Fin 3 × Fin 3)
private abbrev J := ℝ × H
private noncomputable def hess (f : R3 → ℝ) (x : R3) : H :=
  WithLp.toLp 2 (fun ij => pd ij.2 (pd ij.1 f) x)

private lemma hess_norm (f : R3 → ℝ) (x : R3) : ‖hess f x‖ ^ 2 = hessNormSq f x := by
  simp [EuclideanSpace.real_norm_sq_eq, hess, hessNormSq, Fintype.sum_prod_type]

private noncomputable def lift (c : ℝ) (v : H) : EuclideanSpace ℝ (Option (Fin 3 × Fin 3)) :=
  WithLp.toLp 2 (fun i => i.elim c (fun j => v j))

private lemma lift_norm (c : ℝ) (v : H) : ‖lift c v‖ ^ 2 = c ^ 2 + ‖v‖ ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, lift, Fintype.sum_option]

private lemma lift_inner (c : ℝ) (v w : H) :
    inner ℝ (lift c v) (lift c w) = c ^ 2 + inner ℝ v w := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, lift, Fintype.sum_option, pow_two]

private lemma cone_support {a t s : ℝ} {v w : H}
    (ha : 0 < a) (ht : 0 < t) (hs : 0 < s)
    (hv : t ^ 2 = a + ‖v‖ ^ 2) (hw : s ^ 2 = a + ‖w‖ ^ 2) :
    a + inner ℝ v w ≤ t * s ∧
      (a + inner ℝ v w = t * s → w = v) := by
  let c := Real.sqrt a
  have hc : 0 < c := Real.sqrt_pos.2 ha
  have hc2 : c ^ 2 = a := Real.sq_sqrt ha.le
  have hn (u : H) (r : ℝ) (hr : 0 < r) (hu : r ^ 2 = a + ‖u‖ ^ 2) :
      ‖lift c u‖ = r := by
    have := lift_norm c u
    nlinarith [norm_nonneg (lift c u)]
  have hvn := hn v t ht hv
  have hwn := hn w s hs hw
  have hi := real_inner_le_norm (lift c v) (lift c w)
  rw [lift_inner, hc2, hvn, hwn] at hi
  refine ⟨hi, ?_⟩
  intro he
  have he' : inner ℝ (lift c v) (lift c w) = ‖lift c v‖ * ‖lift c w‖ := by
    simpa [lift_inner, hc2, hvn, hwn] using he
  have hh := inner_eq_norm_mul_iff_real.mp he'
  rw [hvn, hwn] at hh
  have hnone := congrArg (fun z => z none) hh
  have hts : s = t := by
    change s * c = t * c at hnone
    exact mul_right_cancel₀ hc.ne' hnone
  have hsome (i : Fin 3 × Fin 3) := congrArg (fun z => z (some i)) hh
  ext i
  have hh' := hsome i
  change s * v i = t * w i at hh'
  rw [hts] at hh'
  exact (mul_left_cancel₀ ht.ne' hh').symm

private lemma barycenter_cone (μ : Measure J) [IsProbabilityMeasure μ]
    (hf : Integrable (fun p : J => p.1) μ) (hh : Integrable (fun p : J => p.2) μ)
    {a : ℝ} (ha : 0 < a)
    (hc : ∀ᵐ p ∂μ, 0 < p.1 ∧ p.1 ^ 2 = a + ‖p.2‖ ^ 2) :
    let L := ∫ p : J, p.1 ∂μ
    let v := ∫ p : J, p.2 ∂μ
    0 < L ∧ a ≤ L ^ 2 - ‖v‖ ^ 2 ∧
      (a = L ^ 2 - ‖v‖ ^ 2 → ∀ p ∈ μ.support, p.2 = v) := by
  dsimp only
  let L := ∫ p : J, p.1 ∂μ
  let v := ∫ p : J, p.2 ∂μ
  let t := Real.sqrt (a + ‖v‖ ^ 2)
  have ht : 0 < t := Real.sqrt_pos.2 (by positivity)
  have ht2 : t ^ 2 = a + ‖v‖ ^ 2 := Real.sq_sqrt (by positivity)
  let g : J → ℝ := fun p => t * p.1 - (a + inner ℝ v p.2)
  have hi : Integrable (fun p : J => inner ℝ v p.2) μ :=
    (innerSL ℝ v).integrable_comp hh
  have hg : Integrable g μ := (hf.const_mul t).sub ((integrable_const a).add hi)
  have hnon : 0 ≤ᵐ[μ] g := by
    filter_upwards [hc] with p hp
    exact sub_nonneg.mpr (cone_support ha ht hp.1 ht2 hp.2).1
  have hgi : ∫ p, g p ∂μ = t * L - (a + ‖v‖ ^ 2) := by
    change (∫ p : J, t * p.1 - (a + inner ℝ v p.2) ∂μ) = _
    rw [integral_sub (f := fun p : J => t * p.1)
      (g := fun p : J => a + inner ℝ v p.2) (hf.const_mul t) ((integrable_const a).add hi),
      integral_add (f := fun _ : J => a) (g := fun p : J => inner ℝ v p.2)
        (integrable_const a) hi, integral_const_mul, integral_const]
    simp only [probReal_univ, one_smul]
    have he : ∫ p : J, inner ℝ v p.2 ∂μ = inner ℝ v v :=
      (innerSL ℝ v).integral_comp_comm hh
    rw [he, real_inner_self_eq_norm_sq]
  have hpos := integral_nonneg_of_ae hnon
  rw [hgi] at hpos
  have hLt : t ≤ L := by nlinarith
  refine ⟨ht.trans_le hLt, ?_, ?_⟩
  · nlinarith [sq_nonneg (L - t)]
  · intro he
    have hLt' : L = t := by nlinarith
    have hzero : ∫ p, g p ∂μ = 0 := by rw [hgi, hLt']; nlinarith
    have hae := (integral_eq_zero_iff_of_nonneg_ae hnon hg).mp hzero
    have hgc : Continuous g := by
      exact (continuous_const.mul continuous_fst).sub
        (continuous_const.add (continuous_const.inner continuous_snd))
    have hclosed : IsClosed {p | g p = 0} := isClosed_eq hgc continuous_const
    have hcontact := μ.support_subset_of_isClosed hclosed hae
    have hconeset : IsClosed {p : J | 0 ≤ p.1 ∧ p.1 ^ 2 = a + ‖p.2‖ ^ 2} :=
      (isClosed_le continuous_const continuous_fst).inter
        (isClosed_eq (continuous_fst.pow 2) (continuous_const.add (continuous_snd.norm.pow 2)))
    have hsupport := μ.support_subset_of_isClosed hconeset (hc.mono fun p hp => ⟨hp.1.le, hp.2⟩)
    intro p hp
    obtain ⟨hcp0, hcp2⟩ := hsupport hp
    have hsp : 0 < p.1 := by nlinarith [sq_nonneg ‖p.2‖]
    have hgp := hcontact hp
    apply (cone_support ha ht hsp ht2 hcp2).2
    dsimp [g] at hgp
    linarith

private lemma smooth_pd {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (i : Fin 3) :
    ContDiff ℝ ∞ (pd i u) :=
  (hu.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

private lemma clm_zero (D : R3 →L[ℝ] ℝ)
    (hD : ∀ i, D (EuclideanSpace.single i 1) = 0) : D = 0 := by
  have hx (x : R3) : x = ∑ i : Fin 3, x i • EuclideanSpace.single i 1 := by
    ext j
    simp [EuclideanSpace.single, Pi.single_apply]
  ext x
  rw [hx x]
  simp [map_sum, map_smul, hD]

private lemma bounded_zero_hessian {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u)
    (hH : ∀ x i j, pd j (pd i u) x = 0)
    (hb : ∃ C : ℝ, ∀ x, |u x| ≤ C) : ∀ x, u x = u 0 := by
  have hp (i : Fin 3) (x : R3) : pd i u x = pd i u 0 := by
    apply is_const_of_fderiv_eq_zero ((smooth_pd hu i).differentiable (by simp))
    intro z
    apply clm_zero
    intro j
    exact hH z i j
  let D := fderiv ℝ u 0
  have hd (x : R3) : fderiv ℝ u x = D := by
    have he : fderiv ℝ u x - D = 0 := by
      apply clm_zero
      intro i
      change pd i u x - pd i u 0 = 0
      exact sub_eq_zero.mpr (hp i x)
    exact sub_eq_zero.mp he
  have he : u = fun x => D x + u 0 := by
    refine eq_of_fderiv_eq (hu.differentiable (by simp))
      (D.differentiable.add_const (u 0)) ?_ (0 : R3) (by simp)
    intro x
    rw [hd, fderiv_add_const, D.fderiv]
  obtain ⟨C, hC⟩ := hb
  have hDz (x : R3) : D x = 0 := by
    by_contra hne
    let r := (C + |u 0| + 1) / D x
    have hr : r * D x = C + |u 0| + 1 := div_mul_cancel₀ _ hne
    have hh := hC (r • x)
    rw [he] at hh
    simp only [map_smul, smul_eq_mul] at hh
    rw [hr] at hh
    have hle := (le_abs_self _).trans hh
    linarith [neg_abs_le (u 0)]
  intro x
  simpa [hDz] using congrFun he x

private lemma average_zero (f : R3 → ℝ) : sphSymmetrization f 0 = f 0 := by
  unfold sphSymmetrization
  simp only [norm_zero, zero_smul]
  let : NeZero ((volume : Measure R3).toSphere) := ⟨Measure.toSphere_ne_zero _⟩
  exact average_const _ _

private lemma average_invariant (f : R3 → ℝ) : IsSphSymm (sphSymmetrization f) := by
  intro R x
  simp only [sphSymmetrization, R.norm_map]

private lemma symmetric_average {f : R3 → ℝ} (hs : IsSphSymm f) :
    sphSymmetrization f = f := by
  ext x
  unfold sphSymmetrization
  have he (u : Metric.sphere (0 : R3) 1) : f (‖x‖ • u.1) = f x := by
    have hu : ‖u.1‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using u.2
    have hn : ‖‖x‖ • u.1‖ = ‖x‖ := by simp [norm_smul, hu]
    let R := (Submodule.span ℝ {‖x‖ • u.1 - x})ᗮ.reflection
    have hR : R (‖x‖ • u.1) = x := Submodule.reflection_sub hn
    simpa only [hR] using (hs R (‖x‖ • u.1)).symm
  simp_rw [he]
  let : NeZero ((volume : Measure R3).toSphere) := ⟨Measure.toSphere_ne_zero _⟩
  exact average_const _ _

end FFRSymmetrization

open FFRSymmetrization

theorem solution (Λ : ℝ) (hΛ : 0 < Λ) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (hconv : ∀ x, 0 < lap f x) (happrox : ApproxSphSymmAtInfty f)
    (heq : ∀ x, lap f x ^ 2 - hessNormSq f x = 2 * Λ) :
    (∀ x, 2 * Λ ≤ lap (sphSymmetrization f) x ^ 2 - hessNormSq (sphSymmetrization f) x) ∧
    ((∀ x, lap (sphSymmetrization f) x ^ 2 - hessNormSq (sphSymmetrization f) x = 2 * Λ) ↔
      IsSphSymm f) := by
  obtain ⟨hbar, hav⟩ := spherical_hessian_barycenter f hf
  have hj (x : R3) :
      2 * Λ ≤ lap (sphSymmetrization f) x ^ 2 - hessNormSq (sphSymmetrization f) x ∧
      (lap (sphSymmetrization f) x ^ 2 - hessNormSq (sphSymmetrization f) x = 2 * Λ →
        hess f x = hess (sphSymmetrization f) x) := by
    obtain ⟨μ, hprob, hi, hH, hL, hA, hcone, hsupport⟩ := hav x
    have : IsProbabilityMeasure μ := hprob
    have hc : ∀ᵐ p ∂μ, 0 < p.1 ∧ p.1 ^ 2 = 2 * Λ + ‖p.2‖ ^ 2 := by
      filter_upwards [hcone] with p hp
      obtain ⟨y, _, hy, hn⟩ := hp
      rw [hy, hn]
      exact ⟨hconv y, by linarith [heq y]⟩
    have hh := barycenter_cone μ hi hH (by linarith : 0 < 2 * Λ) hc
    dsimp only at hh
    change (∫ p, p.2 ∂μ) = hess (sphSymmetrization f) x at hA
    rw [hL, hA, hess_norm] at hh
    exact ⟨hh.2.1, fun he => hh.2.2 he.symm _ hsupport⟩
  refine ⟨fun x => (hj x).1, ?_, ?_⟩
  · intro he
    have hh (x : R3) : hess f x = hess (sphSymmetrization f) x := (hj x).2 (he x)
    let u := fun x => f x - sphSymmetrization f x
    have hu : ContDiff ℝ ∞ u := hf.sub hbar
    have hHz : ∀ x i j, pd j (pd i u) x = 0 := by
      intro x i j
      have h := congrArg (fun A : H => A (i,j)) (hh x)
      simp only [hess, PiLp.toLp_apply] at h
      have he1 : pd i u = pd i f - pd i (sphSymmetrization f) := by
        funext z
        simp only [pd, u, fderiv_fun_sub (hf.differentiable (by simp) z)
          (hbar.differentiable (by simp) z), sub_apply, Pi.sub_apply]
      rw [he1]
      simp only [pd, fderiv_sub ((smooth_pd hf i).differentiable (by simp) x)
        ((smooth_pd hbar i).differentiable (by simp) x), sub_apply]
      exact sub_eq_zero.mpr h
    have hu0 : u 0 = 0 := by simp [u, FFRSymmetrization.average_zero]
    have huc := bounded_zero_hessian hu hHz happrox.1
    have hebar : f = sphSymmetrization f := by
      funext x
      have h := huc x
      rw [hu0] at h
      exact sub_eq_zero.mp h
    rw [hebar]
    exact average_invariant f
  · intro hs
    rw [symmetric_average hs]
    exact heq
