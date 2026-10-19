-- Prove2me | solution 1 for FlatlyFoliated.theorem5_unique_elliptic_vacuum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T17:50:46.956479+00:00
-- url     : https://prove2.me/submissions/9f42b4af-ce64-4661-868c-0ef22e5fc131

import Theorems.Thm_FlatlyFoliated_theorem4_ellipticity
import Theorems.Thm_FlatlyFoliated_scalar_vacuum_rigidity

open scoped ContDiff Topology
open FlatlyFoliated Filter Set Metric

namespace EV

attribute [local instance] PiLp.normedAddCommGroup PiLp.normedSpace

private lemma smooth_pd {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (i : Fin 3) :
    ContDiff ℝ ∞ (pd i u) :=
  (hu.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

private lemma second_nonpos {f : ℝ → ℝ} {a : ℝ}
    (hf : ContinuousAt f a) (hm : IsLocalMax f a) : deriv (deriv f) a ≤ 0 := by
  by_contra hn
  have hp : 0 < deriv (deriv f) a := lt_of_not_ge hn
  have hl := isLocalMin_of_deriv_deriv_pos hp hm.deriv_eq_zero hf
  have he : f =ᶠ[𝓝 a] (fun _ => f a) := by
    filter_upwards [hm, hl] with x hx hy
    exact le_antisymm hx hy
  have hz : deriv (deriv f) a = 0 := by
    simpa only [deriv_const', deriv_const] using he.deriv.deriv_eq
  linarith

set_option backward.isDefEq.respectTransparency false in
private lemma line_deriv (x v : R3) (t : ℝ) :
    HasDerivAt (fun s : ℝ => x + s • v) v t := by
  have hs := (hasDerivAt_id t).smul_const v
  rw [one_smul] at hs
  exact hs.const_add x

private lemma pd_comm {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (i j : Fin 3) :
    pd i (pd j u) = pd j (pd i u) := by
  funext x
  have key : ∀ a b : Fin 3, pd a (pd b u) x =
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) := by
    intro a b
    unfold pd
    have hd := (hu.fderiv_right (m := ∞) le_rfl).differentiable (by simp) x
    rw [(hd.hasFDerivAt.clm_apply
      (hasFDerivAt_const (EuclideanSpace.single b (1 : ℝ)) x)).fderiv]
    simp
  rw [key, key]
  exact hu.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top) _ _

private lemma pd_add {u v : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (i : Fin 3) : pd i (fun x => u x + v x) = fun x => pd i u x + pd i v x := by
  funext x
  simp only [pd, fderiv_fun_add (hu.differentiable (by simp) x) (hv.differentiable (by simp) x),
    add_apply]

@[simp] private lemma pd_const (c : ℝ) (i : Fin 3) : pd i (fun _ : R3 => c) = 0 := by
  ext x
  simp [pd]

private lemma pd_mul_const {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (c : ℝ) (i : Fin 3) :
    pd i (fun x => c * u x) = fun x => c * pd i u x := by
  funext x
  unfold pd
  rw [((hasFDerivAt_const c x).fun_mul
    (hu.differentiable (by simp) x).hasFDerivAt).fderiv]
  simp

private lemma pd_exp (k : ℝ) (i : Fin 3) :
    pd i (fun x : R3 => Real.exp (k * x 0)) =
      fun x => (if i = 0 then k else 0) * Real.exp (k * x 0) := by
  funext x
  have he := (Real.hasDerivAt_exp (k * x 0)).comp_hasFDerivAt x
    ((hasFDerivAt_const k x).fun_mul (EuclideanSpace.proj (0 : Fin 3) : R3 →L[ℝ] ℝ).hasFDerivAt)
  change HasFDerivAt (fun y : R3 => Real.exp (k * y 0)) _ x at he
  rw [pd, he.fderiv]
  by_cases hi : i = 0
  · subst i
    simp
    ring
  · simp [hi, Ne.symm hi]

private lemma smooth_exp (k : ℝ) : ContDiff ℝ ∞ (fun x : R3 => Real.exp (k * x 0)) :=
  (contDiff_const.mul (EuclideanSpace.proj (0 : Fin 3) : R3 →L[ℝ] ℝ).contDiff).exp

private lemma hess_apply {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (x v : R3) :
    fderiv ℝ (fderiv ℝ u) x v v =
      ∑ i, ∑ j, pd j (pd i u) x * v i * v j := by
  have hp (i j : Fin 3) : pd j (pd i u) x =
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) := by
    unfold pd
    rw [(((hu.fderiv_right (m := ∞) le_rfl).differentiable (by simp) x).hasFDerivAt.clm_apply
      (hasFDerivAt_const (EuclideanSpace.single i (1 : ℝ)) x)).fderiv]
    simp
  have hv : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, sum_apply, smul_apply,
    smul_eq_mul, hp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hu.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top) (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)]
  ring

private lemma hess_nonpos {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u)
    {x : R3} (hm : IsLocalMax u x) (v : R3) :
    ∑ i, ∑ j, pd j (pd i u) x * v i * v j ≤ 0 := by
  let g : ℝ → ℝ := fun t => u (x + t • v)
  have hg : IsLocalMax g 0 := by
    have ht : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
      simpa using (line_deriv x v 0).continuousAt.tendsto
    change ∀ᶠ t in 𝓝 (0 : ℝ), u (x + t • v) ≤ u (x + (0 : ℝ) • v)
    simpa only [zero_smul, add_zero] using ht.eventually hm
  have hd : deriv g = fun t => fderiv ℝ u (x + t • v) v := by
    ext t
    exact ((hu.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
      (line_deriv x v t)).deriv
  have hdd : deriv (deriv g) 0 = fderiv ℝ (fderiv ℝ u) x v v := by
    rw [hd]
    have h := (((hu.fderiv_right (m := ∞) le_rfl).differentiable (by simp) (x + (0 : ℝ) • v)).hasFDerivAt.clm_apply
      (hasFDerivAt_const v (x + (0 : ℝ) • v))).comp_hasDerivAt 0 (line_deriv x v 0)
    simpa [Function.comp_def] using h.deriv
  rw [← hess_apply hu, ← hdd]
  exact second_nonpos (hu.continuous.continuousAt.comp (line_deriv x v 0).continuousAt) hg

private lemma operator_nonpos (A : Fin 3 → Fin 3 → ℝ)
    (hs : ∀ i j, A i j = A j i)
    (hp : ∀ v : R3, v ≠ 0 → 0 < ∑ i, ∑ j, A i j * v i * v j)
    {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) {x : R3} (hm : IsLocalMax u x) :
    ∑ i, ∑ j, A i j * pd j (pd i u) x ≤ 0 := by
  classical
  have hA : Matrix.PosSemidef A := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext i j
      change star (A j i) = A i j
      simpa using hs j i
    · intro v
      have hv : (WithLp.toLp 2 v : R3) = 0 ↔ v = 0 := by simp
      by_cases hz : v = 0
      · simp [hz]
      · have h := (hp (WithLp.toLp 2 v) (by simpa using hz)).le
        simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
          using h
  obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hA
  have he (i j : Fin 3) : A i j = ∑ k, v k i * v k j := by
    simpa only [Matrix.sum_apply, Matrix.vecMulVec_apply, star_trivial, Pi.star_apply] using congrFun (congrFun hv i) j
  simp_rw [he, Finset.sum_mul]
  simp_rw [Finset.sum_comm (f := fun j k => v k _ * v k j * pd j (pd _ u) x)]
  rw [Finset.sum_comm]
  apply Finset.sum_nonpos
  intro k _
  simpa [mul_assoc, mul_left_comm, mul_comm] using hess_nonpos hu hm (WithLp.toLp 2 (v k))

private lemma operator_exp (A : Fin 3 → Fin 3 → ℝ) (x : R3) :
    (∑ i, ∑ j, A i j * pd j (pd i (fun y : R3 => Real.exp (y 0))) x) =
      A 0 0 * Real.exp (x 0) := by
  have he : (fun y : R3 => Real.exp (y 0)) = (fun y => Real.exp (1 * y 0)) := by simp
  rw [he]
  simp only [pd_exp, pd_mul_const (smooth_exp 1)]
  simp [mul_ite, ite_mul]

private lemma elliptic_le_zero (A : Fin 3 → Fin 3 → R3 → ℝ)
    (hs : ∀ x i j, A i j x = A j i x)
    (hp : ∀ x (v : R3), v ≠ 0 → 0 < ∑ i, ∑ j, A i j x * v i * v j)
    (u : R3 → ℝ) (hu : ContDiff ℝ ∞ u)
    (heq : ∀ x, ∑ i, ∑ j, A i j x * pd j (pd i u) x = 0)
    (hinf : Tendsto u (Bornology.cobounded R3) (𝓝 0)) : ∀ x, u x ≤ 0 := by
  intro a
  by_contra hn
  have ha : 0 < u a := lt_of_not_ge hn
  let K : Set R3 := {x | u a / 2 ≤ u x}
  let U : Set R3 := {x | u a / 2 < u x}
  have haK : a ∈ K := by dsimp [K]; linarith
  have hK : IsCompact K := by
    apply isCompact_of_isClosed_isBounded (isClosed_le continuous_const hu.continuous)
    rw [Bornology.isBounded_def]
    change ∀ᶠ x in Bornology.cobounded R3, ¬ (u a / 2 ≤ u x)
    filter_upwards [hinf.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < u a / 2))]
      with x hx
    exact not_le.mpr hx
  obtain ⟨E₀, hE₀⟩ := hK.bddAbove_image (by simpa using (smooth_exp 1).continuous.continuousOn)
  let E : ℝ := max E₀ 1
  have hE : 0 < E := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hEb : ∀ x ∈ K, Real.exp (x 0) ≤ E := by
    intro x hx
    exact (hE₀ (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  let ε : ℝ := u a / (4 * E)
  have hε : 0 < ε := div_pos ha (mul_pos (by norm_num) hE)
  have hεE : ε * E = u a / 4 := by dsimp [ε]; field_simp
  let w : R3 → ℝ := fun x => u x + ε * Real.exp (x 0)
  have h_exp : ContDiff ℝ ∞ (fun x : R3 => Real.exp (x 0)) := by simpa using smooth_exp 1
  have hw : ContDiff ℝ ∞ w := hu.add (contDiff_const.mul h_exp)
  obtain ⟨x, _hxU, hmax⟩ := hK.exists_isLocalMax_mem_open
    (s := U) (by
      intro y hy
      change u a / 2 < u y at hy
      change u a / 2 ≤ u y
      exact hy.le) hw.continuous.continuousOn haK
    (fun y hy => by
      have hyu : u y ≤ u a / 2 := le_of_not_gt hy.2
      have hye : ε * Real.exp (y 0) ≤ u a / 4 := by
        rw [← hεE]
        exact mul_le_mul_of_nonneg_left (hEb y hy.1) hε.le
      dsimp [w]
      have hae := mul_pos hε (Real.exp_pos (a 0))
      linarith)
    (isOpen_lt continuous_const hu.continuous)
  have hdiag : 0 < A 0 0 x := by
    have h := hp x (EuclideanSpace.single 0 1) (by simp)
    simpa [Pi.single_apply, mul_ite, ite_mul] using h
  have hpert : (∑ i, ∑ j, A i j x * pd j (pd i w) x) =
      ε * A 0 0 x * Real.exp (x 0) := by
    simp only [w, pd_add hu (contDiff_const.mul h_exp), pd_mul_const h_exp ε,
      pd_add (smooth_pd hu _) (contDiff_const.mul (smooth_pd h_exp _)),
      pd_mul_const (smooth_pd h_exp _) ε]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [heq x]
    have he : (∑ i, ∑ j, A i j x * (ε * pd j (pd i (fun y : R3 => Real.exp (y 0))) x)) =
        ε * ∑ i, ∑ j, A i j x * pd j (pd i (fun y : R3 => Real.exp (y 0))) x := by
      simp only [Finset.mul_sum]; congr 1; ext i; congr 1; ext j; ring
    rw [he, operator_exp]
    ring
  have hnonpos := operator_nonpos (fun i j => A i j x) (hs x) (hp x) hw hmax
  rw [hpert] at hnonpos
  exact (mul_pos (mul_pos hε hdiag) (Real.exp_pos _)).not_ge hnonpos

private lemma elliptic_eq_const (A : Fin 3 → Fin 3 → R3 → ℝ)
    (hs : ∀ x i j, A i j x = A j i x)
    (hp : ∀ x (v : R3), v ≠ 0 → 0 < ∑ i, ∑ j, A i j x * v i * v j)
    (u : R3 → ℝ) (hu : ContDiff ℝ ∞ u) (c : ℝ)
    (heq : ∀ x, ∑ i, ∑ j, A i j x * pd j (pd i u) x = 0)
    (hinf : Tendsto u (Bornology.cobounded R3) (𝓝 c)) : u = fun _ => c := by
  have hd (k l : ℝ) (i : Fin 3) :
      pd i (fun x => k * u x + l) = fun x => k * pd i u x := by
    rw [pd_add (contDiff_const.mul hu) contDiff_const, pd_mul_const hu k, pd_const]
    simp
  have hdd (k l : ℝ) (i j : Fin 3) :
      pd j (pd i (fun x => k * u x + l)) = fun x => k * pd j (pd i u) x := by
    rw [hd, pd_mul_const (smooth_pd hu i)]
  have hb (k l : ℝ) (hkl : k * c + l = 0) : ∀ x, k * u x + l ≤ 0 := by
    apply elliptic_le_zero A hs hp (fun x => k * u x + l)
      ((contDiff_const.mul hu).add contDiff_const)
    · intro x
      simp only [hdd]
      have h : (∑ i, ∑ j, A i j x * (k * pd j (pd i u) x)) =
          k * ∑ i, ∑ j, A i j x * pd j (pd i u) x := by
        simp only [Finset.mul_sum]; congr 1; ext i; congr 1; ext j; ring
      rw [h, heq]; ring
    · convert ((tendsto_const_nhds (x := k)).mul hinf).add (tendsto_const_nhds (x := l)) using 1
      rw [hkl]
  ext x
  have h1 := hb 1 (-c) (by ring) x
  have h2 := hb (-1) c (by ring) x
  linarith
private lemma smooth_comp {w : R3 → R3} (hw : ContDiff ℝ ∞ w) (i : Fin 3) :
    ContDiff ℝ ∞ (FlatlyFoliated.comp w i) :=
  (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp hw

@[simp] private lemma pd_zero (i : Fin 3) : pd i (0 : R3 → ℝ) = 0 := by
  ext x
  simp [pd]

@[simp] private lemma comp_zero (i : Fin 3) : FlatlyFoliated.comp (0 : R3 → R3) i = 0 := rfl

@[simp] private lemma pd_comp_zero (i j : Fin 3) : pd j (FlatlyFoliated.comp (0 : R3 → R3) i) = 0 := by
  rw [comp_zero, pd_zero]

@[simp] private lemma lap_comp_zero (i : Fin 3) : lap (FlatlyFoliated.comp (0 : R3 → R3) i) = 0 := by
  ext x
  unfold lap
  simp only [pd_comp_zero, pd_zero, Pi.zero_apply, Finset.sum_const_zero]

@[simp] private lemma div_zero : divg (0 : R3 → R3) = 0 := by
  ext x
  simp only [divg, pd_comp_zero, Pi.zero_apply, Finset.sum_const_zero]

private lemma coeff_symm {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f)
    (z : R3 → R3) (x : R3) (i j : Fin 3) : ellCoeff f z i j x = ellCoeff f z j i x := by
  unfold ellCoeff Qmat
  rw [pd_comm hf i j]
  by_cases h : i = j
  · subst j; rfl
  · simp only [h, Ne.symm h, ite_false]; ring

private lemma vacuum_fields (Λ : ℝ) (hΛ : 0 < Λ) (f : R3 → ℝ) (z : R3 → R3) (η : R3 → ℝ)
    (hf : ContDiff ℝ ∞ f) (hz : ContDiff ℝ ∞ z) (hη : ContDiff ℝ ∞ η)
    (hηpos : ∀ x, 0 < η x) (hconv : ∀ x, 0 < lap f x / η x)
    (hsys : EllipticSystem Λ 0 0 f z η)
    (hzinf : Tendsto z (Bornology.cobounded R3) (𝓝 0))
    (hηinf : Tendsto η (Bornology.cobounded R3) (𝓝 1)) :
    η = (fun _ => 1) ∧ z = 0 := by
  have hp := (FlatlyFoliated.theorem4_ellipticity Λ hΛ 0 0 f z η
    contDiff_const contDiff_const hf hz hη (by simp) hηpos hconv hsys).1
  have heta := elliptic_eq_const (ellCoeff f z) (coeff_symm hf z) hp η hη 1 (by
    intro x
    have h := hsys.2.2.1 x
    have hz : (fun y => η y ^ 2 • (0 : R3 → R3) y) = 0 := by ext y i; simp
    rw [hz, div_zero] at h
    simpa only [Pi.zero_apply, mul_zero] using h) hηinf
  refine ⟨heta, ?_⟩
  have hηd : ∀ j, pd j η = 0 := by intro j; rw [heta, pd_const]
  have hzlap (i : Fin 3) (x : R3) : lap (FlatlyFoliated.comp z i) x = 0 := by
    simpa [hηd] using hsys.2.1 x i
  have hc (i : Fin 3) : FlatlyFoliated.comp z i = 0 := by
    apply elliptic_eq_const (fun i j _ => if i = j then 1 else 0)
      (by intro x i j; simp [eq_comm])
      (by
        intro x v hv
        simp only [ite_mul, one_mul, zero_mul]
        have h : 0 < ∑ i, v i ^ 2 := by
          apply Finset.sum_pos'
          · intro i _; positivity
          · obtain ⟨i, hi⟩ := Function.ne_iff.mp (show v.ofLp ≠ 0 by simpa using hv)
            exact ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
        simpa [pow_two] using h)
      (FlatlyFoliated.comp z i) (smooth_comp hz i) 0
      (by intro x; simpa [lap, mul_ite, ite_mul] using hzlap i x)
    have h := ((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).continuous.tendsto 0).comp hzinf
    change Tendsto (fun x => z x i) _ _
    exact h
  ext x i
  exact congrFun (hc i) x

private lemma smooth_quad (a : ℝ) : ContDiff ℝ ∞ (fun x : R3 => a * ‖x‖ ^ 2) :=
  contDiff_const.mul (contDiff_norm_sq ℝ)

private lemma pd_quad (a : ℝ) (i : Fin 3) :
    pd i (fun x : R3 => a * ‖x‖ ^ 2) = fun x => 2 * a * x i := by
  ext x
  have h := (hasFDerivAt_const a x).fun_mul (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  rw [pd, h.fderiv]
  simp [EuclideanSpace.inner_single_right]
  ring

private lemma pd_coord (a : ℝ) (i j : Fin 3) :
    pd j (fun x : R3 => a * x i) = fun _ => if i = j then a else 0 := by
  ext x
  have h := (hasFDerivAt_const a x).fun_mul
    (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).hasFDerivAt
  change HasFDerivAt (fun y : R3 => a * y i) _ x at h
  rw [pd, h.fderiv]
  by_cases hij : i = j
  · subst j; simp
  · simp [hij]

private lemma hess_quad (a : ℝ) (i j : Fin 3) :
    pd j (pd i (fun x : R3 => a * ‖x‖ ^ 2)) = fun _ => if i = j then 2 * a else 0 := by
  rw [pd_quad, pd_coord]

private lemma lap_quad (a : ℝ) : lap (fun x : R3 => a * ‖x‖ ^ 2) = fun _ => 6 * a := by
  ext x
  simp [lap, hess_quad]
  ring

private lemma average_quad (a : ℝ) : sphSymmetrization (fun x : R3 => a * ‖x‖ ^ 2) =
    (fun x : R3 => a * ‖x‖ ^ 2) := by
  ext x
  unfold sphSymmetrization
  have he (u : Metric.sphere (0 : R3) 1) : a * ‖‖x‖ • u.1‖ ^ 2 = a * ‖x‖ ^ 2 := by
    have hu : ‖u.1‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using u.2
    simp [norm_smul, hu]
  simp_rw [he]
  let : NeZero ((MeasureTheory.volume : MeasureTheory.Measure R3).toSphere) :=
    ⟨MeasureTheory.Measure.toSphere_ne_zero _⟩
  exact MeasureTheory.average_const _ _

private lemma approx_quad (a : ℝ) : ApproxSphSymmAtInfty (fun x : R3 => a * ‖x‖ ^ 2) := by
  constructor
  · refine ⟨0, ?_⟩; intro x; rw [average_quad]; simp
  · intro ε hε
    refine ⟨0, ?_⟩
    intro x _
    rw [average_quad]
    simp only [sub_self]
    have h0 : (fun y : R3 => (0 : ℝ)) = 0 := rfl
    rw [h0]
    simp
    exact hε.le

private lemma quad_solution (Λ : ℝ) (hΛ : 0 < Λ) :
    let q := fun x : R3 => Real.sqrt (Λ / 12) * ‖x‖ ^ 2
    ContDiff ℝ ∞ q ∧ (∀ x, 0 < lap q x) ∧ EllipticSystem Λ 0 0 q 0 (fun _ => 1) ∧
      ApproxSphSymmAtInfty q ∧
      Tendsto (0 : R3 → R3) (Bornology.cobounded R3) (𝓝 0) ∧
      Tendsto (fun _ : R3 => (1 : ℝ)) (Bornology.cobounded R3) (𝓝 1) := by
  dsimp only
  let a := Real.sqrt (Λ / 12)
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have ha2 : a ^ 2 = Λ / 12 := Real.sq_sqrt (by positivity)
  have hQ (i j : Fin 3) : Qmat (fun x : R3 => a * ‖x‖ ^ 2) 0 i j =
      fun _ => if i = j then 2 * a else 0 := by
    ext x
    simp only [Qmat, pd_comp_zero, Pi.zero_apply, mul_zero, add_zero, hess_quad]
  have hdiv : divg (0 : R3 → R3) = 0 := div_zero
  refine ⟨smooth_quad a, ?_, ?_, approx_quad a, tendsto_const_nhds, tendsto_const_nhds⟩
  · intro x; rw [lap_quad]; positivity
  · change EllipticSystem Λ 0 0 (fun x : R3 => a * ‖x‖ ^ 2) 0 (fun _ => 1)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x
      simp only [lap_quad, hQ, Pi.zero_apply, one_pow, mul_one]
      simp only [Fin.sum_univ_three]
      norm_num only [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
        show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide,
        show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
        ite_true, ite_false, zero_pow, add_zero, zero_add]
      nlinarith [ha2]
    · intro x i
      simp only [lap_comp_zero, Pi.zero_apply, pd_const, mul_zero, Finset.sum_const_zero, sub_zero]
      simp
    · intro x
      have he : (fun y : R3 => (1 : ℝ) ^ 2 • (0 : R3 → R3) y) = 0 := by ext y i; simp
      rw [he, div_zero]
      simp only [pd_const, pd_zero, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    · rw [hdiv]; exact tendsto_const_nhds

end EV

open EV

theorem solution (Λ : ℝ) (hΛ : 0 < Λ) :
    (ContDiff ℝ ∞ (fun x : R3 => Real.sqrt (Λ / 12) * ‖x‖ ^ 2) ∧
      (∀ x, 0 < lap (fun x : R3 => Real.sqrt (Λ / 12) * ‖x‖ ^ 2) x) ∧
      EllipticSystem Λ 0 0 (fun x : R3 => Real.sqrt (Λ / 12) * ‖x‖ ^ 2) 0 (fun _ => 1) ∧
      ApproxSphSymmAtInfty (fun x : R3 => Real.sqrt (Λ / 12) * ‖x‖ ^ 2) ∧
      Filter.Tendsto (0 : R3 → R3) (Bornology.cobounded R3) (nhds 0) ∧
      Filter.Tendsto (fun _ : R3 => (1 : ℝ)) (Bornology.cobounded R3) (nhds 1)) ∧
    ∀ (f : R3 → ℝ) (ζ : R3 → R3) (η : R3 → ℝ),
      ContDiff ℝ ∞ f → ContDiff ℝ ∞ ζ → ContDiff ℝ ∞ η → (∀ x, 0 < η x) →
      (∀ x, 0 < lap f x / η x) →
      EllipticSystem Λ 0 0 f ζ η → ApproxSphSymmAtInfty f →
      Filter.Tendsto ζ (Bornology.cobounded R3) (nhds 0) →
      Filter.Tendsto η (Bornology.cobounded R3) (nhds 1) →
      ∃ c : ℝ, (∀ x, f x = Real.sqrt (Λ / 12) * ‖x‖ ^ 2 + c) ∧ ζ = 0 ∧ η = fun _ => 1 := by
  refine ⟨quad_solution Λ hΛ, ?_⟩
  intro f z η hf hz hη hηpos hconv hsys happ hzinf hηinf
  obtain ⟨heta, hzero⟩ := vacuum_fields Λ hΛ f z η hf hz hη hηpos hconv hsys hzinf hηinf
  have hscalar : ∀ x, lap f x ^ 2 - hessNormSq f x = 2 * Λ := by
    intro x
    have h := hsys.1 x
    rw [heta, hzero] at h
    simpa only [Qmat, pd_comp_zero, Pi.zero_apply, zero_add, mul_zero, add_zero, one_pow, mul_one, hessNormSq] using h
  have hc : ∀ x, 0 < lap f x := by
    intro x
    have h := hconv x
    simpa [heta] using h
  obtain ⟨c, hc⟩ := FlatlyFoliated.scalar_vacuum_rigidity Λ hΛ f hf hc happ hscalar
  exact ⟨c, hc, hzero, heta⟩
