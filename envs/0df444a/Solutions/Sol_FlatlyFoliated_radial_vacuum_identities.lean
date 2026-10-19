-- Prove2me | solution 1 for FlatlyFoliated.radial_vacuum_identities
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T17:36:58.502996+00:00
-- url     : https://prove2.me/submissions/78a233a0-a7b8-4621-a25e-47c61a0f3e94

import Definitions.Def_FlatlyFoliatedRelativity_basic

open scoped ContDiff Topology
open FlatlyFoliated Filter

namespace RadialVacuum

set_option backward.isDefEq.respectTransparency false

attribute [local instance] PiLp.normedAddCommGroup PiLp.normedSpace

private noncomputable abbrev axis (r : ℝ) : R3 := EuclideanSpace.single 0 r

private lemma axis_norm {r : ℝ} (hr : 0 ≤ r) : ‖axis r‖ = r := by
  simp [axis, Real.norm_eq_abs, abs_of_nonneg hr]

private lemma axis_deriv (r : ℝ) : HasDerivAt axis (axis 1) r := by
  have h := (hasDerivAt_id r).smul_const (axis 1)
  simp only [id_eq, one_smul] at h
  convert! h using 1
  ext s i
  simp [axis]

private lemma smooth_comp {w : R3 → R3} (hw : ContDiff ℝ ∞ w) (i : Fin 3) :
    ContDiff ℝ ∞ (comp w i) :=
  (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp hw

private lemma smooth_pd {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (i : Fin 3) :
    ContDiff ℝ ∞ (pd i u) :=
  (hu.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

private lemma profile_deriv {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (r : ℝ) :
    HasDerivAt (fun s => u (axis s)) (pd 0 u (axis r)) r :=
  (hu.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt r (axis_deriv r)

private lemma radial_repr {w : R3 → R3} {η : R3 → ℝ} {R : ℝ}
    (hs : ∀ (T : R3 ≃ₗᵢ[ℝ] R3) (x : R3), R ≤ ‖x‖ →
      η (T x) = η x ∧ w (T x) = T (w x))
    {x : R3} (hx : R ≤ ‖x‖) (hx0 : 0 < ‖x‖) :
    w x = (w (axis ‖x‖) 0 / ‖x‖) • x ∧ η x = η (axis ‖x‖) := by
  let y := axis ‖x‖
  have hy : ‖y‖ = ‖x‖ := axis_norm (norm_nonneg x)
  have hfix : (Submodule.span ℝ {y}).reflection y = y :=
    Submodule.reflection_mem_subspace_eq_self (Submodule.mem_span_singleton_self y)
  have hwy : (Submodule.span ℝ {y}).reflection (w y) = w y := by
    have h := (hs (Submodule.span ℝ {y}).reflection y (by simpa [hy] using hx)).2
    rw [hfix] at h
    exact h.symm
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    ((Submodule.reflection_eq_self_iff (w y)).mp hwy)
  have hc0 : c = w y 0 / ‖x‖ := by
    have h := congrArg (fun z : R3 => z 0) hc
    change c * ‖x‖ = w y 0 at h
    exact (eq_div_iff (ne_of_gt hx0)).mpr h
  let T := (Submodule.span ℝ {y - x})ᗮ.reflection
  have ht : T y = x := Submodule.reflection_sub hy
  have hh := hs T y (by simpa [hy] using hx)
  rw [ht] at hh
  constructor
  · calc
      w x = T (w y) := hh.2
      _ = T (c • y) := congrArg T hc.symm
      _ = c • x := by rw [map_smul, ht]
      _ = _ := by rw [hc0]
  · exact hh.1


private lemma norm_deriv {x : R3} (hx : 0 < ‖x‖) :
    HasFDerivAt (fun y : R3 => ‖y‖) ((‖x‖)⁻¹ • innerSL ℝ x) x := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 (ne_of_gt hx))
  simp only [Real.sqrt_sq (norm_nonneg _)] at h
  have he : (‖x‖)⁻¹ • innerSL ℝ x = (1 / (2 * ‖x‖)) • 2 • innerSL ℝ x := by
    ext v
    simp only [two_smul, add_apply, smul_apply, smul_eq_mul]
    field_simp
    ring
  rw [← he] at h
  exact h

private lemma inner_axis (x : R3) (j : Fin 3) :
    innerSL ℝ x (EuclideanSpace.single j 1) = x j := by
  simp [innerSL_apply_apply, EuclideanSpace.inner_single_right]

private lemma radial_pd {b : ℝ → ℝ} {u : R3 → ℝ} {x : R3} {j i : Fin 3}
    (hx : 0 < ‖x‖) (hb : DifferentiableAt ℝ b ‖x‖)
    (he : u =ᶠ[𝓝 x] (fun y => b ‖y‖ * y i)) :
    pd j u x = deriv b ‖x‖ * (x j / ‖x‖) * x i +
      b ‖x‖ * (if i = j then 1 else 0) := by
  have h := (hb.hasDerivAt.comp_hasFDerivAt x (norm_deriv hx)).fun_mul
    (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).hasFDerivAt
  change HasFDerivAt (fun y : R3 => b ‖y‖ * y i) _ x at h
  rw [pd, he.fderiv_eq, h.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, inner_axis, EuclideanSpace.proj,
    ]
  split_ifs <;> simp_all <;> ring

private lemma scalar_radial_pd {b : ℝ → ℝ} {u : R3 → ℝ} {x : R3} {j : Fin 3}
    (hx : 0 < ‖x‖) (hb : DifferentiableAt ℝ b ‖x‖)
    (he : u =ᶠ[𝓝 x] (fun y => b ‖y‖)) :
    pd j u x = deriv b ‖x‖ * (x j / ‖x‖) := by
  have h := hb.hasDerivAt.comp_hasFDerivAt x (norm_deriv hx)
  change HasFDerivAt (fun y : R3 => b ‖y‖) _ x at h
  rw [pd, he.fderiv_eq, h.fderiv]
  simp [inner_axis, div_eq_mul_inv, mul_comm, mul_left_comm]

private lemma exterior_pd {w : R3 → R3} {η : R3 → ℝ} {R : ℝ}
    (hw : ContDiff ℝ ∞ w) (hη : ContDiff ℝ ∞ η) (hR : 0 < R)
    (hs : ∀ (T : R3 ≃ₗᵢ[ℝ] R3) (x : R3), R ≤ ‖x‖ →
      η (T x) = η x ∧ w (T x) = T (w x))
    {x : R3} (hx : R < ‖x‖) :
    (∀ i j, pd j (comp w i) x =
      deriv (fun s => w (axis s) 0 / s) ‖x‖ * (x j / ‖x‖) * x i +
        (w (axis ‖x‖) 0 / ‖x‖) * (if i = j then 1 else 0)) ∧
    (∀ j, pd j η x = deriv (fun s => η (axis s)) ‖x‖ * (x j / ‖x‖)) := by
  have hx0 : 0 < ‖x‖ := lt_trans hR hx
  have hev : ∀ᶠ y in 𝓝 x, R < ‖y‖ := continuous_norm.continuousAt.preimage_mem_nhds
    (isOpen_Ioi.mem_nhds hx)
  have hwprofile := profile_deriv (smooth_comp hw 0) ‖x‖
  have hb : DifferentiableAt ℝ (fun s => w (axis s) 0 / s) ‖x‖ :=
    hwprofile.differentiableAt.div (differentiableAt_id) (ne_of_gt hx0)
  constructor
  · intro i j
    apply radial_pd hx0 hb
    filter_upwards [hev] with y hy
    have h := (radial_repr hs (le_of_lt hy) (lt_trans hR hy)).1
    exact congrArg (fun z : R3 => z i) h
  · intro j
    apply scalar_radial_pd hx0 (profile_deriv hη ‖x‖).differentiableAt
    filter_upwards [hev] with y hy
    exact (radial_repr hs (le_of_lt hy) (lt_trans hR hy)).2

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

private lemma pd_sum {u : Fin 3 → R3 → ℝ}
    (hu : ∀ j, ContDiff ℝ ∞ (u j)) (i : Fin 3) :
    pd i (fun x => ∑ j, u j x) = fun x => ∑ j, pd i (u j) x := by
  funext x
  unfold pd
  rw [(HasFDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => (hu j |>.differentiable (by simp) x).hasFDerivAt)).fderiv]
  simp

private lemma exterior_curl {w : R3 → R3} {η : R3 → ℝ} {R : ℝ}
    (hw : ContDiff ℝ ∞ w) (hη : ContDiff ℝ ∞ η) (hR : 0 < R)
    (hs : ∀ (T : R3 ≃ₗᵢ[ℝ] R3) (x : R3), R ≤ ‖x‖ →
      η (T x) = η x ∧ w (T x) = T (w x))
    {x : R3} (hx : R < ‖x‖) (i : Fin 3) :
    lap (comp w i) x = pd i (divg w) x := by
  have hsym : ∀ y, R < ‖y‖ → ∀ i j, pd j (comp w i) y = pd i (comp w j) y := by
    intro y hy i j
    rw [(exterior_pd hw hη hR hs hy).1 i j, (exterior_pd hw hη hR hs hy).1 j i]
    by_cases hij : i = j
    · subst j; ring
    · simp only [hij, Ne.symm hij, ↓reduceIte]
      ring
  have hev : ∀ᶠ y in 𝓝 x, R < ‖y‖ := continuous_norm.continuousAt.preimage_mem_nhds
    (isOpen_Ioi.mem_nhds hx)
  unfold divg
  rw [pd_sum (fun j => smooth_pd (smooth_comp hw j) j)]
  apply Finset.sum_congr rfl
  intro j _
  have he : pd j (comp w i) =ᶠ[𝓝 x] pd i (comp w j) := hev.mono (fun y hy => hsym y hy i j)
  change fderiv ℝ (pd j (comp w i)) x _ = _
  rw [he.fderiv_eq]
  change pd j (pd i (comp w j)) x = _
  rw [pd_comm (smooth_comp hw j) j i]


private lemma axis_pd {w : R3 → R3} {η : R3 → ℝ} {R r : ℝ}
    (hw : ContDiff ℝ ∞ w) (hη : ContDiff ℝ ∞ η) (hR : 0 < R)
    (hs : ∀ (T : R3 ≃ₗᵢ[ℝ] R3) (x : R3), R ≤ ‖x‖ →
      η (T x) = η x ∧ w (T x) = T (w x)) (hr : R < r) :
    (∀ i j, pd j (comp w i) (axis r) =
      if i = j then (if i = 0 then deriv (fun s => w (axis s) 0) r else w (axis r) 0 / r) else 0) ∧
    (∀ j, pd j η (axis r) = if j = 0 then deriv (fun s => η (axis s)) r else 0) := by
  have hr0 := lt_trans hR hr
  have hn := axis_norm (le_of_lt hr0)
  have h := exterior_pd hw hη hR hs (x := axis r) (by rwa [hn])
  constructor
  · intro i j
    fin_cases i <;> fin_cases j
    · exact (profile_deriv (smooth_comp hw 0) r).deriv.symm
    all_goals simp [h.1, hn, axis]
  · intro j
    fin_cases j
    · exact (profile_deriv hη r).deriv.symm
    all_goals simp [h.2, hn, axis]

private lemma vacuum_axis {w : R3 → R3} {η : R3 → ℝ} {Λ R r : ℝ}
    (hw : ContDiff ℝ ∞ w) (hη : ContDiff ℝ ∞ η) (hηpos : ∀ x, 0 < η x)
    (heq : FFREquations Λ 0 0 w η) (hR : 0 < R)
    (hs : ∀ (T : R3 ≃ₗᵢ[ℝ] R3) (x : R3), R ≤ ‖x‖ →
      η (T x) = η x ∧ w (T x) = T (w x)) (hr : R < r) :
    (w (axis r) 0)^2 + 2*r*w (axis r) 0*deriv (fun s => w (axis s) 0) r =
      Λ*r^2*(η (axis r))^2 ∧ w (axis r) 0 * deriv (fun s => η (axis s)) r = 0 := by
  have hr0 := lt_trans hR hr
  have hrn := ne_of_gt hr0
  have hen := ne_of_gt (hηpos (axis r))
  obtain ⟨hj, hg⟩ := axis_pd hw hη hR hs hr
  have hd : divg w (axis r) = deriv (fun s => w (axis s) 0) r + 2*(w (axis r) 0/r) := by
    simp [divg, Fin.sum_univ_three, hj]
    ring
  have hcurl := exterior_curl hw hη hR hs (x := axis r)
    (by rwa [axis_norm (le_of_lt hr0)]) 0
  have h34 := (heq (axis r)).1
  have h35 := (heq (axis r)).2 0
  simp only [Eq34, Pi.zero_apply, mul_zero, add_zero, hd] at h34
  simp only [Eq35, Pi.zero_apply, hcurl, sub_self, mul_zero, zero_add, hd] at h35
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  simp only [Fin.sum_univ_three, hj, hg] at h34 h35
  norm_num [h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12] at h34 h35
  constructor
  · field_simp [hrn, hen] at h34
    nlinarith [h34]
  · field_simp [hrn, hen] at h35
    rcases mul_eq_zero.mp (by nlinarith [h35] : r * (w (axis r) 0 * deriv (fun s => η (axis s)) r) = 0) with hz | hz
    · exact (hrn hz).elim
    · exact hz

end RadialVacuum

set_option backward.isDefEq.respectTransparency false in
open RadialVacuum in
theorem solution (Λ : ℝ) (w : R3 → R3) (η : R3 → ℝ)
    (hw : ContDiff ℝ ∞ w) (hη : ContDiff ℝ ∞ η) (hηpos : ∀ x, 0 < η x)
    (heq : FFREquations Λ 0 0 w η) (hsph : SphSymmAtInfty w η) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R < r →
      HasDerivAt (fun s : ℝ => s * (w (EuclideanSpace.single 0 s) 0) ^ 2)
        (Λ * r ^ 2 * (η (EuclideanSpace.single 0 r)) ^ 2) r ∧
      w (EuclideanSpace.single 0 r) 0 *
        deriv (fun s : ℝ => η (EuclideanSpace.single 0 s)) r = 0 := by
  obtain ⟨R, hR, hs⟩ := hsph
  refine ⟨R, hR, fun r hr => ?_⟩
  obtain ⟨he, hv⟩ := vacuum_axis hw hη hηpos heq hR hs hr
  constructor
  · have ha : HasDerivAt (fun s => w (axis s) 0) (deriv (fun s => w (axis s) 0) r) r :=
      (profile_deriv (smooth_comp hw 0) r).differentiableAt.hasDerivAt
    have h := (hasDerivAt_id r).mul (ha.pow 2)
    simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, one_mul] at h
    convert! h using 1
    nlinarith only [he]
  · exact hv
