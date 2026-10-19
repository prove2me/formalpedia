-- Prove2me | solution 1 for FlatlyFoliated.decaying_drift_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T17:17:25.130526+00:00
-- url     : https://prove2.me/submissions/6de42a56-7444-4eff-baec-a261cabfc2a2

import Definitions.Def_FlatlyFoliatedRelativity_basic

open scoped ContDiff Topology
open FlatlyFoliated Filter Set Metric

namespace Drift

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

private lemma pd_line {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u)
    (x : R3) (i : Fin 3) (t : ℝ) :
    deriv (fun s : ℝ => u (x + s • EuclideanSpace.single i 1)) t =
      pd i u (x + t • EuclideanSpace.single i 1) := by
  exact ((hu.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
    (line_deriv x _ t)).deriv

private lemma lap_nonpos {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u)
    {x : R3} (hm : IsLocalMax u x) : lap u x ≤ 0 := by
  apply Finset.sum_nonpos
  intro i _
  let v : R3 := EuclideanSpace.single i 1
  have hl : IsLocalMax (fun t : ℝ => u (x + t • v)) 0 := by
    have ht : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
      simpa using (line_deriv x v 0).continuousAt.tendsto
    change ∀ᶠ t in 𝓝 (0 : ℝ), u (x + t • v) ≤ u (x + (0 : ℝ) • v)
    simpa only [zero_smul, add_zero] using ht.eventually hm
  have hd : deriv (deriv (fun t : ℝ => u (x + t • v))) 0 = pd i (pd i u) x := by
    have he : deriv (fun t : ℝ => u (x + t • v)) =
        (fun t => pd i u (x + t • v)) := funext (pd_line hu x i)
    rw [he]
    simpa [v] using pd_line (smooth_pd hu i) x i 0
  rw [← hd]
  exact second_nonpos (hu.continuous.continuousAt.comp
    (line_deriv x v 0).continuousAt) hl

private lemma pd_add {u v : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (i : Fin 3) : pd i (fun x => u x + v x) = fun x => pd i u x + pd i v x := by
  funext x
  simp only [pd, fderiv_fun_add (hu.differentiable (by simp) x) (hv.differentiable (by simp) x),
    add_apply]

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

private lemma lap_exp (k : ℝ) : lap (fun x : R3 => Real.exp (k * x 0)) =
    fun x => k ^ 2 * Real.exp (k * x 0) := by
  funext x
  simp only [lap, pd_exp, pd_mul_const (smooth_exp k)]
  simp
  ring

private lemma lap_add {u v : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    lap (fun x => u x + v x) = fun x => lap u x + lap v x := by
  funext x
  simp only [lap, pd_add hu hv]
  simp only [pd_add (smooth_pd hu _) (smooth_pd hv _), Finset.sum_add_distrib]

private lemma lap_mul_const {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (c : ℝ) :
    lap (fun x => c * u x) = fun x => c * lap u x := by
  funext x
  simp only [lap, pd_mul_const hu c]
  simp only [pd_mul_const (smooth_pd hu _) c, Finset.mul_sum]

private lemma perturbed_operator (η u : R3 → ℝ) (hu : ContDiff ℝ ∞ u)
    (heq : ∀ x, η x * lap u x = ∑ i, pd i η x * pd i u x) (k ε : ℝ) (x : R3) :
    η x * lap (fun y => u y + ε * Real.exp (k * y 0)) x -
      (∑ i, pd i η x * pd i (fun y => u y + ε * Real.exp (k * y 0)) x) =
      ε * k * Real.exp (k * x 0) * (η x * k - pd 0 η x) := by
  rw [lap_add hu (contDiff_const.mul (smooth_exp k)),
    lap_mul_const (smooth_exp k), lap_exp]
  simp only [pd_add hu (contDiff_const.mul (smooth_exp k)),
    pd_mul_const (smooth_exp k), pd_exp]
  have hh := heq x
  simp only [Fin.sum_univ_three] at hh ⊢
  simp only [ite_true, show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
    ite_false]
  nlinarith only [hh]

private lemma le_zero (η u : R3 → ℝ)
    (hη : ContDiff ℝ ∞ η) (hu : ContDiff ℝ ∞ u) (hηpos : ∀ x, 0 < η x)
    (heq : ∀ x, η x * lap u x = ∑ i, pd i η x * pd i u x)
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
  have hb : Continuous (fun x => pd 0 η x / η x) :=
    (smooth_pd hη 0).continuous.div hη.continuous (fun x => ne_of_gt (hηpos x))
  obtain ⟨B, hB⟩ := hK.bddAbove_image hb.continuousOn
  let k : ℝ := max B 0 + 1
  have hk : 0 < k := by dsimp [k]; linarith [le_max_right B 0]
  have hkb : ∀ x ∈ K, pd 0 η x / η x < k := by
    intro x hx
    have hxB : pd 0 η x / η x ≤ B := hB (mem_image_of_mem _ hx)
    dsimp [k]
    linarith [le_max_left B 0]
  obtain ⟨E₀, hE₀⟩ := hK.bddAbove_image (smooth_exp k).continuous.continuousOn
  let E : ℝ := max E₀ 1
  have hE : 0 < E := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hEb : ∀ x ∈ K, Real.exp (k * x 0) ≤ E := by
    intro x hx
    exact (hE₀ (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  let ε : ℝ := u a / (4 * E)
  have hε : 0 < ε := div_pos ha (mul_pos (by norm_num) hE)
  have hεE : ε * E = u a / 4 := by dsimp [ε]; field_simp
  let w : R3 → ℝ := fun x => u x + ε * Real.exp (k * x 0)
  have hw : ContDiff ℝ ∞ w := hu.add (contDiff_const.mul (smooth_exp k))
  obtain ⟨x, hxU, hmax⟩ := hK.exists_isLocalMax_mem_open
    (s := U) (by
      intro y hy
      change u a / 2 < u y at hy
      change u a / 2 ≤ u y
      exact hy.le) hw.continuous.continuousOn haK
    (fun y hy => by
      have hyu : u y ≤ u a / 2 := le_of_not_gt hy.2
      have hye : ε * Real.exp (k * y 0) ≤ u a / 4 := by
        rw [← hεE]
        exact mul_le_mul_of_nonneg_left (hEb y hy.1) hε.le
      dsimp [w]
      have hae := mul_pos hε (Real.exp_pos (k * a 0))
      linarith)
    (isOpen_lt continuous_const hu.continuous)
  have hxK : x ∈ K := (show u a / 2 ≤ u x from le_of_lt hxU)
  have hstrict : 0 < η x * lap w x - ∑ i, pd i η x * pd i w x := by
    rw [show w = (fun y => u y + ε * Real.exp (k * y 0)) from rfl,
      perturbed_operator η u hu heq]
    have hdiff : 0 < η x * k - pd 0 η x := by
      have hh := (div_lt_iff₀ (hηpos x)).mp (hkb x hxK)
      nlinarith
    exact mul_pos (mul_pos (mul_pos hε hk) (Real.exp_pos _)) hdiff
  have hgrad : ∀ i, pd i w x = 0 := by
    intro i
    simp [pd, hmax.fderiv_eq_zero]
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos (hηpos x).le (lap_nonpos hw hmax)
  simp only [hgrad, mul_zero, Finset.sum_const_zero, sub_zero] at hstrict
  exact hstrict.not_ge hnonpos

end Drift

theorem solution (η u : R3 → ℝ)
    (hη : ContDiff ℝ ∞ η) (hu : ContDiff ℝ ∞ u) (hηpos : ∀ x, 0 < η x)
    (heq : ∀ x, η x * lap u x = ∑ i, pd i η x * pd i u x)
    (hinf : Filter.Tendsto u (Bornology.cobounded R3) (nhds 0)) :
    ∀ x, u x = 0 := by
  have hn : ∀ x, (-u x) ≤ 0 := by
    apply Drift.le_zero η (fun x => -u x) hη hu.neg hηpos
    · intro x
      have hd : ∀ i, pd i (fun y => -u y) = fun y => -pd i u y := by
        intro i
        simpa using Drift.pd_mul_const hu (-1) i
      have hl : lap (fun y => -u y) = fun y => -lap u y := by
        simpa using Drift.lap_mul_const hu (-1)
      simp only [hl, hd, mul_neg, Finset.sum_neg_distrib]
      exact congrArg Neg.neg (heq x)
    · simpa using hinf.neg
  intro x
  exact le_antisymm (Drift.le_zero η u hη hu hηpos heq hinf x) (neg_nonpos.mp (hn x))
