-- Prove2me | solution 1 for CosmoConstCentury.seeliger_modified_poisson_bounded_solution
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T12:17:34.171261+00:00
-- url     : https://prove2.me/submissions/f9664a6d-2e85-45fe-9696-faaa2226da76

import Mathlib
import Definitions.Def_CosmoConstCentury_Defs

open Filter Topology

namespace CCSeel215

open CosmoConstCentury

lemma oneD (g g' : ℝ → ℝ) (c : ℝ) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg' : HasDerivAt g' c 0) (hmax : IsLocalMax g 0) : c ≤ 0 := by
  by_contra hc
  push Not at hc
  set h : ℝ → ℝ := fun t => g t - (c / 4) * t ^ 2 with hh
  have hd : ∀ t, HasDerivAt h (g' t - (c / 2) * t) t := by
    intro t
    have := ((hg t).sub ((hasDerivAt_pow 2 t).const_mul (c / 4)) :
      HasDerivAt (fun x => g x - c / 4 * x ^ 2) _ t)
    refine this.congr_deriv ?_
    rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]; push_cast; ring
  have hderiv : deriv h = fun t => g' t - (c / 2) * t := funext fun t => (hd t).deriv
  have hd2 : HasDerivAt (fun t => g' t - (c / 2) * t) (c - c / 2) 0 := by
    have := (hg'.sub ((hasDerivAt_id (0:ℝ)).const_mul (c / 2)) :
      HasDerivAt (fun x => g' x - c / 2 * id x) _ 0)
    exact this.congr_deriv (by ring)
  have h1 : deriv (deriv h) 0 > 0 := by
    rw [hderiv, hd2.deriv]; linarith
  have h0 : deriv h 0 = 0 := by
    rw [hderiv]
    have := hmax.hasDerivAt_eq_zero (hg 0)
    simp [this]
  have hmin : IsLocalMin h 0 :=
    isLocalMin_of_deriv_deriv_pos h1 h0 (hd 0).continuousAt
  have hev := hmin.and hmax
  rcases Metric.eventually_nhds_iff.1 hev with ⟨δ, hδ, hball⟩
  have := hball (y := δ / 2) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  obtain ⟨hA, hB⟩ := this
  simp only [hh] at hA
  have : 0 < (c / 4) * (δ / 2) ^ 2 := by positivity
  simp at hA
  linarith

lemma dir (Φ : EuclideanSpace ℝ (Fin 3) → ℝ) (hΦ : ContDiff ℝ 2 Φ) (ε : ℝ)
    (x0 : EuclideanSpace ℝ (Fin 3))
    (hmax : ∀ y, Φ y - ε * ‖y‖ ^ 2 ≤ Φ x0 - ε * ‖x0‖ ^ 2) (i : Fin 3) :
    fderiv ℝ (fun y => fderiv ℝ Φ y (EuclideanSpace.single i 1)) x0
      (EuclideanSpace.single i 1) ≤ 2 * ε := by
  set v : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single i 1 with hv
  have hvv : inner ℝ v v = 1 := by simp [hv]
  have hD : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hD2 : Differentiable ℝ (fderiv ℝ Φ) :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hDv : Differentiable ℝ (fun y => fderiv ℝ Φ y v) :=
    fun y => (hD2 y).clm_apply (differentiableAt_const v)
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x0 + s • v) v t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const v).const_add x0
  let g : ℝ → ℝ := fun t => Φ (x0 + t • v) - ε * ‖x0 + t • v‖ ^ 2
  let g' : ℝ → ℝ := fun t => fderiv ℝ Φ (x0 + t • v) v - ε * (2 * inner ℝ (x0 + t • v) v)
  have hg : ∀ t, HasDerivAt g (g' t) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => Φ (x0 + s • v)) (fderiv ℝ Φ (x0 + t • v) v) t :=
      (hD _).hasFDerivAt.comp_hasDerivAt t (hline t)
    have h2 := ((hline t).norm_sq).const_mul ε
    exact h1.sub h2
  have hg' : HasDerivAt g' (fderiv ℝ (fun y => fderiv ℝ Φ y v) x0 v - ε * (2 * 1)) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ Φ (x0 + s • v) v)
        (fderiv ℝ (fun y => fderiv ℝ Φ y v) x0 v) 0 := by
      have := (hDv (x0 + (0:ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0:ℝ) (hline 0)
      simp only [zero_smul, add_zero] at this
      exact this
    have h2 : HasDerivAt (fun s : ℝ => inner ℝ (x0 + s • v) v) (inner ℝ v v) 0 := by
      have : (fun s : ℝ => inner ℝ (x0 + s • v) v) = fun s => inner ℝ x0 v + s * inner ℝ v v := by
        funext s; simp [inner_add_left, inner_smul_left]
      rw [this]
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const (inner ℝ v v)).const_add (inner ℝ x0 v)
    rw [hvv] at h2
    exact h1.sub ((h2.const_mul 2).const_mul ε)
  have hlm : IsLocalMax g 0 := by
    refine Filter.Eventually.of_forall fun t => ?_
    have := hmax (x0 + t • v)
    simpa [g] using this
  have := oneD g g' _ hg hg' hlm
  linarith

lemma key (Φ : EuclideanSpace ℝ (Fin 3) → ℝ) (hΦ : ContDiff ℝ 2 Φ) (M : ℝ)
    (hM : ∀ x, |Φ x| ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ x0, laplacian3 Φ x0 ≤ 6 * ε ∧ ∀ y, Φ y - ε * ‖y‖ ^ 2 ≤ Φ x0 - ε * ‖x0‖ ^ 2 := by
  have hcont : Continuous fun y : EuclideanSpace ℝ (Fin 3) => Φ y - ε * ‖y‖ ^ 2 :=
    (hΦ.continuous).sub (continuous_const.mul (continuous_norm.pow 2))
  set R : ℝ := 2 * |M| / ε + 1 with hR
  have hR1 : 1 ≤ R := by have : 0 ≤ 2 * |M| / ε := by positivity
                         linarith
  have hεR : 2 * M < ε * R ^ 2 := by
    have h1 : R ≤ R ^ 2 := by nlinarith
    have h2 : ε * R = 2 * |M| + ε := by rw [hR]; field_simp
    have h3 : M ≤ |M| := le_abs_self M
    nlinarith
  obtain ⟨x0, hx0, hmaxon⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) R).exists_isMaxOn
    ⟨0, Metric.mem_closedBall_self (by linarith)⟩ hcont.continuousOn
  have h0 : Φ 0 - ε * ‖(0 : EuclideanSpace ℝ (Fin 3))‖ ^ 2 ≤ Φ x0 - ε * ‖x0‖ ^ 2 :=
    hmaxon (Metric.mem_closedBall_self (by linarith))
  have hglob : ∀ y, Φ y - ε * ‖y‖ ^ 2 ≤ Φ x0 - ε * ‖x0‖ ^ 2 := by
    intro y
    by_cases hy : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R
    · exact hmaxon hy
    · simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hy
      have hy2 : R ^ 2 < ‖y‖ ^ 2 := by nlinarith
      have := hM y
      have := hM 0
      have ha := abs_le.1 (hM y)
      have hb := abs_le.1 (hM 0)
      simp at h0
      nlinarith
  refine ⟨x0, ?_, hglob⟩
  unfold laplacian3
  rw [Fin.sum_univ_three]
  have := dir Φ hΦ ε x0 hglob 0
  have := dir Φ hΦ ε x0 hglob 1
  have := dir Φ hΦ ε x0 hglob 2
  linarith

lemma lap_neg (Φ : EuclideanSpace ℝ (Fin 3) → ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    laplacian3 (fun y => -Φ y) x = -laplacian3 Φ x := by
  unfold laplacian3
  have : ∀ i : Fin 3, (fun y => fderiv ℝ (fun z => -Φ z) y (EuclideanSpace.single i 1)) =
      fun y => -(fderiv ℝ Φ y (EuclideanSpace.single i 1)) := by
    intro i; funext y; simp
  simp only [this]
  simp [Finset.sum_neg_distrib]

lemma lap_add_const (Φ : EuclideanSpace ℝ (Fin 3) → ℝ) (a : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    laplacian3 (fun y => Φ y + a) x = laplacian3 Φ x := by
  unfold laplacian3
  simp only [fderiv_add_const]

lemma lap_const (a : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    laplacian3 (fun _ => a) x = 0 := by
  unfold laplacian3
  simp

lemma nonpos (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (hψ : ContDiff ℝ 2 ψ) (M : ℝ)
    (hM : ∀ x, |ψ x| ≤ M) (lam : ℝ) (hlam : 0 < lam)
    (hL : ∀ x, laplacian3 ψ x = lam * ψ x) (y : EuclideanSpace ℝ (Fin 3)) : ψ y ≤ 0 := by
  by_contra hy
  push Not at hy
  set K : ℝ := ‖y‖ ^ 2 + 6 / lam with hK
  have hKpos : 0 < K := by positivity
  set ε : ℝ := ψ y / (2 * K) with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨x0, hlap, hglob⟩ := key ψ hψ M hM ε hεpos
  have h1 := hglob y
  rw [hL] at hlap
  have h2 : ψ x0 ≤ 6 * ε / lam := by rw [le_div_iff₀ hlam]; linarith
  have h3 : 0 ≤ ε * ‖x0‖ ^ 2 := by positivity
  have h4 : ε * K = ψ y / 2 := by rw [hε]; field_simp
  have h5 : ε * K = ε * ‖y‖ ^ 2 + 6 * ε / lam := by rw [hK]; ring
  linarith

end CCSeel215

open CosmoConstCentury in
theorem solution (G ρ lam : ℝ) (hlam : 0 < lam)
    (Φ : EuclideanSpace ℝ (Fin 3) → ℝ) (hΦ : ContDiff ℝ 2 Φ) (hbdd : ∃ M : ℝ, ∀ x, |Φ x| ≤ M) :
    (∀ x, laplacian3 Φ x - lam * Φ x = 4 * Real.pi * G * ρ) ↔
      ∀ x, Φ x = -(4 * Real.pi * G * ρ) / lam := by
  set k := 4 * Real.pi * G * ρ with hk
  obtain ⟨M, hM⟩ := hbdd
  constructor
  · intro hL x
    set ψ : EuclideanSpace ℝ (Fin 3) → ℝ := fun y => Φ y + k / lam with hψ
    have hψC : ContDiff ℝ 2 ψ := hΦ.add contDiff_const
    have hψM : ∀ x, |ψ x| ≤ M + |k / lam| := fun x =>
      (abs_add_le _ _).trans (by linarith [hM x])
    have hψL : ∀ x, laplacian3 ψ x = lam * ψ x := by
      intro x
      rw [hψ, CCSeel215.lap_add_const]
      have := hL x
      simp only
      field_simp
      linarith
    have h1 := CCSeel215.nonpos ψ hψC _ hψM lam hlam hψL x
    have h2 := CCSeel215.nonpos (fun y => -ψ y) hψC.neg _ (by simpa using hψM) lam hlam
      (fun x => by rw [CCSeel215.lap_neg, hψL]; ring) x
    have : ψ x = 0 := by linarith
    simp only [hψ] at this
    rw [neg_div]; linarith
  · intro hc x
    have : Φ = fun _ => -k / lam := funext hc
    rw [this, CCSeel215.lap_const]
    field_simp
    ring
