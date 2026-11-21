-- Prove2me | solution 2 for BorsukUlam.exists_eq_neg
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T09:41:28.694288+00:00
-- url     : https://prove2.me/submissions/2be2b2cc-7b74-4ea6-9647-5e87e18364e2

import Mathlib
import Theorems.Thm_Tucker_exists_complementary_edge_cube

noncomputable section
open Classical

namespace BorsukUlam.PartBU

/-- A grid point of the cube `[-m,m]^n`. -/
def InBox {n : ℕ} (m : ℕ) (x : Fin n → ℤ) : Prop := ∀ i, |x i| ≤ m


/-! ## The map from the cube `[-1,1]^d` to the sphere -/

/-- The vector `(u, 1 - ‖u‖∞)`. -/
def rawVec {d : ℕ} (u : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  fun j => if h : (j : ℕ) < d then u ⟨j, h⟩ else 1 - ‖u‖

lemma rawVec_cont (d : ℕ) : Continuous (rawVec (d := d)) := by
  refine continuous_pi fun j => ?_
  by_cases h : (j : ℕ) < d
  · simp only [rawVec, h, dif_pos]
    exact continuous_apply _
  · simp only [rawVec, h, dif_neg, not_false_eq_true]
    exact continuous_const.sub continuous_norm

lemma rawVec_ne {d : ℕ} (u : Fin d → ℝ) : rawVec u ≠ 0 := by
  intro h
  have hu : u = 0 := by
    funext i
    have := congrFun h ⟨i, by omega⟩
    simpa [rawVec, i.isLt] using this
  have := congrFun h (Fin.last d)
  simp [rawVec, hu] at this

lemma rawVec_neg {d : ℕ} (u : Fin d → ℝ) (hu : ‖u‖ = 1) : rawVec (-u) = -rawVec u := by
  funext j
  by_cases h : (j : ℕ) < d
  · simp [rawVec, h]
  · simp [rawVec, h, hu]

/-- `(u, 1 - ‖u‖∞)` as a Euclidean vector. -/
def wVec {d : ℕ} (u : Fin d → ℝ) : EuclideanSpace ℝ (Fin (d + 1)) :=
  (EuclideanSpace.equiv (Fin (d + 1)) ℝ).symm (rawVec u)

lemma wVec_cont (d : ℕ) : Continuous (wVec (d := d)) :=
  (EuclideanSpace.equiv (Fin (d + 1)) ℝ).symm.continuous.comp (rawVec_cont d)

lemma wVec_ne {d : ℕ} (u : Fin d → ℝ) : wVec u ≠ 0 := by
  intro h
  apply rawVec_ne u
  have := congrArg (EuclideanSpace.equiv (Fin (d + 1)) ℝ) h
  simpa [wVec] using this

lemma wVec_neg {d : ℕ} (u : Fin d → ℝ) (hu : ‖u‖ = 1) : wVec (-u) = -wVec u := by
  simp [wVec, rawVec_neg u hu]

/-- The normalized vector, a point of the sphere. -/
def phi {d : ℕ} (u : Fin d → ℝ) : Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1 :=
  ⟨‖wVec u‖⁻¹ • wVec u, by
    simp [norm_smul, norm_ne_zero_iff.2 (wVec_ne u)]⟩

lemma phi_cont (d : ℕ) : Continuous (phi (d := d)) :=
  Continuous.subtype_mk (((wVec_cont d).norm.inv₀ fun u => norm_ne_zero_iff.2 (wVec_ne u)).smul
    (wVec_cont d)) _

lemma phi_neg {d : ℕ} (u : Fin d → ℝ) (hu : ‖u‖ = 1) : phi (-u) = -phi u := by
  apply Subtype.ext
  simp [phi, wVec_neg u hu]

/-! ## Labels -/

/-- Indices where `|v i| ≥ δ`. -/
def idxSet {d : ℕ} (δ : ℝ) (v : Fin d → ℝ) : Finset (Fin d) :=
  Finset.univ.filter fun i => δ ≤ |v i|

/-- The label: sign of `v i` times `i + 1`, for the least index `i` with `|v i| ≥ δ`. -/
def labOf {d : ℕ} (δ : ℝ) (v : Fin d → ℝ) : ℤ :=
  if h : (idxSet δ v).Nonempty then
    (if 0 < v ((idxSet δ v).min' h) then 1 else -1) * ((((idxSet δ v).min' h : ℕ) : ℤ) + 1)
  else 0

lemma idxSet_neg {d : ℕ} (δ : ℝ) (v : Fin d → ℝ) : idxSet δ (-v) = idxSet δ v := by
  ext i
  simp [idxSet, abs_neg]

lemma labOf_neg {d : ℕ} {δ : ℝ} (hδ : 0 < δ) (v : Fin d → ℝ) : labOf δ (-v) = -labOf δ v := by
  unfold labOf
  rw [idxSet_neg]
  by_cases h : (idxSet δ v).Nonempty
  · rw [dif_pos h, dif_pos h]
    have hi : δ ≤ |v ((idxSet δ v).min' h)| :=
      (Finset.mem_filter.1 (Finset.min'_mem _ h)).2
    have hne : v ((idxSet δ v).min' h) ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hi
      linarith
    simp only [Pi.neg_apply, neg_pos]
    split_ifs with h1 h2 h2
    · linarith
    · ring
    · ring
    · exact absurd (le_antisymm (not_lt.1 h2) (not_lt.1 h1)) hne
  · rw [dif_neg h, dif_neg h, neg_zero]

lemma labOf_spec {d : ℕ} {δ : ℝ} (v : Fin d → ℝ) (h : ∃ i, δ ≤ |v i|) :
    ∃ i : Fin d, labOf δ v = (if 0 < v i then 1 else -1) * (((i : ℕ) : ℤ) + 1) ∧
      δ ≤ |v i| := by
  have hne : (idxSet δ v).Nonempty := by
    obtain ⟨i, hi⟩ := h
    exact ⟨i, by simp [idxSet, hi]⟩
  refine ⟨(idxSet δ v).min' hne, ?_, (Finset.mem_filter.1 (Finset.min'_mem _ hne)).2⟩
  simp only [labOf, dif_pos hne]

/-! ## Borsuk–Ulam -/

theorem exists_eq_neg_dev (d : ℕ)
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1, EuclideanSpace ℝ (Fin d))) :
    ∃ x, f x = f (-x) := by
  by_contra hne
  push Not at hne
  set e := EuclideanSpace.equiv (Fin d) ℝ
  let G : (Fin d → ℝ) → (Fin d → ℝ) := fun u => e (f (phi u) - f (-phi u))
  have hG : Continuous G := e.continuous.comp
    ((f.continuous.comp (phi_cont d)).sub (f.continuous.comp (phi_cont d).neg))
  have hG0 : ∀ u, G u ≠ 0 := by
    intro u h
    apply hne (phi u)
    have : f (phi u) - f (-phi u) = 0 := by
      apply e.injective
      simpa [G] using h
    exact sub_eq_zero.1 this
  have hGneg : ∀ u : Fin d → ℝ, ‖u‖ = 1 → G (-u) = -G u := by
    intro u hu
    simp only [G, phi_neg u hu, neg_neg, ← map_neg, neg_sub]
  set K := Metric.closedBall (0 : Fin d → ℝ) 1
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨u0, _, hmin⟩ :=
    hK.exists_isMinOn ⟨0, by simp [K]⟩ (continuous_norm.comp hG).continuousOn
  set δ := ‖G u0‖
  have hδ : 0 < δ := norm_pos_iff.2 (hG0 u0)
  have hbig : ∀ u ∈ K, ∃ i, δ ≤ |G u i| := by
    intro u hu
    by_contra h
    push Not at h
    have h1 : ‖G u‖ < δ := (pi_norm_lt_iff hδ).2 (fun i => by
      simpa [Real.norm_eq_abs] using h i)
    have h2 : δ ≤ ‖G u‖ := hmin hu
    linarith
  obtain ⟨η, hη, hUC⟩ :=
    Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hG.continuousOn) δ hδ
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hη
  set m : ℕ := N + 1 with hm
  have hm0 : (0 : ℝ) < m := by positivity
  let U : (Fin d → ℤ) → (Fin d → ℝ) := fun x i => (x i : ℝ) / m
  have hUK : ∀ x : Fin d → ℤ, InBox m x → U x ∈ K := by
    intro x hx
    simp only [K, Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    have hxi : |(x i : ℝ)| ≤ m := by exact_mod_cast hx i
    simp only [U, Real.norm_eq_abs, abs_div, abs_of_pos hm0]
    exact (div_le_one hm0).2 hxi
  have hUneg : ∀ x : Fin d → ℤ, U (-x) = -U x := by
    intro x
    funext i
    simp [U, neg_div]
  have hUbd : ∀ x : Fin d → ℤ, InBox m x → (∃ a, |x a| = m) → ‖U x‖ = 1 := by
    intro x hx ⟨a, ha⟩
    refine le_antisymm ?_ ?_
    · simpa [K] using hUK x hx
    · have h1 := norm_le_pi_norm (U x) a
      have hxa : |(x a : ℝ)| = m := by exact_mod_cast ha
      have h2 : ‖U x a‖ = 1 := by
        simp only [U, Real.norm_eq_abs, abs_div, abs_of_pos hm0, hxa]
        exact div_self hm0.ne'
      linarith
  let lab : (Fin d → ℤ) → ℤ := fun x => labOf δ (G (U x))
  have hlab : ∀ x : Fin d → ℤ, InBox m x → lab x ≠ 0 ∧ |lab x| ≤ d := by
    intro x hx
    obtain ⟨i, hi, -⟩ := labOf_spec (G (U x)) (hbig _ (hUK x hx))
    have hid : (i : ℕ) + 1 ≤ d := i.isLt
    simp only [lab, hi]
    split_ifs
    · refine ⟨by omega, ?_⟩
      rw [one_mul, abs_of_nonneg (by omega)]
      exact_mod_cast hid
    · refine ⟨by omega, ?_⟩
      rw [neg_one_mul, abs_neg, abs_of_nonneg (by omega)]
      exact_mod_cast hid
  have hanti : ∀ x : Fin d → ℤ, InBox m x → (∃ a, |x a| = m) → lab (-x) = -lab x := by
    intro x hx hb
    simp only [lab, hUneg, hGneg _ (hUbd x hx hb), labOf_neg hδ]
  obtain ⟨x, y, hx, hy, -, -, hxy, hsum⟩ :=
    Tucker.exists_complementary_edge_cube d m (by omega) lab hlab hanti
  have hdist : dist (U x) (U y) < η := by
    have : dist (U x) (U y) ≤ 1 / m := by
      refine (dist_pi_le_iff (by positivity)).2 fun i => ?_
      have hxyi : |((x i : ℝ) - y i)| ≤ 1 := by exact_mod_cast hxy i
      simp only [U, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hm0]
      exact div_le_div_of_nonneg_right hxyi hm0.le
    have hN' : 1 / (m : ℝ) < η := by simpa [hm] using hN
    linarith
  have key : ∀ i, |G (U x) i - G (U y) i| < δ := by
    intro i
    have h1 := hUC (U x) (hUK x hx) (U y) (hUK y hy) hdist
    have h2 := dist_le_pi_dist (G (U x)) (G (U y)) i
    rw [Real.dist_eq] at h2
    linarith
  obtain ⟨i, hi, hix⟩ := labOf_spec (G (U x)) (hbig _ (hUK x hx))
  obtain ⟨j, hj, hjy⟩ := labOf_spec (G (U y)) (hbig _ (hUK y hy))
  simp only [lab, hi, hj] at hsum
  have hk := key i
  split_ifs at hsum with h1 h2 h2
  · omega
  · have hij : i = j := Fin.ext (by omega)
    subst hij
    rw [abs_of_pos h1] at hix
    rw [abs_of_nonpos (not_lt.1 h2)] at hjy
    rw [abs_lt] at hk
    linarith
  · have hij : i = j := Fin.ext (by omega)
    subst hij
    rw [abs_of_nonpos (not_lt.1 h1)] at hix
    rw [abs_of_pos h2] at hjy
    rw [abs_lt] at hk
    linarith
  · omega

end BorsukUlam.PartBU

theorem solution (d : ℕ)
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1, EuclideanSpace ℝ (Fin d))) :
    ∃ x, f x = f (-x) := by
  exact BorsukUlam.PartBU.exists_eq_neg_dev d f
