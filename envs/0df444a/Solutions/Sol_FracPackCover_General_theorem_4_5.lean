-- Prove2me | solution 1 for FracPackCover.General.theorem_4_5
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-20T11:07:03.029856+00:00
-- url     : https://prove2.me/submissions/6e88a2f0-5a39-4c7b-a529-84e098f638b2

/-
SPDX-License-Identifier: Apache-2.0
Original standalone Lean proof of the complete GENERAL oracle decision algorithm.
Mathematical source: Plotkin, Shmoys, and Tardos, Fast Approximation Algorithms for
Fractional Packing and Covering Problems, Stanford STAN-CS-92-1419 (February 1992),
Section 4, Theorem 4.5. The mission-approved corrected Figure 4 constants 12 and 48
are retained exactly. All native definitions are imported unchanged.
The proof independently derives the exponential potential decrease and G1 certificate,
then proves both actual fuelled recursions with an inverse-square credit invariant.
All four native conclusions and the explicit 11520 call bound are proved.
No accepted implementation source is copied. All helper proofs are newly authored.
-/
import Mathlib
import Definitions.Def_FracPackCover_General_Driver

-- BEGIN Foundation
open scoped BigOperators
open Finset Set

namespace GeneralPackingProof
open FracPackCover.General
end GeneralPackingProof
-- END Foundation

-- BEGIN Residuals
namespace GeneralPackingProof

open FracPackCover.General
open scoped BigOperators

variable {m n : ℕ}

noncomputable def residual (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (x : Fin n → ℝ) (i : Fin m) : ℝ :=
  (FracPackCover.Covering.rowVal A x i - b i) / d i

noncomputable def weight (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (α : ℝ) (x : Fin n → ℝ) (i : Fin m) : ℝ := Real.exp (α * residual A b d x i)

lemma residual_abs_le (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    {P : Set (Fin n → ℝ)} (hd : ∀ i, 0 < d i) {ρ : ℝ}
    (hW : WidthBound A b d P ρ) {x : Fin n → ℝ} (hx : x ∈ P) (i : Fin m) :
    |residual A b d x i| ≤ ρ := by
  rw [residual, abs_div, abs_of_pos (hd i)]
  exact (div_le_iff₀ (hd i)).mpr (hW x hx i)

lemma residual_le_lam [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ)
    (b d : Fin m → ℝ) (x : Fin n → ℝ) (i : Fin m) :
    residual A b d x i ≤ lam A b d x := by
  exact Finset.le_sup' (fun j => residual A b d x j) (Finset.mem_univ i)

lemma exists_lam_eq_residual [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ)
    (b d : Fin m → ℝ) (x : Fin n → ℝ) :
    ∃ i, lam A b d x = residual A b d x i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i => residual A b d x i)
  exact ⟨i, hi⟩

lemma lam_le_width [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ)
    (b d : Fin m → ℝ) {P : Set (Fin n → ℝ)} (hd : ∀ i, 0 < d i) {ρ : ℝ}
    (hW : WidthBound A b d P ρ) {x : Fin n → ℝ} (hx : x ∈ P) :
    lam A b d x ≤ ρ := by
  obtain ⟨i, hi⟩ := exists_lam_eq_residual A b d x
  rw [hi]
  exact (le_abs_self _).trans (residual_abs_le A b d hd hW hx i)

lemma approx_of_lam_le [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ)
    (b d : Fin m → ℝ) (hd : ∀ i, 0 < d i) {x : Fin n → ℝ} {ε : ℝ}
    (h : lam A b d x ≤ ε) :
    ∀ i, FracPackCover.Covering.rowVal A x i ≤ b i + ε * d i := by
  intro i
  have hi := (div_le_iff₀ (hd i)).mp ((residual_le_lam A b d x i).trans h)
  linarith

lemma residual_affine (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (x z : Fin n → ℝ) (σ : ℝ) (i : Fin m) :
    residual A b d ((1 - σ) • x + σ • z) i =
      (1 - σ) * residual A b d x i + σ * residual A b d z i := by
  have hrow : FracPackCover.Covering.rowVal A ((1 - σ) • x + σ • z) i =
      (1 - σ) * FracPackCover.Covering.rowVal A x i +
        σ * FracPackCover.Covering.rowVal A z i := by
    simp only [FracPackCover.Covering.rowVal, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
  simp only [residual, hrow]
  ring

lemma potential_eq_sum_weight (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (α : ℝ) (x : Fin n → ℝ) : potential A b d α x = ∑ i, weight A b d α x i := by
  simp only [potential, weight, residual, mul_div_assoc]

lemma dual_mul_d (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (hd : ∀ i, 0 < d i) (α : ℝ) (x : Fin n → ℝ) (i : Fin m) :
    dualVec A b d α x i * d i = weight A b d α x i := by
  simp only [dualVec, weight, residual, mul_div_assoc]
  field_simp [ne_of_gt (hd i)]

lemma dual_nonneg (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (hd : ∀ i, 0 < d i) (α : ℝ) (x : Fin n → ℝ) :
    0 ≤ dualVec A b d α x := by
  intro i
  exact mul_nonneg (one_div_pos.mpr (hd i)).le (Real.exp_pos _).le

lemma dual_sum_eq_potential (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (hd : ∀ i, 0 < d i) (α : ℝ) (x : Fin n → ℝ) :
    (∑ i, dualVec A b d α x i * d i) = potential A b d α x := by
  simp only [dual_mul_d A b d hd, potential_eq_sum_weight]

lemma lagr_dual_eq (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (α : ℝ) (x z : Fin n → ℝ) :
    lagr A b (dualVec A b d α x) z = ∑ i, weight A b d α x i * residual A b d z i := by
  unfold lagr
  apply Finset.sum_congr rfl
  intro i _
  simp only [dualVec, weight, residual, mul_div_assoc]
  ring

lemma oracle_lagr_le (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    {P : Set (Fin n → ℝ)} {orc : (Fin m → ℝ) → (Fin n → ℝ)}
    (horc : IsMinOracle P A orc) {y : Fin m → ℝ} (hy : 0 ≤ y)
    {x : Fin n → ℝ} (hx : x ∈ P) : lagr A b y (orc y) ≤ lagr A b y x := by
  have h := (horc y hy).2 x hx
  simpa only [lagr, mul_sub, Finset.sum_sub_distrib, sub_le_sub_iff_right] using h

lemma step_mem (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    {P : Set (Fin n → ℝ)} (hP : Convex ℝ P) (hd : ∀ i, 0 < d i)
    {orc : (Fin m → ℝ) → (Fin n → ℝ)} (horc : IsMinOracle P A orc)
    (α : ℝ) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) {x : Fin n → ℝ} (hx : x ∈ P) :
    (1 - σ) • x + σ • orc (dualVec A b d α x) ∈ P := by
  exact hP hx ((horc _ (dual_nonneg A b d hd α x)).1)
    (sub_nonneg.mpr hσ1) hσ0 (by ring)

lemma potential_pos [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ)
    (b d : Fin m → ℝ) (α : ℝ) (x : Fin n → ℝ) : 0 < potential A b d α x := by
  rw [potential_eq_sum_weight]
  exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

lemma exp_lam_le_potential [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ)
    (b d : Fin m → ℝ) (α : ℝ) (x : Fin n → ℝ) :
    Real.exp (α * lam A b d x) ≤ potential A b d α x := by
  obtain ⟨i, hi⟩ := exists_lam_eq_residual A b d x
  rw [hi, potential_eq_sum_weight]
  exact Finset.single_le_sum (f := fun j => weight A b d α x j)
    (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)

lemma potential_le_exp_lam [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ)
    (b d : Fin m → ℝ) {α : ℝ} (hα : 0 ≤ α) (x : Fin n → ℝ) :
    potential A b d α x ≤ m * Real.exp (α * lam A b d x) := by
  rw [potential_eq_sum_weight]
  calc
    ∑ i, weight A b d α x i ≤ ∑ _i : Fin m, Real.exp (α * lam A b d x) :=
      Finset.sum_le_sum (fun i _ => Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (residual_le_lam A b d x i) hα))
    _ = _ := by simp

end GeneralPackingProof
-- END Residuals

-- BEGIN Parameters
namespace GeneralPackingProof

open FracPackCover.General

noncomputable def logScale (m : ℕ) (ρ t : ℝ) : ℝ := Real.log (12 * m * ρ / t)

noncomputable def decreaseRate (ρ t : ℝ) : ℝ := t ^ 2 / (2880 * ρ ^ 2)

noncomputable def initialBudget (m : ℕ) (ρ t : ℝ) : ℝ :=
  8640 * ρ ^ 2 / t ^ 2 * Real.log (12 * m * ρ / t)

lemma scale_ge_twelve {m : ℕ} [NeZero m] {ρ t : ℝ} (ht : 0 < t) (htr : t ≤ ρ) :
    (12 : ℝ) ≤ 12 * m * ρ / t := by
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast (NeZero.one_le : 1 ≤ m)
  apply (le_div_iff₀ ht).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hm) (show 0 ≤ ρ by linarith)]

lemma logScale_ge_one {m : ℕ} [NeZero m] {ρ t : ℝ} (ht : 0 < t) (htr : t ≤ ρ) :
    1 ≤ logScale m ρ t := by
  have hC := scale_ge_twelve (m := m) ht htr
  calc
    1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ logScale m ρ t := Real.log_le_log (Real.exp_pos 1)
      (Real.exp_one_lt_three.le.trans (by linarith))

lemma alpha_pos {m : ℕ} [NeZero m] {ρ t : ℝ} (ht : 0 < t) (htr : t ≤ ρ) :
    0 < alphaGen m ρ t := by
  exact mul_pos (div_pos (by norm_num) ht) (lt_of_lt_of_le (by norm_num) (logScale_ge_one ht htr))

lemma alpha_mul_start (m : ℕ) {ρ t : ℝ} (ht : 0 < t) :
    alphaGen m ρ t * t = 4 * logScale m ρ t := by
  unfold alphaGen logScale
  field_simp

lemma sigma_eq {m : ℕ} [NeZero m] {ρ t : ℝ} (ht : 0 < t) (htr : t ≤ ρ) :
    sigmaGen m ρ t = t ^ 2 / (192 * ρ ^ 2 * logScale m ρ t) := by
  have hρ : 0 < ρ := ht.trans_le htr
  have hl : 0 < logScale m ρ t := lt_of_lt_of_le (by norm_num) (logScale_ge_one ht htr)
  unfold sigmaGen alphaGen
  change t / (48 * (4 / t * logScale m ρ t) * ρ ^ 2) = _
  field_simp
  ring

lemma sigma_pos_le_one {m : ℕ} [NeZero m] {ρ t : ℝ} (ht : 0 < t) (htr : t ≤ ρ) :
    0 < sigmaGen m ρ t ∧ sigmaGen m ρ t ≤ 1 := by
  have hρ : 0 < ρ := ht.trans_le htr
  have hl := logScale_ge_one (m := m) ht htr
  have hlp : 0 < logScale m ρ t := by linarith
  rw [sigma_eq ht htr]
  constructor
  · positivity
  · apply (div_le_one (show 0 < 192 * ρ ^ 2 * logScale m ρ t by positivity)).mpr
    have hsq : t ^ 2 ≤ ρ ^ 2 := sq_le_sq₀ ht.le hρ.le |>.mpr htr
    nlinarith [mul_nonneg (sq_nonneg ρ) (sub_nonneg.mpr hl)]

lemma alpha_mul_sigma {m : ℕ} [NeZero m] {ρ t : ℝ} (ht : 0 < t) (htr : t ≤ ρ) :
    alphaGen m ρ t * sigmaGen m ρ t = t / (48 * ρ ^ 2) := by
  have ha := alpha_pos (m := m) ht htr
  have hρ : 0 < ρ := ht.trans_le htr
  unfold sigmaGen
  field_simp

lemma decreaseRate_pos_lt_one {ρ t : ℝ} (ht : 0 < t) (htr : t ≤ ρ) :
    0 < decreaseRate ρ t ∧ decreaseRate ρ t < 1 := by
  have hρ : 0 < ρ := ht.trans_le htr
  unfold decreaseRate
  constructor
  · positivity
  · apply (div_lt_one (show 0 < 2880 * ρ ^ 2 by positivity)).mpr
    have hsq : t ^ 2 ≤ ρ ^ 2 := sq_le_sq₀ ht.le hρ.le |>.mpr htr
    nlinarith [sq_pos_of_pos hρ]

lemma rate_identity {m : ℕ} [NeZero m] {ρ t : ℝ} (ht : 0 < t) (htr : t ≤ ρ) :
    alphaGen m ρ t * sigmaGen m ρ t * (t / 2) / 30 = decreaseRate ρ t := by
  rw [alpha_mul_sigma ht htr]
  unfold decreaseRate
  ring

lemma initialBudget_nonneg {m : ℕ} [NeZero m] {ρ t : ℝ} (ht : 0 < t) (htr : t ≤ ρ) :
    0 ≤ initialBudget m ρ t := by
  have hl := logScale_ge_one (m := m) ht htr
  unfold initialBudget
  change 0 ≤ 8640 * ρ ^ 2 / t ^ 2 * logScale m ρ t
  positivity

end GeneralPackingProof
-- END Parameters

-- BEGIN Potential
namespace GeneralPackingProof

open FracPackCover.General
open scoped BigOperators

lemma exp_quadratic (a z : ℝ) (hz : |z| ≤ 1) :
    Real.exp (a + z) ≤ Real.exp a + z * Real.exp a + z ^ 2 * Real.exp a := by
  have h := Real.norm_exp_sub_one_sub_id_le (show ‖z‖ ≤ 1 by simpa using hz)
  have he : Real.exp z - 1 - z ≤ z ^ 2 := (le_abs_self _).trans (by simpa using h)
  rw [Real.exp_add]
  nlinarith [mul_le_mul_of_nonneg_left he (Real.exp_pos a).le]

variable {m n : ℕ}

lemma potential_affine_bound (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    {P : Set (Fin n → ℝ)} (hd : ∀ i, 0 < d i) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hW : WidthBound A b d P ρ) {x z : Fin n → ℝ} (hx : x ∈ P) (hz : z ∈ P)
    {α σ : ℝ} (hα : 0 ≤ α) (hσ : 0 ≤ σ) (hsmall : 2 * α * σ * ρ ≤ 1) :
    potential A b d α ((1 - σ) • x + σ • z) ≤
      potential A b d α x + α * σ *
        (lagr A b (dualVec A b d α x) z - lagr A b (dualVec A b d α x) x) +
          4 * α ^ 2 * σ ^ 2 * ρ ^ 2 * potential A b d α x := by
  have hi (i : Fin m) :
      weight A b d α ((1 - σ) • x + σ • z) i ≤
        weight A b d α x i + α * σ *
          (weight A b d α x i * residual A b d z i -
            weight A b d α x i * residual A b d x i) +
          4 * α ^ 2 * σ ^ 2 * ρ ^ 2 * weight A b d α x i := by
    let Δ := α * σ * (residual A b d z i - residual A b d x i)
    have habs : |residual A b d z i - residual A b d x i| ≤ 2 * ρ := by
      have hxabs := residual_abs_le A b d hd hW hx i
      have hzabs := residual_abs_le A b d hd hW hz i
      exact (abs_sub _ _).trans (by linarith)
    have hΔ : |Δ| ≤ 2 * α * σ * ρ := by
      dsimp [Δ]
      rw [abs_mul, abs_of_nonneg (mul_nonneg hα hσ)]
      nlinarith [mul_le_mul_of_nonneg_left habs (mul_nonneg hα hσ)]
    have hsquare : Δ ^ 2 ≤ 4 * α ^ 2 * σ ^ 2 * ρ ^ 2 := by
      have hh := sq_le_sq₀ (abs_nonneg Δ) (by positivity : 0 ≤ 2 * α * σ * ρ) |>.mpr hΔ
      nlinarith [sq_abs Δ]
    have he := exp_quadratic (α * residual A b d x i) Δ (hΔ.trans hsmall)
    have haff : α * residual A b d ((1 - σ) • x + σ • z) i =
        α * residual A b d x i + Δ := by rw [residual_affine]; dsimp [Δ]; ring
    unfold weight
    rw [haff]
    have hw := Real.exp_pos (α * residual A b d x i)
    have hmul := mul_le_mul_of_nonneg_right hsquare hw.le
    dsimp [Δ] at he hmul ⊢
    nlinarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    ← lagr_dual_eq, ← potential_eq_sum_weight] using hsum

lemma potential_decrease [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    {P : Set (Fin n → ℝ)} (hd : ∀ i, 0 < d i) {ρ t : ℝ}
    (ht : 0 < t) (htr : t ≤ ρ) (hW : WidthBound A b d P ρ)
    {orc : (Fin m → ℝ) → (Fin n → ℝ)} (horc : IsMinOracle P A orc)
    {x : Fin n → ℝ} (hx : x ∈ P) (hlive : t / 2 ≤ lam A b d x)
    (hfail : ¬ G2 A b d x (lam A b d x) (dualVec A b d (alphaGen m ρ t) x)
      (lagr A b (dualVec A b d (alphaGen m ρ t) x)
        (orc (dualVec A b d (alphaGen m ρ t) x)))) :
    potential A b d (alphaGen m ρ t)
      ((1 - sigmaGen m ρ t) • x + sigmaGen m ρ t • orc (dualVec A b d (alphaGen m ρ t) x)) ≤
        (1 - decreaseRate ρ t) * potential A b d (alphaGen m ρ t) x := by
  let α := alphaGen m ρ t
  let σ := sigmaGen m ρ t
  let y := dualVec A b d α x
  have hρ : 0 < ρ := ht.trans_le htr
  have hα : 0 < α := alpha_pos ht htr
  have hσ : 0 < σ := (sigma_pos_le_one ht htr).1
  have hασ : α * σ = t / (48 * ρ ^ 2) := alpha_mul_sigma ht htr
  have hsmall : 2 * α * σ * ρ ≤ 1 := by
    have heq : 2 * α * σ * ρ = t / (24 * ρ) := by
      rw [show 2 * α * σ * ρ = 2 * (α * σ) * ρ by ring, hασ]
      field_simp
      ring
    rw [heq]
    apply (div_le_one (show 0 < 24 * ρ by positivity)).mpr
    linarith
  have hxt := (horc y (dual_nonneg A b d hd α x)).1
  have hb := potential_affine_bound A b d hd hρ.le hW hx hxt hα.le hσ.le hsmall
  have hf : lam A b d x / 5 * potential A b d α x <
      lagr A b y x - lagr A b y (orc y) := by
    simpa only [G2, dual_sum_eq_potential A b d hd, not_le] using hfail
  have herr : 4 * α ^ 2 * σ ^ 2 * ρ ^ 2 = α * σ * (t / 12) := by
    have hh : 4 * (α * σ) * ρ ^ 2 = t / 12 := by
      rw [hασ]
      field_simp
      norm_num
    nlinarith
  have hc : decreaseRate ρ t = α * σ * (t / 60) := by
    have hh := rate_identity (m := m) ht htr
    dsimp [α, σ]
    nlinarith [hh]
  have hcoef : decreaseRate ρ t ≤ α * σ * (lam A b d x / 5) -
      4 * α ^ 2 * σ ^ 2 * ρ ^ 2 := by
    rw [hc, herr, ← mul_sub]
    apply mul_le_mul_of_nonneg_left _ (mul_pos hα hσ).le
    linarith
  have hp := potential_pos A b d α x
  have hfscaled := mul_le_mul_of_nonneg_left hf.le (mul_pos hα hσ).le
  have hcscaled := mul_le_mul_of_nonneg_right hcoef hp.le
  change potential A b d α ((1 - σ) • x + σ • orc y) ≤
    (1 - decreaseRate ρ t) * potential A b d α x
  nlinarith

lemma log_potential_decrease [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ)
    (b d : Fin m → ℝ) {P : Set (Fin n → ℝ)} (hd : ∀ i, 0 < d i) {ρ t : ℝ}
    (ht : 0 < t) (htr : t ≤ ρ) (hW : WidthBound A b d P ρ)
    {orc : (Fin m → ℝ) → (Fin n → ℝ)} (horc : IsMinOracle P A orc)
    {x : Fin n → ℝ} (hx : x ∈ P) (hlive : t / 2 ≤ lam A b d x)
    (hfail : ¬ G2 A b d x (lam A b d x) (dualVec A b d (alphaGen m ρ t) x)
      (lagr A b (dualVec A b d (alphaGen m ρ t) x)
        (orc (dualVec A b d (alphaGen m ρ t) x)))) :
    Real.log (potential A b d (alphaGen m ρ t)
      ((1 - sigmaGen m ρ t) • x + sigmaGen m ρ t • orc (dualVec A b d (alphaGen m ρ t) x))) ≤
        Real.log (potential A b d (alphaGen m ρ t) x) - decreaseRate ρ t := by
  have h := Real.log_le_log (potential_pos A b d (alphaGen m ρ t) _)
    (potential_decrease A b d hd ht htr hW horc hx hlive hfail)
  have hc := (decreaseRate_pos_lt_one ht htr).2
  rw [Real.log_mul (ne_of_gt (sub_pos.mpr hc))
    (ne_of_gt (potential_pos A b d (alphaGen m ρ t) x))] at h
  have hh := Real.log_le_sub_one_of_pos (sub_pos.mpr hc)
  linarith

end GeneralPackingProof
-- END Potential

-- BEGIN Certificate
namespace GeneralPackingProof

open FracPackCover.General
open scoped BigOperators

variable {m n : ℕ}

lemma fixed_parameter_G1 [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    {P : Set (Fin n → ℝ)} (hd : ∀ i, 0 < d i) {ρ t : ℝ}
    (ht : 0 < t) (htr : t ≤ ρ) (hW : WidthBound A b d P ρ)
    {x : Fin n → ℝ} (hx : x ∈ P) (hlive : t / 2 ≤ lam A b d x) :
    G1 A b d x (lam A b d x) (dualVec A b d (alphaGen m ρ t) x) := by
  let α := alphaGen m ρ t
  let C : ℝ := 12 * m * ρ / t
  let l := lam A b d x
  let Φ := potential A b d α x
  have hm : (0 : ℝ) < m := by exact_mod_cast (NeZero.pos m)
  have hρ : 0 < ρ := ht.trans_le htr
  have hα : 0 < α := alpha_pos ht htr
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (scale_ge_twelve ht htr)
  have hl : 0 < l := by dsimp [l]; linarith
  have hlr : l ≤ ρ := lam_le_width A b d hd hW hx
  have hΦ : 0 < Φ := potential_pos A b d α x
  have hmax : Real.exp (α * l) ≤ Φ := exp_lam_le_potential A b d α x
  have hat : α * t = 4 * logScale m ρ t := alpha_mul_start m ht
  have hCt : C * t = 12 * m * ρ := by dsimp [C]; field_simp
  have hpoint (i : Fin m) : l * weight A b d α x i ≤
      2 * (weight A b d α x i * residual A b d x i) + l * Φ / (2 * m) := by
    have hw : 0 < weight A b d α x i := Real.exp_pos _
    by_cases hgood : l ≤ 2 * residual A b d x i
    · have hh := mul_le_mul_of_nonneg_right hgood hw.le
      have hn : 0 ≤ l * Φ / (2 * m) := by positivity
      nlinarith
    · have hres := (abs_le.mp (residual_abs_le A b d hd hW hx i)).1
      have he : α * residual A b d x i + logScale m ρ t ≤ α * l := by
        have hu := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hgood)) hα.le
        have hh := mul_le_mul_of_nonneg_left hlive hα.le
        dsimp [l] at *
        nlinarith
      have hexp := Real.exp_le_exp.mpr he
      rw [Real.exp_add] at hexp
      change Real.exp (α * residual A b d x i) * Real.exp (Real.log C) ≤ _ at hexp
      rw [Real.exp_log hC] at hexp
      have hwC : weight A b d α x i * C ≤ Φ := hexp.trans hmax
      have hscaled : 12 * m * ρ * weight A b d α x i ≤ t * Φ := by
        calc
          12 * m * ρ * weight A b d α x i = (weight A b d α x i * C) * t := by rw [← hCt]; ring
          _ ≤ Φ * t := mul_le_mul_of_nonneg_right hwC ht.le
          _ = _ := by ring
      have hsmall : 3 * ρ * weight A b d α x i ≤ l * Φ / (2 * m) := by
        apply (le_div_iff₀ (show 0 < (2 : ℝ) * m by positivity)).mpr
        have htf : t * Φ ≤ 2 * l * Φ :=
          mul_le_mul_of_nonneg_right (by dsimp [l]; linarith) hΦ.le
        nlinarith
      have hcoef : l - 2 * residual A b d x i ≤ 3 * ρ := by linarith
      have hmul := mul_le_mul_of_nonneg_right hcoef hw.le
      linarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  have hcancel : (m : ℝ) * (l * Φ / (2 * m)) = l * Φ / 2 := by field_simp
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [hcancel] at hsum
  have hpot : (∑ i, weight A b d α x i) = Φ := (potential_eq_sum_weight A b d α x).symm
  rw [hpot] at hsum
  unfold G1
  rw [dual_sum_eq_potential A b d hd, lagr_dual_eq]
  change l * Φ ≤ 4 * ∑ i, weight A b d α x i * residual A b d x i
  linarith

lemma infeasible_of_G1_G2 [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    {P : Set (Fin n → ℝ)} (hd : ∀ i, 0 < d i)
    {orc : (Fin m → ℝ) → (Fin n → ℝ)} (horc : IsMinOracle P A orc)
    {α : ℝ} {x : Fin n → ℝ} (hl : 0 < lam A b d x)
    (h1 : G1 A b d x (lam A b d x) (dualVec A b d α x))
    (h2 : G2 A b d x (lam A b d x) (dualVec A b d α x)
      (lagr A b (dualVec A b d α x) (orc (dualVec A b d α x)))) :
    ¬ ∃ z ∈ P, ∀ i, FracPackCover.Covering.rowVal A z i ≤ b i := by
  rintro ⟨z, hz, hfeas⟩
  have hy := dual_nonneg A b d hd α x
  have hor := oracle_lagr_le A b horc hy hz
  have hzval : lagr A b (dualVec A b d α x) z ≤ 0 := by
    exact Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hy i)
      (sub_nonpos.mpr (hfeas i)))
  have hpos := mul_pos hl (potential_pos A b d α x)
  unfold G1 at h1
  unfold G2 at h2
  rw [dual_sum_eq_potential A b d hd] at h1 h2
  nlinarith

lemma fixed_parameter_infeasible [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    {P : Set (Fin n → ℝ)} (hd : ∀ i, 0 < d i) {ρ t : ℝ}
    (ht : 0 < t) (htr : t ≤ ρ) (hW : WidthBound A b d P ρ)
    {orc : (Fin m → ℝ) → (Fin n → ℝ)} (horc : IsMinOracle P A orc)
    {x : Fin n → ℝ} (hx : x ∈ P) (hlive : t / 2 ≤ lam A b d x)
    (h2 : G2 A b d x (lam A b d x) (dualVec A b d (alphaGen m ρ t) x)
      (lagr A b (dualVec A b d (alphaGen m ρ t) x)
        (orc (dualVec A b d (alphaGen m ρ t) x)))) :
    ¬ ∃ z ∈ P, ∀ i, FracPackCover.Covering.rowVal A z i ≤ b i := by
  exact infeasible_of_G1_G2 A b d hd horc (by linarith)
    (fixed_parameter_G1 A b d hd ht htr hW hx hlive) h2

end GeneralPackingProof
-- END Certificate

-- BEGIN Rank
namespace GeneralPackingProof

open FracPackCover.General

noncomputable def potentialRank {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b d : Fin m → ℝ) (ρ t : ℝ) (x : Fin n → ℝ) : ℝ :=
  (Real.log (potential A b d (alphaGen m ρ t) x) - alphaGen m ρ t * t / 2) /
    decreaseRate ρ t

variable {m n : ℕ}

lemma potentialRank_nonneg [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ)
    (b d : Fin m → ℝ) {ρ t : ℝ} (ht : 0 < t) (htr : t ≤ ρ)
    {x : Fin n → ℝ} (hlive : t / 2 ≤ lam A b d x) :
    0 ≤ potentialRank A b d ρ t x := by
  have hl := Real.log_le_log (Real.exp_pos _)
    (exp_lam_le_potential A b d (alphaGen m ρ t) x)
  rw [Real.log_exp] at hl
  have ha := alpha_pos (m := m) ht htr
  have hh := mul_le_mul_of_nonneg_left hlive ha.le
  unfold potentialRank
  exact div_nonneg (by nlinarith) (decreaseRate_pos_lt_one ht htr).1.le

lemma potentialRank_decrease [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ)
    (b d : Fin m → ℝ) {P : Set (Fin n → ℝ)} (hd : ∀ i, 0 < d i) {ρ t : ℝ}
    (ht : 0 < t) (htr : t ≤ ρ) (hW : WidthBound A b d P ρ)
    {orc : (Fin m → ℝ) → (Fin n → ℝ)} (horc : IsMinOracle P A orc)
    {x : Fin n → ℝ} (hx : x ∈ P) (hlive : t / 2 ≤ lam A b d x)
    (hfail : ¬ G2 A b d x (lam A b d x) (dualVec A b d (alphaGen m ρ t) x)
      (lagr A b (dualVec A b d (alphaGen m ρ t) x)
        (orc (dualVec A b d (alphaGen m ρ t) x)))) :
    potentialRank A b d ρ t
      ((1 - sigmaGen m ρ t) • x + sigmaGen m ρ t • orc (dualVec A b d (alphaGen m ρ t) x)) ≤
        potentialRank A b d ρ t x - 1 := by
  have hdrop := log_potential_decrease A b d hd ht htr hW horc hx hlive hfail
  have hc := (decreaseRate_pos_lt_one ht htr).1
  have hdiv := div_le_div_of_nonneg_right
    (sub_le_sub_right hdrop (alphaGen m ρ t * t / 2)) hc.le
  have he : (Real.log (potential A b d (alphaGen m ρ t) x) - decreaseRate ρ t -
      alphaGen m ρ t * t / 2) / decreaseRate ρ t = potentialRank A b d ρ t x - 1 := by
    unfold potentialRank
    field_simp
    ring
  exact he ▸ hdiv

lemma potentialRank_initial_bound [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ)
    (b d : Fin m → ℝ) {ρ t : ℝ} (ht : 0 < t) (htr : t ≤ ρ)
    {x : Fin n → ℝ} (hstart : lam A b d x = t) :
    potentialRank A b d ρ t x ≤ initialBudget m ρ t := by
  have hm : (0 : ℝ) < m := by exact_mod_cast (NeZero.pos m)
  have hρ : 0 < ρ := ht.trans_le htr
  have hc := (decreaseRate_pos_lt_one ht htr).1
  have ha := alpha_pos (m := m) ht htr
  have hp := Real.log_le_log (potential_pos A b d (alphaGen m ρ t) x)
    (potential_le_exp_lam A b d ha.le x)
  rw [hstart, Real.log_mul (ne_of_gt hm) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at hp
  have hmC : (m : ℝ) ≤ 12 * m * ρ / t := by
    apply (le_div_iff₀ ht).mpr
    nlinarith [mul_le_mul_of_nonneg_left htr hm.le]
  have hlogm : Real.log m ≤ logScale m ρ t := Real.log_le_log hm hmC
  have hat := alpha_mul_start m (ρ := ρ) ht
  have hnum : Real.log (potential A b d (alphaGen m ρ t) x) - alphaGen m ρ t * t / 2 ≤
      3 * logScale m ρ t := by nlinarith
  have he : 3 * logScale m ρ t / decreaseRate ρ t = initialBudget m ρ t := by
    unfold decreaseRate initialBudget logScale
    field_simp
    ring
  exact he ▸ div_le_div_of_nonneg_right hnum hc.le

end GeneralPackingProof
-- END Rank

-- BEGIN InnerLoop
open scoped BigOperators
open Finset Set
namespace GeneralPackingProof
open FracPackCover.General

noncomputable def nextPoint {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b d : Fin m → ℝ) (orc : (Fin m → ℝ) → (Fin n → ℝ))
    (α σ : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  (1 - σ) • x + σ • orc (dualVec A b d α x)

section Inner
variable {m n : ℕ} [NeZero m]
variable (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
variable (orc : (Fin m → ℝ) → (Fin n → ℝ)) (t α σ : ℝ)
variable (P : Set (Fin n → ℝ)) (R : (Fin n → ℝ) → ℝ)

noncomputable def rankBudget (x : Fin n → ℝ) : ℝ :=
  if lam A b d x < t / 2 then 0 else R x + 2

/-- Exact loop accounting, including the unused final half-level test. -/
theorem improveLoop_rank_bound
    (hnonneg : ∀ x ∈ P, t / 2 ≤ lam A b d x → 0 ≤ R x)
    (hstep : ∀ x ∈ P, nextPoint A b d orc α σ x ∈ P)
    (hdrop : ∀ x ∈ P, t / 2 ≤ lam A b d x →
      ¬ G2 A b d x (lam A b d x) (dualVec A b d α x)
        (lagr A b (dualVec A b d α x) (orc (dualVec A b d α x))) →
      R (nextPoint A b d orc α σ x) ≤ R x - 1)
    (fuel : ℕ) (x : Fin n → ℝ) (hx : x ∈ P) (hf : 0 < fuel)
    (hbudget : rankBudget A b d t R x ≤ (fuel : ℝ)) :
    let r := improveLoop A b d orc t α σ fuel x
    r.point ∈ P ∧ r.exit ≠ ImproveExit.outOfFuel ∧
      (r.exit = ImproveExit.lambdaHalved → lam A b d r.point < t / 2) ∧
      (r.exit = ImproveExit.relaxedOpt → t / 2 ≤ lam A b d r.point ∧
        G2 A b d r.point (lam A b d r.point) (dualVec A b d α r.point)
          (lagr A b (dualVec A b d α r.point) (orc (dualVec A b d α r.point)))) ∧
      (r.calls : ℝ) ≤ rankBudget A b d t R x := by
  classical
  induction fuel generalizing x with
  | zero => omega
  | succ k ih =>
    dsimp only
    by_cases hh : lam A b d x < t / 2
    · simp only [improveLoop, hh, ↓reduceIte, rankBudget]
      simp [hx]
    · have hl : t / 2 ≤ lam A b d x := le_of_not_gt hh
      have hr := hnonneg x hx hl
      have hb : R x + 2 ≤ (k : ℝ) + 1 := by
        simpa only [rankBudget, hh, ↓reduceIte, Nat.cast_add, Nat.cast_one] using hbudget
      by_cases hg : G2 A b d x (lam A b d x) (dualVec A b d α x)
          (lagr A b (dualVec A b d α x) (orc (dualVec A b d α x)))
      · simp only [improveLoop, hh, hg, ↓reduceIte, rankBudget]
        refine ⟨hx, by decide, ?_, ?_, ?_⟩
        · intro he; cases he
        · intro _; exact ⟨hl, trivial⟩
        · norm_num; linarith
      · have hk : 0 < k := by
          by_contra hn
          have hz : k = 0 := by omega
          simp only [hz, Nat.cast_zero, zero_add] at hb
          linarith
        have hy := hstep x hx
        have hd := hdrop x hx hl hg
        have hby : rankBudget A b d t R (nextPoint A b d orc α σ x) ≤ (k : ℝ) := by
          unfold rankBudget
          split_ifs
          · positivity
          · linarith
        have hi := ih (nextPoint A b d orc α σ x) hy hk hby
        dsimp only at hi
        simp only [improveLoop, hh, hg, ↓reduceIte]
        change (improveLoop A b d orc t α σ k (nextPoint A b d orc α σ x)).point ∈ P ∧ _
        refine ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, ?_⟩
        have hc := hi.2.2.2.2
        simp only [rankBudget, hh, ↓reduceIte, Nat.cast_add, Nat.cast_one]
        by_cases hh' : lam A b d (nextPoint A b d orc α σ x) < t / 2
        · simp only [rankBudget, hh', ↓reduceIte] at hc
          dsimp only [nextPoint] at hc
          linarith
        · simp only [rankBudget, hh', ↓reduceIte] at hc
          dsimp only [nextPoint] at hc hd
          linarith
end Inner
end GeneralPackingProof
-- END InnerLoop

-- BEGIN GeometricBudget
open scoped BigOperators
namespace GeneralPackingProof

/-- The inverse-square credit invariant when a new halved level is reached. -/
theorem inverse_square_credit {t u z : ℝ} (ht : 0 < t) (hu : 0 < u)
    (hhalf : u ≤ t / 2) (hz : z ≤ 1 / (3 * t ^ 2)) :
    z + 1 / t ^ 2 ≤ 1 / (3 * u ^ 2) := by
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have hu2 : 0 < u ^ 2 := sq_pos_of_pos hu
  have hs : 4 * u ^ 2 ≤ t ^ 2 := by nlinarith
  have hrec : 4 / (3 * t ^ 2) ≤ 1 / (3 * u ^ 2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  calc
    z + 1 / t ^ 2 ≤ 1 / (3 * t ^ 2) + 1 / t ^ 2 := add_le_add_left hz _
    _ = 4 / (3 * t ^ 2) := by field_simp; ring
    _ ≤ _ := hrec

/-- A live call's charge is bounded using the terminal threshold, not the initial level. -/
theorem charged_cost_bound {ε t K z c N : ℝ} {j L : ℕ}
    (he : 0 < ε) (ht : ε < t) (hK : 0 ≤ K)
    (hz : z ≤ 1 / (3 * t ^ 2)) (hc : c ≤ 2 * (j : ℝ) + K * z)
    (hj : j + 1 ≤ L) (hN : 2 * (L : ℝ) + 4 * K / (3 * ε ^ 2) ≤ N) :
    c + (2 + K / t ^ 2) ≤ N := by
  have ht0 : 0 < t := lt_trans he ht
  have hsq : ε ^ 2 ≤ t ^ 2 := by nlinarith
  have hjr : (j : ℝ) + 1 ≤ (L : ℝ) := by exact_mod_cast hj
  have hcz : K * z ≤ K / (3 * t ^ 2) := by
    simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hz hK
  have hh : K / (3 * t ^ 2) + K / t ^ 2 = 4 * K / (3 * t ^ 2) := by
    field_simp; ring
  have hf : 4 * K / (3 * t ^ 2) ≤ 4 * K / (3 * ε ^ 2) := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
  linarith

/-- Non-strict power invariant suffices; the live threshold provides strictness. -/
theorem live_round_lt {ρ ε t : ℝ} (he : 0 < ε) (ht : ε < t)
    (j : ℕ) (hpow : (2 : ℝ) ^ j * t ≤ ρ) :
    j < ⌊Real.logb 2 (ρ / ε)⌋₊ + 1 := by
  have hp : 0 < (2 : ℝ) ^ j := by positivity
  have hlt : (2 : ℝ) ^ j < ρ / ε := (lt_div_iff₀ he).2 (by nlinarith)
  have hl := (Real.strictMonoOn_logb (show (1 : ℝ) < 2 by norm_num)) hp
    (lt_trans hp hlt) hlt
  have hj : (j : ℝ) < Real.logb 2 (ρ / ε) := by
    simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] using hl
  have hf : j ≤ ⌊Real.logb 2 (ρ / ε)⌋₊ := Nat.le_floor hj.le
  omega

end GeneralPackingProof
-- END GeometricBudget

-- BEGIN DriverLoop
open scoped BigOperators
open Set
namespace GeneralPackingProof
open FracPackCover.General

section Driver
variable {m n : ℕ} [NeZero m]
variable (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
variable (P : Set (Fin n → ℝ)) (ρ ε : ℝ)
variable (orc : (Fin m → ℝ) → (Fin n → ℝ)) (inner : ℕ)

/-- A full specification of every possible terminal driver outcome. -/
def DriverValid (Impossible : Prop) (N : ℝ) (r : DriverResult n) : Prop :=
  r.outcome ≠ DriverOutcome.outOfFuel ∧
  (∀ y, r.outcome = DriverOutcome.approx y → y ∈ P ∧ lam A b d y ≤ ε) ∧
  (r.outcome = DriverOutcome.infeasible → Impossible) ∧ (r.calls : ℝ) ≤ N

/-- Accumulated geometric credit proves the actual driver, without a trace surrogate. -/
theorem driverLoop_credit
    (he : 0 < ε) (K N : ℝ) (hK : 0 ≤ K)
    (Impossible : Prop)
    (hinner : ∀ x ∈ P, ε < lam A b d x →
      let r := improveGeneral A b d ρ orc inner x
      r.point ∈ P ∧ r.exit ≠ ImproveExit.outOfFuel ∧
      (r.exit = ImproveExit.lambdaHalved → lam A b d r.point < lam A b d x / 2) ∧
      (r.exit = ImproveExit.relaxedOpt → Impossible) ∧
      (r.calls : ℝ) ≤ 2 + K / (lam A b d x) ^ 2)
    (hN : 2 * ((⌊Real.logb 2 (ρ / ε)⌋₊ + 1 : ℕ) : ℝ) +
      4 * K / (3 * ε ^ 2) ≤ N)
    (k j c : ℕ) (x : Fin n → ℝ) (z : ℝ)
    (hx : x ∈ P)
    (hj : j ≤ ⌊Real.logb 2 (ρ / ε)⌋₊ + 1)
    (hf : ⌊Real.logb 2 (ρ / ε)⌋₊ + 2 ≤ k + j)
    (hp : (2 : ℝ) ^ j * lam A b d x ≤ ρ)
    (hz : 0 ≤ z) (hc : (c : ℝ) ≤ 2 * (j : ℝ) + K * z)
    (hcn : (c : ℝ) ≤ N)
    (hcredit : ε < lam A b d x → z ≤ 1 / (3 * (lam A b d x) ^ 2)) :
    DriverValid A b d P ε Impossible N (driverLoop A b d ρ ε orc inner k x c) := by
  classical
  induction k generalizing j c x z with
  | zero => omega
  | succ k ih =>
    by_cases hdone : lam A b d x ≤ ε
    · simp only [driverLoop, hdone, ↓reduceIte, DriverValid]
      refine ⟨(by intro h; cases h), ?_, ?_, hcn⟩
      · intro y hy
        cases hy
        exact ⟨hx, hdone⟩
      · intro h; cases h
    · have ht : ε < lam A b d x := lt_of_not_ge hdone
      have ht0 : 0 < lam A b d x := lt_trans he ht
      have hjlt := live_round_lt he ht j hp
      have hjnext : j + 1 ≤ ⌊Real.logb 2 (ρ / ε)⌋₊ + 1 := hjlt
      have hi := hinner x hx ht
      dsimp only at hi
      let r := improveGeneral A b d ρ orc inner x
      change r.point ∈ P ∧ r.exit ≠ ImproveExit.outOfFuel ∧
        (r.exit = ImproveExit.lambdaHalved → lam A b d r.point < lam A b d x / 2) ∧
        (r.exit = ImproveExit.relaxedOpt → Impossible) ∧
        (r.calls : ℝ) ≤ 2 + K / (lam A b d x) ^ 2 at hi
      have hcnew : ((c + r.calls : ℕ) : ℝ) ≤ N := by
        rw [Nat.cast_add]
        have hb := charged_cost_bound he ht hK (hcredit ht) hc hjnext hN
        linarith [hi.2.2.2.2]
      simp only [driverLoop, hdone, ↓reduceIte]
      change DriverValid A b d P ε Impossible N
        (match r.exit with
        | .outOfFuel => ⟨.outOfFuel, c + r.calls⟩
        | .relaxedOpt => if lam A b d r.point ≤ ε then ⟨.approx r.point, c + r.calls⟩
            else ⟨.infeasible, c + r.calls⟩
        | .lambdaHalved => driverLoop A b d ρ ε orc inner k r.point (c + r.calls))
      cases hr : r.exit with
      | outOfFuel => exact (hi.2.1 hr).elim
      | relaxedOpt =>
        simp only
        split_ifs with hresult
        · refine ⟨(by intro h; cases h), ?_, ?_, hcnew⟩
          · intro y hy; cases hy; exact ⟨hi.1, hresult⟩
          · intro h; cases h
        · refine ⟨(by intro h; cases h), ?_, ?_, hcnew⟩
          · intro y hy; cases hy
          · intro _; exact hi.2.2.2.1 hr
      | lambdaHalved =>
        simp only
        have hhalf := hi.2.2.1 hr
        have hpnew : (2 : ℝ) ^ (j + 1) * lam A b d r.point ≤ ρ := by
          rw [pow_succ]
          have hpow : 0 < (2 : ℝ) ^ j := by positivity
          nlinarith
        have hcostnew : ((c + r.calls : ℕ) : ℝ) ≤
            2 * ((j + 1 : ℕ) : ℝ) + K * (z + 1 / (lam A b d x) ^ 2) := by
          simp only [Nat.cast_add, Nat.cast_one]
          have hi' := hi.2.2.2.2
          simp only [div_eq_mul_inv, one_mul] at hi' ⊢
          nlinarith
        apply ih (j + 1) (c + r.calls) r.point
          (z + 1 / (lam A b d x) ^ 2) hi.1 hjnext (by omega) hpnew
          (by positivity) hcostnew hcnew
        intro hlive
        exact inverse_square_credit ht0 (lt_trans he hlive) hhalf.le (hcredit ht)

end Driver
end GeneralPackingProof
-- END DriverLoop

-- BEGIN BudgetArithmetic
namespace GeneralPackingProof

noncomputable def totalBudget (m : ℕ) (ρ ε : ℝ) : ℝ :=
  2 * ((⌊Real.logb 2 (ρ / ε)⌋₊ : ℝ) + 1) +
    11520 * ρ ^ 2 / ε ^ 2 * Real.log (12 * m * max ρ ε / ε)

noncomputable def costScale (m : ℕ) (ρ ε : ℝ) : ℝ :=
  8640 * ρ ^ 2 * Real.log (12 * m * max ρ ε / ε)

theorem global_log_nonneg {m : ℕ} [NeZero m] {ρ ε : ℝ} (he : 0 < ε) :
    0 ≤ Real.log (12 * m * max ρ ε / ε) := by
  apply Real.log_nonneg
  apply (le_div_iff₀ he).2
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast NeZero.one_le
  have hh : ε ≤ max ρ ε := le_max_right _ _
  have hp : 0 < max ρ ε := lt_of_lt_of_le he hh
  nlinarith

theorem costScale_nonneg {m : ℕ} [NeZero m] {ρ ε : ℝ} (he : 0 < ε) :
    0 ≤ costScale m ρ ε := by
  unfold costScale
  exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (global_log_nonneg he)

theorem totalBudget_decomposition (m : ℕ) (ρ ε : ℝ) :
    totalBudget m ρ ε =
      2 * ((⌊Real.logb 2 (ρ / ε)⌋₊ + 1 : ℕ) : ℝ) +
        4 * costScale m ρ ε / (3 * ε ^ 2) := by
  simp only [totalBudget, costScale, Nat.cast_add, Nat.cast_one]
  ring

theorem totalBudget_outer_fuel {m : ℕ} [NeZero m] {ρ ε : ℝ} (he : 0 < ε)
    (fuel : ℕ) (hf : totalBudget m ρ ε ≤ (fuel : ℝ)) :
    ⌊Real.logb 2 (ρ / ε)⌋₊ + 2 ≤ fuel := by
  rw [totalBudget_decomposition] at hf
  have hp : 0 ≤ 4 * costScale m ρ ε / (3 * ε ^ 2) := by
    exact div_nonneg (mul_nonneg (by norm_num) (costScale_nonneg he)) (by positivity)
  have h : ((⌊Real.logb 2 (ρ / ε)⌋₊ + 2 : ℕ) : ℝ) ≤ (fuel : ℝ) := by
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hf ⊢
    have hn : (0 : ℝ) ≤ (⌊Real.logb 2 (ρ / ε)⌋₊ : ℝ) := Nat.cast_nonneg _
    linarith
  exact_mod_cast h

/-- Each individual call fits the same common fuel used by the native driver. -/
theorem initialBudget_le_global {m : ℕ} [NeZero m] {ρ ε t : ℝ}
    (he : 0 < ε) (ht : ε < t) (htr : t ≤ ρ) :
    2 + 8640 * ρ ^ 2 / t ^ 2 * Real.log (12 * m * ρ / t) ≤ totalBudget m ρ ε := by
  have ht0 : 0 < t := lt_trans he ht
  have hr : 0 < ρ := lt_of_lt_of_le ht0 htr
  have hm : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have harg : 0 < 12 * (m : ℝ) * ρ / t := by positivity
  have hnum : 12 * (m : ℝ) * ρ ≤ 12 * m * max ρ ε := by
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
  have hratio : 12 * (m : ℝ) * ρ / t ≤ 12 * m * max ρ ε / ε := by
    exact (div_le_div_of_nonneg_left (by positivity) he ht.le).trans
      ((div_le_div_iff_of_pos_right he).2 hnum)
  have hlog := Real.log_le_log harg hratio
  have hscale : 8640 * ρ ^ 2 / t ^ 2 * Real.log (12 * m * ρ / t) ≤
      costScale m ρ ε / t ^ 2 := by
    calc
      _ ≤ (8640 * ρ ^ 2 / t ^ 2) * Real.log (12 * m * max ρ ε / ε) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = _ := by unfold costScale; ring
  have hi : costScale m ρ ε / t ^ 2 ≤ costScale m ρ ε / ε ^ 2 :=
    div_le_div_of_nonneg_left (costScale_nonneg he) (by positivity) (by nlinarith)
  have hN := totalBudget_decomposition m ρ ε
  have hk := costScale_nonneg (m := m) (ρ := ρ) he
  have hwide : costScale m ρ ε / ε ^ 2 ≤ 4 * costScale m ρ ε / (3 * ε ^ 2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [sq_nonneg ε]
  have hnat : (0 : ℝ) ≤ (⌊Real.logb 2 (ρ / ε)⌋₊ : ℝ) := Nat.cast_nonneg _
  simp only [Nat.cast_add, Nat.cast_one] at hN
  linarith

end GeneralPackingProof
-- END BudgetArithmetic

-- BEGIN BudgetComparison
namespace GeneralPackingProof

theorem initialBudget_le_costScale {m : ℕ} [NeZero m] {ρ ε t : ℝ}
    (he : 0 < ε) (ht : ε < t) (htr : t ≤ ρ) :
    initialBudget m ρ t ≤ costScale m ρ ε / t ^ 2 := by
  have ht0 : 0 < t := lt_trans he ht
  have hr : 0 < ρ := ht0.trans_le htr
  have hm : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have harg : 0 < 12 * (m : ℝ) * ρ / t := by positivity
  have hnum : 12 * (m : ℝ) * ρ ≤ 12 * m * max ρ ε :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
  have hratio : 12 * (m : ℝ) * ρ / t ≤ 12 * m * max ρ ε / ε :=
    (div_le_div_of_nonneg_left (by positivity) he ht.le).trans
      ((div_le_div_iff_of_pos_right he).2 hnum)
  have hlog := Real.log_le_log harg hratio
  unfold initialBudget
  calc
    _ ≤ (8640 * ρ ^ 2 / t ^ 2) * Real.log (12 * m * max ρ ε / ε) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = _ := by unfold costScale; ring

theorem common_inner_fuel {m : ℕ} [NeZero m] {ρ ε t : ℝ}
    (he : 0 < ε) (ht : ε < t) (htr : t ≤ ρ) (fuel : ℕ)
    (hf : totalBudget m ρ ε ≤ (fuel : ℝ)) :
    initialBudget m ρ t + 2 ≤ (fuel : ℝ) := by
  have h := (initialBudget_le_global he ht htr).trans hf
  change 2 + initialBudget m ρ t ≤ (fuel : ℝ) at h
  linarith

end GeneralPackingProof
-- END BudgetComparison

-- BEGIN DriverTheorem
namespace GeneralPackingProof
open FracPackCover.General
open Set

/-- The common outer fuel and the initial zero credit instantiate the exact driver. -/
theorem generalDriver_of_inner {m n : ℕ} [NeZero m]
    (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (ρ ε : ℝ) (he : 0 < ε)
    (orc : (Fin m → ℝ) → (Fin n → ℝ)) (fuel : ℕ)
    (Impossible : Prop)
    (hinner : ∀ x ∈ P, ε < lam A b d x →
      let r := improveGeneral A b d ρ orc fuel x
      r.point ∈ P ∧ r.exit ≠ ImproveExit.outOfFuel ∧
      (r.exit = ImproveExit.lambdaHalved → lam A b d r.point < lam A b d x / 2) ∧
      (r.exit = ImproveExit.relaxedOpt → Impossible) ∧
      (r.calls : ℝ) ≤ 2 + costScale m ρ ε / (lam A b d x) ^ 2)
    (x0 : Fin n → ℝ) (hx : x0 ∈ P) (hl : lam A b d x0 ≤ ρ)
    (hf : totalBudget m ρ ε ≤ (fuel : ℝ)) :
    DriverValid A b d P ε Impossible (totalBudget m ρ ε)
      (generalDriver A b d ρ ε orc fuel x0) := by
  have hcost := costScale_nonneg (m := m) (ρ := ρ) he
  have hN : 0 ≤ totalBudget m ρ ε := by
    rw [totalBudget_decomposition]
    positivity
  have hout := totalBudget_outer_fuel he fuel hf
  apply driverLoop_credit A b d P ρ ε orc fuel he (costScale m ρ ε)
    (totalBudget m ρ ε) hcost Impossible hinner
    (le_of_eq (totalBudget_decomposition m ρ ε).symm) fuel 0 0 x0 0 hx
  · omega
  · simpa only [Nat.add_zero] using hout
  · simpa only [pow_zero, one_mul] using hl
  · exact le_refl 0
  · norm_num
  · simpa only [Nat.cast_zero] using hN
  · intro _; positivity

end GeneralPackingProof
-- END DriverTheorem

-- BEGIN InnerTheorem
namespace GeneralPackingProof
open FracPackCover.General
open Set

theorem improveGeneral_spec {m n : ℕ} [NeZero m]
    (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    {P : Set (Fin n → ℝ)} (hP : Convex ℝ P) (hd : ∀ i, 0 < d i)
    {ρ : ℝ} (hW : WidthBound A b d P ρ)
    {orc : (Fin m → ℝ) → (Fin n → ℝ)} (horc : IsMinOracle P A orc)
    {x : Fin n → ℝ} (hx : x ∈ P) (ht : 0 < lam A b d x)
    (fuel : ℕ) (hf : initialBudget m ρ (lam A b d x) + 2 ≤ (fuel : ℝ)) :
    let r := improveGeneral A b d ρ orc fuel x
    r.point ∈ P ∧ r.exit ≠ ImproveExit.outOfFuel ∧
    (r.exit = ImproveExit.lambdaHalved → lam A b d r.point < lam A b d x / 2) ∧
    (r.exit = ImproveExit.relaxedOpt →
      ¬ ∃ z ∈ P, ∀ i, FracPackCover.Covering.rowVal A z i ≤ b i) ∧
    (r.calls : ℝ) ≤ initialBudget m ρ (lam A b d x) + 2 := by
  let t := lam A b d x
  have htr : t ≤ ρ := lam_le_width A b d hd hW hx
  have hσ := sigma_pos_le_one (m := m) ht htr
  have hB := initialBudget_nonneg (m := m) ht htr
  have hpos : 0 < fuel := by
    by_contra hn
    have hz : fuel = 0 := by omega
    simp only [hz, Nat.cast_zero] at hf
    linarith
  have hi := improveLoop_rank_bound A b d orc t (alphaGen m ρ t) (sigmaGen m ρ t)
    P (potentialRank A b d ρ t)
    (fun y _ hl => potentialRank_nonneg A b d ht htr hl)
    (fun y hy => step_mem A b d hP hd horc _ hσ.1.le hσ.2 hy)
    (fun y hy hl hg => potentialRank_decrease A b d hd ht htr hW horc hy hl hg)
    fuel x hx hpos
  have hstart : lam A b d x = t := rfl
  have hr := potentialRank_initial_bound A b d ht htr hstart
  have hh : ¬ lam A b d x < t / 2 := by dsimp [t]; linarith
  have hbudget : rankBudget A b d t (potentialRank A b d ρ t) x ≤ (fuel : ℝ) := by
    simp only [rankBudget, hh, ↓reduceIte]
    linarith
  have hi' := hi hbudget
  dsimp only at hi' ⊢
  change (improveGeneral A b d ρ orc fuel x).point ∈ P ∧ _ at hi'
  refine ⟨hi'.1, hi'.2.1, hi'.2.2.1, ?_, ?_⟩
  · intro he
    have hg := hi'.2.2.2.1 he
    exact fixed_parameter_infeasible A b d hd ht htr hW horc hi'.1 hg.1 hg.2
  · have hc := hi'.2.2.2.2
    simp only [rankBudget, hh, ↓reduceIte] at hc
    change ((improveGeneral A b d ρ orc fuel x).calls : ℝ) ≤
      potentialRank A b d ρ (lam A b d x) x + 2 at hc
    linarith

end GeneralPackingProof
-- END InnerTheorem

-- BEGIN NativeRoot
namespace FracPackCover.General

/-- Theorem 4.5 (p. 27), for the driver over IMPROVE-GENERAL with the corrected parameters.
For every `ε ∈ (0,1)`, every start `x₀ ∈ P` and every exact minimizing oracle, the driver run with
any fuel `≥ N` stops; if it outputs `x` then `x ∈ P` and `Ax ≤ b + εd`; if it reports
infeasibility then no `x ∈ P` has `Ax ≤ b`; and it makes at most
`N = 2(⌊log₂(ρ/ε)⌋ + 1) + 11520 ρ² ε⁻² ln(12 m max(ρ,ε)/ε)` oracle calls (the paper writes
`O(ρ²ε⁻² log(mρε⁻¹))`). -/
theorem theorem_4_5 {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hP : Convex ℝ P) (hd : ∀ i, 0 < d i)
    (ρ : ℝ) (hρ : 0 < ρ) (hW : WidthBound A b d P ρ)
    (orc : (Fin m → ℝ) → (Fin n → ℝ)) (horc : IsMinOracle P A orc)
    (x0 : Fin n → ℝ) (hx0 : x0 ∈ P) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (fuel : ℕ)
    (hfuel : 2 * ((⌊Real.logb 2 (ρ / ε)⌋₊ : ℝ) + 1)
        + 11520 * ρ ^ 2 / ε ^ 2 * Real.log (12 * m * max ρ ε / ε) ≤ (fuel : ℝ)) :
    (generalDriver A b d ρ ε orc fuel x0).outcome ≠ DriverOutcome.outOfFuel ∧
    (∀ x, (generalDriver A b d ρ ε orc fuel x0).outcome = DriverOutcome.approx x →
        x ∈ P ∧ ∀ i, FracPackCover.Covering.rowVal A x i ≤ b i + ε * d i) ∧
    ((generalDriver A b d ρ ε orc fuel x0).outcome = DriverOutcome.infeasible →
        ¬ ∃ x ∈ P, ∀ i, FracPackCover.Covering.rowVal A x i ≤ b i) ∧
    ((generalDriver A b d ρ ε orc fuel x0).calls : ℝ) ≤
        2 * ((⌊Real.logb 2 (ρ / ε)⌋₊ : ℝ) + 1)
          + 11520 * ρ ^ 2 / ε ^ 2 * Real.log (12 * m * max ρ ε / ε) := by
  have _ := hρ
  have _ := hε1
  have hinner (x : Fin n → ℝ) (hx : x ∈ P) (hl : ε < lam A b d x) :=
    GeneralPackingProof.improveGeneral_spec A b d hP hd hW horc hx (hε0.trans hl) fuel
      (GeneralPackingProof.common_inner_fuel hε0 hl
        (GeneralPackingProof.lam_le_width A b d hd hW hx) fuel hfuel)
  have h := GeneralPackingProof.generalDriver_of_inner A b d P ρ ε hε0 orc fuel
    (¬ ∃ z ∈ P, ∀ i, FracPackCover.Covering.rowVal A z i ≤ b i)
    (fun x hx hl => by
      have hi := hinner x hx hl
      dsimp only at hi ⊢
      refine ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, ?_⟩
      have hs := GeneralPackingProof.initialBudget_le_costScale (m := m) hε0 hl
        (GeneralPackingProof.lam_le_width A b d hd hW hx)
      linarith [hi.2.2.2.2])
    x0 hx0 (GeneralPackingProof.lam_le_width A b d hd hW hx0) hfuel
  refine ⟨h.1, ?_, h.2.2.1, h.2.2.2⟩
  intro x hx
  have hh := h.2.1 x hx
  exact ⟨hh.1, GeneralPackingProof.approx_of_lam_le A b d hd hh.2⟩

end FracPackCover.General
-- END NativeRoot

open FracPackCover.General

theorem solution {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hP : Convex ℝ P) (hd : ∀ i, 0 < d i)
    (ρ : ℝ) (hρ : 0 < ρ) (hW : WidthBound A b d P ρ)
    (orc : (Fin m → ℝ) → (Fin n → ℝ)) (horc : IsMinOracle P A orc)
    (x0 : Fin n → ℝ) (hx0 : x0 ∈ P) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (fuel : ℕ)
    (hfuel : 2 * ((⌊Real.logb 2 (ρ / ε)⌋₊ : ℝ) + 1)
        + 11520 * ρ ^ 2 / ε ^ 2 * Real.log (12 * m * max ρ ε / ε) ≤ (fuel : ℝ)) :
    (generalDriver A b d ρ ε orc fuel x0).outcome ≠ DriverOutcome.outOfFuel ∧
    (∀ x, (generalDriver A b d ρ ε orc fuel x0).outcome = DriverOutcome.approx x →
        x ∈ P ∧ ∀ i, FracPackCover.Covering.rowVal A x i ≤ b i + ε * d i) ∧
    ((generalDriver A b d ρ ε orc fuel x0).outcome = DriverOutcome.infeasible →
        ¬ ∃ x ∈ P, ∀ i, FracPackCover.Covering.rowVal A x i ≤ b i) ∧
    ((generalDriver A b d ρ ε orc fuel x0).calls : ℝ) ≤
        2 * ((⌊Real.logb 2 (ρ / ε)⌋₊ : ℝ) + 1)
          + 11520 * ρ ^ 2 / ε ^ 2 * Real.log (12 * m * max ρ ε / ε) :=
  FracPackCover.General.theorem_4_5 A b d P hP hd ρ hρ hW orc horc x0 hx0 ε hε0 hε1 fuel hfuel
