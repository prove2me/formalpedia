-- Prove2me | solution 1 for FracPackCover.General.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T21:57:05.044723+00:00
-- url     : https://prove2.me/submissions/7024e69e-5f57-4558-9b1d-a3ef723f4e4b

import Mathlib
import Definitions.Def_FracPackCover_General_Basic



namespace FracPackCover.General

open FracPackCover.Covering in
theorem rowVal_conv {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x xt : Fin n → ℝ) (σ : ℝ) (i : Fin m) :
    rowVal A ((1 - σ) • x + σ • xt) i = (1 - σ) * rowVal A x i + σ * rowVal A xt i := by
  unfold rowVal
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros; ring

open FracPackCover.Covering in
theorem lam_le_rho {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (hd : ∀ i, 0 < d i) (P : Set (Fin n → ℝ)) (ρ : ℝ)
    (hW : WidthBound A b d P ρ) (x : Fin n → ℝ) (hx : x ∈ P) : lam A b d x ≤ ρ := by
  unfold lam
  apply Finset.sup'_le
  intro i _
  have := hW x hx i
  rw [div_le_iff₀ (hd i)]
  exact le_trans (le_abs_self _) this

open FracPackCover.Covering in
theorem potential_ge_exp {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (hd : ∀ i, 0 < d i) (α : ℝ) (hα : 0 < α) (x : Fin n → ℝ) :
    Real.exp (α * lam A b d x) ≤ potential A b d α x := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin m))
    (fun i => (rowVal A x i - b i) / d i)
  have : lam A b d x = (rowVal A x i - b i) / d i := hi
  rw [this]
  unfold potential
  have h1 : Real.exp (α * ((rowVal A x i - b i) / d i)) = Real.exp (α * (rowVal A x i - b i) / d i) := by
    congr 1; ring
  rw [h1]
  exact Finset.single_le_sum (f := fun i => Real.exp (α * (rowVal A x i - b i) / d i))
    (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)

theorem potential_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ) (α : ℝ)
    (x : Fin n → ℝ) : 0 ≤ potential A b d α x :=
  Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)

open FracPackCover.Covering in
theorem lemma43_core {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hP : Convex ℝ P) (hd : ∀ i, 0 < d i)
    (ρ : ℝ) (hρ : 0 < ρ) (hW : WidthBound A b d P ρ)
    (x : Fin n → ℝ) (hx : x ∈ P)
    (α : ℝ) (hα : 0 < α)
    (xt : Fin n → ℝ) (hxt : xt ∈ P)
    (hnG2 : ¬ G2 A b d x (lam A b d x) (dualVec A b d α x)
      (lagr A b (dualVec A b d α x) xt))
    (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ : σ ≤ lam A b d x / (24 * α * ρ ^ 2)) :
    α * σ * lam A b d x * potential A b d α x / 30 ≤
      potential A b d α x - potential A b d α ((1 - σ) • x + σ • xt) := by
  set l := lam A b d x with hl
  have hlρ : l ≤ ρ := lam_le_rho A b d hd P ρ hW x hx
  have hσ' : σ * (24 * α * ρ ^ 2) ≤ l := by
    rw [le_div_iff₀ (by positivity)] at hσ; exact hσ
  have hl0 : 0 ≤ l := by
    have : 0 ≤ σ * (24 * α * ρ ^ 2) := by positivity
    linarith
  set r : Fin m → ℝ := fun i => (rowVal A x i - b i) / d i with hr
  set rt : Fin m → ℝ := fun i => (rowVal A xt i - b i) / d i with hrt
  have hr1 : ∀ i, |r i| ≤ ρ := by
    intro i
    have := hW x hx i
    simp only [hr]
    rw [abs_div, abs_of_pos (hd i), div_le_iff₀ (hd i)]; exact this
  have hrt1 : ∀ i, |rt i| ≤ ρ := by
    intro i
    have := hW xt hxt i
    simp only [hrt]
    rw [abs_div, abs_of_pos (hd i), div_le_iff₀ (hd i)]; exact this
  have hασ0 : 0 ≤ α * σ := by positivity
  have hkey : α * σ * (24 * ρ) ≤ 1 := by
    have h1 : (α * σ * (24 * ρ)) * ρ ≤ 1 * ρ := by nlinarith
    exact le_of_mul_le_mul_right h1 hρ
  set t : Fin m → ℝ := fun i => α * σ * (rt i - r i) with ht
  have htb : ∀ i, |t i| ≤ α * σ * (2 * ρ) := by
    intro i
    simp only [ht]
    rw [abs_mul, abs_of_nonneg hασ0]
    apply mul_le_mul_of_nonneg_left _ hασ0
    calc |rt i - r i| ≤ |rt i| + |r i| := abs_sub _ _
      _ ≤ 2 * ρ := by linarith [hr1 i, hrt1 i]
  have htb1 : ∀ i, |t i| ≤ 1 := by
    intro i
    have := htb i
    have : α * σ * (2 * ρ) ≤ 1 := by nlinarith
    linarith [htb i]
  have hexp : ∀ i, Real.exp (α * ((rowVal A ((1 - σ) • x + σ • xt) i - b i) / d i)) ≤
      Real.exp (α * r i) * (1 + t i + t i ^ 2) := by
    intro i
    have h1 : α * ((rowVal A ((1 - σ) • x + σ • xt) i - b i) / d i) = α * r i + t i := by
      rw [rowVal_conv]
      simp only [ht, hr, hrt]
      field_simp
      ring
    rw [h1, Real.exp_add]
    have := Real.abs_exp_sub_one_sub_id_le (htb1 i)
    have h2 : Real.exp (t i) ≤ 1 + t i + t i ^ 2 := by
      have := (abs_le.mp this).2; linarith
    exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  have hpot : potential A b d α ((1 - σ) • x + σ • xt) ≤
      ∑ i, Real.exp (α * r i) * (1 + t i + t i ^ 2) := by
    unfold potential
    apply Finset.sum_le_sum
    intro i _
    have := hexp i
    have h5 : α * (rowVal A ((1 - σ) • x + σ • xt) i - b i) / d i =
        α * ((rowVal A ((1 - σ) • x + σ • xt) i - b i) / d i) := by ring
    rw [h5]; exact this
  have hΦ : potential A b d α x = ∑ i, Real.exp (α * r i) := by
    unfold potential
    apply Finset.sum_congr rfl
    intro i _
    simp only [hr]; congr 1; ring
  -- linear term
  have hlin : ∑ i, Real.exp (α * r i) * t i =
      α * σ * (lagr A b (dualVec A b d α x) xt - lagr A b (dualVec A b d α x) x) := by
    unfold lagr
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have := (hd i).ne'
    simp only [ht, hr, hrt, dualVec]
    field_simp
  have hsumyd : ∑ i, dualVec A b d α x i * d i = potential A b d α x := by
    unfold potential
    apply Finset.sum_congr rfl
    intro i _
    have := (hd i).ne'
    simp only [dualVec]
    field_simp
  have hquad : ∑ i, Real.exp (α * r i) * t i ^ 2 ≤
      (α * σ * (2 * ρ)) ^ 2 * potential A b d α x := by
    rw [hΦ, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have : t i ^ 2 ≤ (α * σ * (2 * ρ)) ^ 2 := by
      rw [← sq_abs (t i)]
      exact pow_le_pow_left₀ (abs_nonneg _) (htb i) 2
    nlinarith [Real.exp_pos (α * r i)]
  have hnG := not_le.mp hnG2
  unfold G2 at hnG
  rw [hsumyd] at hnG
  have hsq : (α * σ * (2 * ρ)) ^ 2 ≤ α * σ * l / 6 := by
    have : (α * σ * (2 * ρ)) ^ 2 = (α * σ) * (4 * σ * α * ρ ^ 2) := by ring
    rw [this]
    nlinarith
  have hΦ0 := potential_nonneg A b d α x
  have hsplit : ∑ i, Real.exp (α * r i) * (1 + t i + t i ^ 2) =
      potential A b d α x + ∑ i, Real.exp (α * r i) * t i + ∑ i, Real.exp (α * r i) * t i ^ 2 := by
    rw [hΦ, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [hsplit] at hpot
  rw [hlin] at hpot
  have h3 : (α * σ * (2 * ρ)) ^ 2 * potential A b d α x ≤ α * σ * l / 6 * potential A b d α x :=
    mul_le_mul_of_nonneg_right hsq hΦ0
  have h4 : α * σ * (l / 5 * potential A b d α x) ≤
      α * σ * (lagr A b (dualVec A b d α x) x - lagr A b (dualVec A b d α x) xt) :=
    mul_le_mul_of_nonneg_left hnG.le hασ0
  nlinarith

end FracPackCover.General

open FracPackCover.General


theorem solution {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hP : Convex ℝ P) (hd : ∀ i, 0 < d i)
    (ρ : ℝ) (hρ : 0 < ρ) (hW : WidthBound A b d P ρ)
    (x : Fin n → ℝ) (hx : x ∈ P) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (α : ℝ) (hα : 0 < α)
    (xt : Fin n → ℝ) (hxt : xt ∈ P)
    (hmin : ∀ x' ∈ P, lagr A b (dualVec A b d α x) xt ≤ lagr A b (dualVec A b d α x) x')
    (hnG2 : ¬ G2 A b d x (lam A b d x) (dualVec A b d α x)
      (lagr A b (dualVec A b d α x) xt))
    (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ : σ ≤ lam A b d x / (24 * α * ρ ^ 2)) :
    α * σ * lam A b d x * potential A b d α x / 30 ≤
      potential A b d α x - potential A b d α ((1 - σ) • x + σ • xt) := by
  exact lemma43_core A b d P hP hd ρ hρ hW x hx α hα xt hxt hnG2 σ hσ0 hσ
