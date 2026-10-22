-- Prove2me | solution 1 for FracPackCover.Covering.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T23:25:19.475132+00:00
-- url     : https://prove2.me/submissions/2a635878-948e-47e6-852e-df35d3153398

import Mathlib
import Definitions.Def_FracPackCover_Covering_Basic
import Definitions.Def_FracPackCover_Covering_ImproveCover



namespace FracPackCover.Covering

open Finset

lemma e79_rowVal_comb {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x z : Fin n → ℝ) (σ : ℝ)
    (i : Fin m) :
    rowVal A ((1 - σ) • x + σ • z) i = (1 - σ) * rowVal A x i + σ * rowVal A z i := by
  simp only [rowVal, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring

lemma e79_rowVal_nonneg {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    {P : Set (Fin n → ℝ)} (hdata : IsCoveringData A b P) {x : Fin n → ℝ} (hx : x ∈ P)
    (i : Fin m) : 0 ≤ rowVal A x i :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (hdata.1 i j) (hdata.2.2.2.2 x hx j))

lemma e79_r_nonneg {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    {P : Set (Fin n → ℝ)} (hdata : IsCoveringData A b P) {x : Fin n → ℝ} (hx : x ∈ P)
    (i : Fin m) : 0 ≤ rowVal A x i / b i :=
  div_nonneg (e79_rowVal_nonneg hdata hx i) (hdata.2.1 i).le

lemma e79_r_le {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    {P : Set (Fin n → ℝ)} (hdata : IsCoveringData A b P) {ρ : ℝ} (hρ : WidthBound A b P ρ)
    {x : Fin n → ℝ} (hx : x ∈ P) (i : Fin m) : rowVal A x i / b i ≤ ρ := by
  rw [div_le_iff₀ (hdata.2.1 i)]; exact hρ.2 x hx i

lemma e79_lam_le {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) (i : Fin m) : lam A b x ≤ rowVal A x i / b i :=
  Finset.inf'_le _ (mem_univ i)

lemma e79_le_lam {m n : ℕ} [NeZero m] {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    {x : Fin n → ℝ} {c : ℝ} (h : ∀ i, c ≤ rowVal A x i / b i) : c ≤ lam A b x :=
  Finset.le_inf' _ _ (fun i _ => h i)

lemma e79_lam_attained {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) : ∃ i, lam A b x = rowVal A x i / b i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun i => rowVal A x i / b i)
  exact ⟨i, hi⟩

lemma e79_potential_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hb : ∀ i, 0 < b i) (α : ℝ) (x : Fin n → ℝ) :
    potential A b α x = ∑ i, Real.exp (-(α * (rowVal A x i / b i))) := by
  unfold potential ytb dualY
  apply sum_congr rfl; intro i _
  have h1 := (hb i).ne'
  rw [mul_div_assoc]
  field_simp

lemma e79_yAx_dualY {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (α : ℝ) (x z : Fin n → ℝ) :
    yAx A (dualY A b α x) z =
      ∑ i, Real.exp (-(α * (rowVal A x i / b i))) * (rowVal A z i / b i) := by
  unfold yAx dualY
  apply sum_congr rfl; intro i _
  rw [mul_div_assoc]
  ring

lemma e79_ytb_dualY {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hb : ∀ i, 0 < b i) (α : ℝ) (x : Fin n → ℝ) :
    ytb b (dualY A b α x) = ∑ i, Real.exp (-(α * (rowVal A x i / b i))) :=
  e79_potential_eq A b hb α x

lemma e79_dualY_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hb : ∀ i, 0 < b i) (α : ℝ) (x : Fin n → ℝ) (i : Fin m) : 0 ≤ dualY A b α x i := by
  unfold dualY
  exact mul_nonneg (div_nonneg zero_le_one (hb i).le) (Real.exp_pos _).le

/-- One step of IMPROVE-COVER decreases the potential by the factor `1 - εασ`. -/
lemma e79_pot_step {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hdata : IsCoveringData A b P) (ρ : ℝ) (hρ : WidthBound A b P ρ)
    (x z : Fin n → ℝ) (hx : x ∈ P) (hz : z ∈ P)
    (ε α σ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hα : 0 < α) (hσ0 : 0 ≤ σ)
    (hσ : α * σ * ρ ≤ ε / 4)
    (hmax : ∀ x' ∈ P, yAx A (dualY A b α x) x' ≤ yAx A (dualY A b α x) z)
    (hC2 : ¬ C2 A b ε (dualY A b α x) x (yAx A (dualY A b α x) z)) :
    potential A b α ((1 - σ) • x + σ • z) ≤ (1 - ε * α * σ) * potential A b α x := by
  have hb := hdata.2.1
  set e : Fin m → ℝ := fun i => Real.exp (-(α * (rowVal A x i / b i))) with he
  set r : Fin m → ℝ := fun i => rowVal A x i / b i with hr
  set s : Fin m → ℝ := fun i => rowVal A z i / b i with hs
  have hΦ : potential A b α x = ∑ i, e i := e79_potential_eq A b hb α x
  have hD : yAx A (dualY A b α x) x = ∑ i, e i * r i := e79_yAx_dualY A b α x x
  have hC : yAx A (dualY A b α x) z = ∑ i, e i * s i := e79_yAx_dualY A b α x z
  have hytb : ytb b (dualY A b α x) = ∑ i, e i := e79_ytb_dualY A b hb α x
  have hασ : 0 ≤ α * σ := mul_nonneg hα.le hσ0
  have hΦhat : potential A b α ((1 - σ) • x + σ • z) =
      ∑ i, e i * Real.exp (-(α * σ * (s i - r i))) := by
    rw [e79_potential_eq A b hb]
    apply sum_congr rfl; intro i _
    rw [e79_rowVal_comb, he, hr, hs]
    simp only
    rw [← Real.exp_add]
    congr 1
    have := (hb i).ne'
    field_simp
    ring
  have hterm : ∀ i, e i * Real.exp (-(α * σ * (s i - r i))) ≤
      e i + (-(α * σ) + ε / 4 * (α * σ)) * (e i * s i) +
        (α * σ + ε / 4 * (α * σ)) * (e i * r i) := by
    intro i
    have hr0 : 0 ≤ r i := e79_r_nonneg hdata hx i
    have hs0 : 0 ≤ s i := e79_r_nonneg hdata hz i
    have hr1 : r i ≤ ρ := e79_r_le hdata hρ hx i
    have hs1 : s i ≤ ρ := e79_r_le hdata hρ hz i
    have he0 : 0 < e i := Real.exp_pos _
    set u := α * σ * (s i - r i) with hu
    have hab : |s i - r i| ≤ ρ := by rw [abs_le]; constructor <;> linarith
    have hu1 : |u| ≤ ε / 4 := by
      rw [hu, abs_mul, abs_of_nonneg hασ]
      calc α * σ * |s i - r i| ≤ α * σ * ρ := mul_le_mul_of_nonneg_left hab hασ
        _ ≤ ε / 4 := hσ
    have hu2 : |-u| ≤ 1 := by rw [abs_neg]; linarith
    have hexp := Real.abs_exp_sub_one_sub_id_le hu2
    have hexp' : Real.exp (-u) ≤ 1 - u + u ^ 2 := by
      have := (abs_le.mp hexp).2; nlinarith
    have hu3 : u ^ 2 ≤ ε / 4 * |u| := by
      rw [← sq_abs]; nlinarith [abs_nonneg u]
    have hu4 : |u| ≤ α * σ * (s i + r i) := by
      rw [hu, abs_mul, abs_of_nonneg hασ]
      apply mul_le_mul_of_nonneg_left _ hασ
      rw [abs_le]; constructor <;> linarith
    have hε4 : 0 ≤ ε / 4 := by linarith
    have : Real.exp (-u) ≤ 1 - u + ε / 4 * (α * σ * (s i + r i)) := by
      nlinarith [mul_le_mul_of_nonneg_left hu4 hε4]
    calc e i * Real.exp (-u) ≤ e i * (1 - u + ε / 4 * (α * σ * (s i + r i))) :=
          mul_le_mul_of_nonneg_left this he0.le
      _ = _ := by rw [hu]; ring
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ univ) => hterm i)
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum] at hsum
  rw [hΦhat, hΦ]
  set Φ := ∑ i, e i
  set D := ∑ i, e i * r i
  set C := ∑ i, e i * s i
  have hDC : D ≤ C := by rw [← hD, ← hC]; exact hmax x hx
  have hC0 : 0 ≤ C := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (Real.exp_pos _).le (e79_r_nonneg hdata hz i))
  have hD0 : 0 ≤ D := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (Real.exp_pos _).le (e79_r_nonneg hdata hx i))
  have hnC2 : ε * (C + Φ) < C - D := by
    unfold C2 at hC2; rw [hC, hD, hytb] at hC2; push_neg at hC2; exact hC2
  have key : ε / 4 * (C + D) + ε * Φ ≤ C - D := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left key hασ]

/-! ## Iterates of IMPROVE-COVER -/

lemma e79_log_ge {m : ℕ} [NeZero m] (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    3 / 4 ≤ Real.log (4 * m * ε⁻¹) ∧ Real.log m ≤ Real.log (4 * m * ε⁻¹) ∧
      Real.exp (Real.log (4 * m * ε⁻¹)) = 4 * m * ε⁻¹ := by
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  have hei : 1 < ε⁻¹ := by rw [lt_inv_comm₀ one_pos hε]; simpa using hε1
  have h4 : (4 : ℝ) ≤ 4 * m * ε⁻¹ := by nlinarith
  have hpos : 0 < 4 * (m : ℝ) * ε⁻¹ := by linarith
  refine ⟨?_, ?_, Real.exp_log hpos⟩
  · have := Real.one_sub_inv_le_log_of_pos hpos
    have : (4 * (m : ℝ) * ε⁻¹)⁻¹ ≤ 1 / 4 := by
      rw [inv_eq_one_div]; exact div_le_div_of_nonneg_left zero_le_one (by norm_num) h4
    linarith
  · apply Real.log_le_log (by linarith); nlinarith

section iter

variable {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (orc : (Fin m → ℝ) → (Fin n → ℝ)) (ρ ε : ℝ) (x : Fin n → ℝ)

/-- Basic facts on `α, σ` of IMPROVE-COVER. -/
lemma e79_params (hdata : IsCoveringData A b P) (hρ : WidthBound A b P ρ) (hx : x ∈ P)
    (hlam : 0 < lam A b x) (hε : 0 < ε) (hε1 : ε < 1) :
    0 < coverAlpha m ε (lam A b x) ∧ 0 < coverSigma m ρ ε (lam A b x) ∧
    coverSigma m ρ ε (lam A b x) ≤ 1 ∧
    coverAlpha m ε (lam A b x) * coverSigma m ρ ε (lam A b x) * ρ = ε / 4 ∧
    coverAlpha m ε (lam A b x) * coverSigma m ρ ε (lam A b x) = ε / (4 * ρ) ∧
    coverAlpha m ε (lam A b x) * lam A b x = 4 * ε⁻¹ * Real.log (4 * m * ε⁻¹) := by
  obtain ⟨hL, -, -⟩ := e79_log_ge (m := m) ε hε hε1
  set L := Real.log (4 * m * ε⁻¹)
  set l := lam A b x
  have hρ0 := hρ.1
  have hlρ : l ≤ ρ := by
    obtain ⟨i, hi⟩ := e79_lam_attained A b x
    rw [show l = lam A b x from rfl, hi]; exact e79_r_le hdata hρ hx i
  have hS : coverSigma m ρ ε l = ε / (4 * coverAlpha m ε l * ρ) := rfl
  have hA : coverAlpha m ε l = 4 * l⁻¹ * ε⁻¹ * L := rfl
  rw [hS, hA]
  clear_value L l
  have hα : 0 < 4 * l⁻¹ * ε⁻¹ * L := by
    have : 0 < L := by linarith
    positivity
  have hαρ : ε / 4 ≤ 4 * l⁻¹ * ε⁻¹ * L * ρ := by
    have : 4 * l⁻¹ * ε⁻¹ * L * ρ = 4 * L * ε⁻¹ * (ρ / l) := by
      field_simp
    have h1 : 1 ≤ ρ / l := by rw [le_div_iff₀ hlam]; linarith
    have h2 : 1 < ε⁻¹ := by rw [lt_inv_comm₀ one_pos hε]; simpa using hε1
    rw [this]
    have : 3 ≤ 4 * L * ε⁻¹ := by nlinarith
    nlinarith
  refine ⟨hα, ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · rw [div_le_one (by positivity)]; nlinarith
  · field_simp
  · field_simp
  · field_simp

lemma e79_iter_succ (t : ℕ) :
    coverIterate A b orc ρ ε x (t + 1) =
      coverStep A b orc (coverAlpha m ε (lam A b x)) (coverSigma m ρ ε (lam A b x))
        (coverIterate A b orc ρ ε x t) := by
  unfold coverIterate; rw [Function.iterate_succ_apply']

lemma e79_iter_mem (hdata : IsCoveringData A b P) (hρ : WidthBound A b P ρ)
    (horc : IsMaxOracle A P orc) (hx : x ∈ P)
    (hlam : 0 < lam A b x) (hε : 0 < ε) (hε1 : ε < 1) (t : ℕ) :
    coverIterate A b orc ρ ε x t ∈ P := by
  obtain ⟨-, hσ, hσ1, -⟩ := e79_params A b P ρ ε x hdata hρ hx hlam hε hε1
  induction t with
  | zero => simpa [coverIterate] using hx
  | succ t ih =>
    rw [e79_iter_succ]
    unfold coverStep
    exact hdata.2.2.1 ih (horc _ (e79_dualY_nonneg A b hdata.2.1 _ _)).1 (by linarith) hσ.le
      (by ring)

lemma e79_pot_decay (hdata : IsCoveringData A b P) (hρ : WidthBound A b P ρ)
    (horc : IsMaxOracle A P orc) (hx : x ∈ P)
    (hlam : 0 < lam A b x) (hε : 0 < ε) (hε1 : ε < 1) (t : ℕ)
    (ht : IsReachedCover A b orc ρ ε x t) :
    potential A b (coverAlpha m ε (lam A b x)) (coverIterate A b orc ρ ε x t) ≤
      Real.exp (-(ε * (ε / (4 * ρ)) * t)) *
        potential A b (coverAlpha m ε (lam A b x)) x := by
  obtain ⟨hα, hσ, hσ1, hασρ, hασ, -⟩ := e79_params A b P ρ ε x hdata hρ hx hlam hε hε1
  induction t with
  | zero => simp [coverIterate]
  | succ t ih =>
    have ht' : IsReachedCover A b orc ρ ε x t := fun s hs => ht s (by omega)
    have htest := ht t (by omega)
    have hmem := e79_iter_mem A b P orc ρ ε x hdata hρ horc hx hlam hε hε1 t
    set α := coverAlpha m ε (lam A b x)
    set σ := coverSigma m ρ ε (lam A b x)
    set xt := coverIterate A b orc ρ ε x t
    have hy := e79_dualY_nonneg A b hdata.2.1 α xt
    have hstep := e79_pot_step A b P hdata ρ hρ xt (orc (dualY A b α xt)) hmem
      (horc _ hy).1 ε α σ hε hε1.le hα hσ.le hασρ.le (horc _ hy).2 htest.2
    rw [e79_iter_succ]
    unfold coverStep
    have hp0 : 0 ≤ potential A b α xt := by
      rw [e79_potential_eq A b hdata.2.1]; exact sum_nonneg (fun i _ => (Real.exp_pos _).le)
    have h1 : 1 - ε * α * σ ≤ Real.exp (-(ε * (ε / (4 * ρ)))) := by
      have := Real.add_one_le_exp (-(ε * (ε / (4 * ρ))))
      rw [mul_assoc, hασ]; linarith
    calc potential A b α ((1 - σ) • xt + σ • orc (dualY A b α xt))
        ≤ (1 - ε * α * σ) * potential A b α xt := hstep
      _ ≤ Real.exp (-(ε * (ε / (4 * ρ)))) * potential A b α xt :=
          mul_le_mul_of_nonneg_right h1 hp0
      _ ≤ Real.exp (-(ε * (ε / (4 * ρ)))) *
            (Real.exp (-(ε * (ε / (4 * ρ)) * t)) * potential A b α x) :=
          mul_le_mul_of_nonneg_left (ih ht') (Real.exp_pos _).le
      _ = _ := by
          rw [← mul_assoc, ← Real.exp_add]; push_cast; ring_nf

lemma e79_pot_upper (hb : ∀ i, 0 < b i) (α : ℝ) (hα : 0 ≤ α) (z : Fin n → ℝ) :
    potential A b α z ≤ m * Real.exp (-(α * lam A b z)) := by
  rw [e79_potential_eq A b hb]
  calc ∑ i, Real.exp (-(α * (rowVal A z i / b i))) ≤ ∑ _i : Fin m, Real.exp (-(α * lam A b z)) :=
        sum_le_sum (fun i _ => Real.exp_le_exp.mpr (by
          nlinarith [e79_lam_le A b z i, mul_le_mul_of_nonneg_left (e79_lam_le A b z i) hα]))
    _ = _ := by simp

lemma e79_pot_row (hb : ∀ i, 0 < b i) (α : ℝ) (z : Fin n → ℝ) (i : Fin m) :
    Real.exp (-(α * (rowVal A z i / b i))) ≤ potential A b α z := by
  rw [e79_potential_eq A b hb]
  exact single_le_sum (f := fun i => Real.exp (-(α * (rowVal A z i / b i))))
    (fun i _ => (Real.exp_pos _).le) (mem_univ i)

lemma e79_pot_lower (hb : ∀ i, 0 < b i) (α : ℝ) (z : Fin n → ℝ) :
    Real.exp (-(α * lam A b z)) ≤ potential A b α z := by
  obtain ⟨i, hi⟩ := e79_lam_attained A b z
  rw [hi]; exact e79_pot_row A b hb α z i

/-- Lemma 3.4 core. -/
theorem e79_lam_ge (hdata : IsCoveringData A b P) (hρ : WidthBound A b P ρ)
    (horc : IsMaxOracle A P orc) (hx : x ∈ P)
    (hlam : 0 < lam A b x) (hε : 0 < ε) (hε1 : ε < 1) (t : ℕ)
    (ht : IsReachedCover A b orc ρ ε x t) :
    3 * lam A b x / 4 ≤ lam A b (coverIterate A b orc ρ ε x t) := by
  obtain ⟨hα, -, -, -, -, hαl⟩ := e79_params A b P ρ ε x hdata hρ hx hlam hε hε1
  obtain ⟨hL, hlogm, -⟩ := e79_log_ge (m := m) ε hε hε1
  have hdec := e79_pot_decay A b P orc ρ ε x hdata hρ horc hx hlam hε hε1 t ht
  set α := coverAlpha m ε (lam A b x)
  set l := lam A b x
  set L := Real.log (4 * m * ε⁻¹)
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  apply e79_le_lam
  intro i
  have h1 := e79_pot_row A b hdata.2.1 α (coverIterate A b orc ρ ε x t) i
  have h2 := e79_pot_upper A b hdata.2.1 α hα.le x
  have h3 : Real.exp (-(ε * (ε / (4 * ρ)) * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := hρ.1
    have : 0 ≤ ε * (ε / (4 * ρ)) * t := by positivity
    linarith
  have h4 : Real.exp (-(α * (rowVal A (coverIterate A b orc ρ ε x t) i / b i))) ≤
      Real.exp (Real.log m + -(α * l)) := by
    rw [Real.exp_add, Real.exp_log hm]
    have hp0 : 0 ≤ potential A b α x := le_trans (Real.exp_pos _).le (e79_pot_lower A b hdata.2.1 α x)
    calc _ ≤ _ := h1
      _ ≤ _ := hdec
      _ ≤ 1 * potential A b α x := mul_le_mul_of_nonneg_right h3 hp0
      _ ≤ _ := by rw [one_mul]; exact h2
  rw [Real.exp_le_exp] at h4
  -- r ≥ l - log m / α
  set r := rowVal A (coverIterate A b orc ρ ε x t) i / b i
  have h5 : α * (l - r) ≤ Real.log m := by linarith
  have h6 : Real.log m ≤ L := hlogm
  have h7 : α * (l / 4) ≥ L := by
    have : α * (l / 4) = ε⁻¹ * L := by rw [mul_div_assoc', hαl]; ring
    rw [this]
    have hei : 1 < ε⁻¹ := by rw [lt_inv_comm₀ one_pos hε]; simpa using hε1
    nlinarith
  have : α * (l - r) ≤ α * (l / 4) := by linarith
  have := le_of_mul_le_mul_left this hα
  linarith

end iter

end FracPackCover.Covering

open FracPackCover.Covering


theorem solution {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hdata : IsCoveringData A b P) (ρ : ℝ) (hρ : WidthBound A b P ρ)
    (orc : (Fin m → ℝ) → (Fin n → ℝ)) (horc : IsMaxOracle A P orc)
    (x : Fin n → ℝ) (hx : x ∈ P) (hlam : 0 < lam A b x) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (t : ℕ) (ht : IsReachedCover A b orc ρ ε x t) :
    3 * lam A b x / 4 ≤ lam A b (coverIterate A b orc ρ ε x t) := by
  exact e79_lam_ge A b P orc ρ ε x hdata hρ horc hx hlam hε hε1 t ht
