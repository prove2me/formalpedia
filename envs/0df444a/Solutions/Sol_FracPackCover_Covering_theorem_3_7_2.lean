-- Prove2me | solution 2 for FracPackCover.Covering.theorem_3_7
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T15:48:17.168661+00:00
-- url     : https://prove2.me/submissions/75e771ef-eb55-42b0-8b66-3c49e446e970

import Mathlib
import Definitions.Def_FracPackCover_Covering_Basic
import Definitions.Def_FracPackCover_Covering_ImproveCover
import Definitions.Def_FracPackCover_Covering_Driver
import Theorems.Thm_FracPackCover_Covering_lemma_3_6

-- carved verbatim out of submission 1ecda2e1-2e1b-4d79-b6f3-3e30cb184daf, lines 1026-1037

section
open FracPackCover
open FracPackCover.Covering
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

end

section
open FracPackCover
open FracPackCover.Covering
open Finset
variable {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (orc : (Fin m → ℝ) → (Fin n → ℝ)) (ρ ε : ℝ) (x : Fin n → ℝ)

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

lemma e79_count (hdata : IsCoveringData A b P) (hρ : WidthBound A b P ρ)
    (horc : IsMaxOracle A P orc) (hx : x ∈ P)
    (hlam : 0 < lam A b x) (hε : 0 < ε) (hε1 : ε < 1) (k : ℕ)
    (hk : IsReachedCover A b orc ρ ε x k) :
    ε * (ε / (4 * ρ)) * k ≤ Real.log m + coverAlpha m ε (lam A b x) *
      (lam A b (coverIterate A b orc ρ ε x k) - lam A b x) := by
  obtain ⟨hα, -, -, -, -, -⟩ := e79_params A b P ρ ε x hdata hρ hx hlam hε hε1
  have hdec := e79_pot_decay A b P orc ρ ε x hdata hρ horc hx hlam hε hε1 k hk
  set α := coverAlpha m ε (lam A b x)
  have hlow := e79_pot_lower A b hdata.2.1 α (coverIterate A b orc ρ ε x k)
  have hup := e79_pot_upper A b hdata.2.1 α hα.le x
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have h : Real.exp (-(α * lam A b (coverIterate A b orc ρ ε x k))) ≤
      Real.exp (-(ε * (ε / (4 * ρ)) * k) + (Real.log m + -(α * lam A b x))) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log hm]
    calc _ ≤ _ := hlow
      _ ≤ _ := hdec
      _ ≤ _ := mul_le_mul_of_nonneg_left hup (Real.exp_pos _).le
  rw [Real.exp_le_exp] at h
  linarith

lemma e79_loop_spec (ε l0 α σ : ℝ) : ∀ (t : ℕ) (x : Fin n → ℝ),
    (∀ s < t, coverTest A b orc ε l0 α ((coverStep A b orc α σ)^[s] x)) →
    ¬ coverTest A b orc ε l0 α ((coverStep A b orc α σ)^[t] x) →
    ∃ c ≤ t + 1, ∀ F, t < F →
      coverLoop A b orc ε l0 α σ F x = some ((coverStep A b orc α σ)^[t] x, c) := by
  intro t
  induction t with
  | zero =>
    intro x _ hn
    simp only [Function.iterate_zero, id] at hn ⊢
    by_cases h1 : lam A b x ≤ 2 * l0
    · have h2 : C2 A b ε (dualY A b α x) x (yAx A (dualY A b α x) (orc (dualY A b α x))) := by
        by_contra h2; exact hn ⟨h1, h2⟩
      refine ⟨1, le_rfl, fun F hF => ?_⟩
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      rw [coverLoop, if_pos h1, if_pos h2]
    · refine ⟨0, by omega, fun F hF => ?_⟩
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      rw [coverLoop, if_neg h1]
  | succ t ih =>
    intro x hs hn
    have h0 := hs 0 (by omega)
    simp only [Function.iterate_zero, id] at h0
    obtain ⟨c, hc, hF⟩ := ih (coverStep A b orc α σ x)
      (fun s hs' => by
        have := hs (s + 1) (by omega)
        rwa [Function.iterate_succ_apply] at this)
      (by rwa [Function.iterate_succ_apply] at hn)
    refine ⟨c + 1, by omega, fun F hF' => ?_⟩
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    rw [coverLoop, if_pos h0.1, if_neg h0.2, hF F' (by omega), Function.iterate_succ_apply]
    rfl

theorem e79_ic_spec (hdata : IsCoveringData A b P) (hρ : WidthBound A b P ρ)
    (horc : IsMaxOracle A P orc) (hx : x ∈ P)
    (hlam : 0 < lam A b x) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ T c : ℕ, c ≤ T + 1 ∧
      (∀ F, T < F → improveCover A b orc ρ ε x F = some (coverIterate A b orc ρ ε x T, c)) ∧
      IsReachedCover A b orc ρ ε x T ∧
      ¬ coverTest A b orc ε (lam A b x) (coverAlpha m ε (lam A b x))
          (coverIterate A b orc ρ ε x T) ∧
      (T : ℝ) ≤ 1 + 20 * ρ * ε⁻¹ ^ 3 * Real.log (4 * m * ε⁻¹) ∧
      (ε ≤ 1 / 12 → (∀ x' ∈ P, (1 - 6 * ε) * lam A b x' ≤ lam A b x) →
        (T : ℝ) ≤ 1 + 196 * ρ * ε⁻¹ ^ 2 * Real.log (4 * m * ε⁻¹)) := by
  obtain ⟨hα, -, -, -, -, hαl⟩ := e79_params A b P ρ ε x hdata hρ hx hlam hε hε1
  obtain ⟨hL, hlogm, -⟩ := e79_log_ge (m := m) ε hε hε1
  have hρ0 := hρ.1
  have hq : 0 < ε * (ε / (4 * ρ)) := by positivity
  have hei : 1 < ε⁻¹ := by rw [lt_inv_comm₀ one_pos hε]; simpa using hε1
  have hcount := e79_count A b P orc ρ ε x hdata hρ horc hx hlam hε hε1
  set α := coverAlpha m ε (lam A b x)
  set l := lam A b x
  set L := Real.log (4 * m * ε⁻¹) with hLdef
  have hB1 : 20 * ρ * ε⁻¹ ^ 3 * L = 5 * ε⁻¹ * L / (ε * (ε / (4 * ρ))) := by
    clear_value L; field_simp; ring
  have hB2 : 196 * ρ * ε⁻¹ ^ 2 * L = 49 * L / (ε * (ε / (4 * ρ))) := by
    clear_value L; field_simp; ring
  have hkB : ∀ k : ℕ, IsReachedCover A b orc ρ ε x (k + 1) →
      (k : ℝ) ≤ 20 * ρ * ε⁻¹ ^ 3 * L := by
    intro k hk
    have hc := hcount k (fun s hs => hk s (by omega))
    have h1 : lam A b (coverIterate A b orc ρ ε x k) ≤ 2 * l := (hk k (by omega)).1
    have h2 : α * (lam A b (coverIterate A b orc ρ ε x k) - l) ≤ α * l :=
      mul_le_mul_of_nonneg_left (by linarith) hα.le
    have h3 : L ≤ ε⁻¹ * L := by nlinarith
    rw [hB1, le_div_iff₀ hq]; linarith
  have hex : ∃ s, ¬ coverTest A b orc ε l α (coverIterate A b orc ρ ε x s) := by
    by_contra h; push_neg at h
    have h1 := hkB (⌈20 * ρ * ε⁻¹ ^ 3 * L⌉₊ + 1) (fun s _ => h s)
    have h2 := Nat.le_ceil (20 * ρ * ε⁻¹ ^ 3 * L)
    push_cast at h1; linarith
  classical
  have hTspec := Nat.find_spec hex
  have hTmin : IsReachedCover A b orc ρ ε x (Nat.find hex) :=
    fun s hs => not_not.mp (Nat.find_min hex hs)
  obtain ⟨c, hc, hF⟩ := e79_loop_spec A b orc ε l α (coverSigma m ρ ε l) (Nat.find hex) x
    hTmin hTspec
  have hBnn : 0 ≤ 20 * ρ * ε⁻¹ ^ 3 * L := by
    have : 0 ≤ L := by linarith
    positivity
  have hcase : Nat.find hex = 0 ∨ ∃ k, Nat.find hex = k + 1 := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨Nat.find hex - 1, by omega⟩
  refine ⟨Nat.find hex, c, hc, fun F hFT => hF F hFT, hTmin, hTspec, ?_, ?_⟩
  · rcases hcase with h0 | ⟨k, h0⟩
    · rw [h0]; push_cast; linarith
    · have := hkB k (by rw [← h0]; exact hTmin)
      rw [h0]; push_cast; linarith
  · intro h12 hopt
    rcases hcase with h0 | ⟨k, h0⟩
    · rw [h0]; push_cast
      have : 0 ≤ L := by linarith
      have : 0 ≤ 196 * ρ * ε⁻¹ ^ 2 * L := by positivity
      linarith
    · have hk : IsReachedCover A b orc ρ ε x (k + 1) := by rw [← h0]; exact hTmin
      have hc := hcount k (fun s hs => hk s (by omega))
      have hmem := e79_iter_mem A b P orc ρ ε x hdata hρ horc hx hlam hε hε1 k
      have ho := hopt _ hmem
      set lk := lam A b (coverIterate A b orc ρ ε x k)
      have hlk0 : 0 < lk := lt_of_lt_of_le (by linarith) (e79_lam_ge A b P orc ρ ε x hdata hρ horc
        hx hlam hε hε1 k (fun s hs => hk s (by omega)))
      have ha : lk ≤ 2 * l := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 2 - 6 * ε) hlk0.le]
      have hb : lk - l ≤ 6 * ε * lk := by linarith
      have hc6 : 6 * ε * lk ≤ 12 * ε * l := by
        nlinarith [mul_le_mul_of_nonneg_left ha (by linarith : 0 ≤ 6 * ε)]
      have h1 : lk - l ≤ 12 * ε * l := by linarith
      have h2 : α * (lk - l) ≤ α * (12 * ε * l) := mul_le_mul_of_nonneg_left h1 hα.le
      have h3 : α * (12 * ε * l) = 48 * L := by
        rw [show α * (12 * ε * l) = 12 * ε * (α * l) by ring, hαl]
        field_simp; ring
      have : (k : ℝ) ≤ 196 * ρ * ε⁻¹ ^ 2 * L := by
        rw [hB2, le_div_iff₀ hq]; linarith
      rw [h0]; push_cast; linarith

end

section
open FracPackCover
open FracPackCover.Covering
open Finset

lemma e79_C1 {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hb : ∀ i, 0 < b i) (z : Fin n → ℝ) (α ε : ℝ) (hα : 0 < α) (hε : 0 < ε)
    (hl : 0 < lam A b z)
    (hw : (m : ℝ) ≤ α * ε * lam A b z * Real.exp (α * ε * lam A b z)) :
    C1 A b ε (lam A b z) (dualY A b α z) z := by
  unfold C1
  rw [e79_yAx_dualY, e79_ytb_dualY A b hb]
  obtain ⟨i0, hi0⟩ := e79_lam_attained A b z
  set l := lam A b z
  set r : Fin m → ℝ := fun i => rowVal A z i / b i with hr
  set e : Fin m → ℝ := fun i => Real.exp (-(α * r i)) with he
  set K := Real.exp (-(α * ((1 + ε) * l))) / α with hK
  have hK0 : 0 ≤ K := div_nonneg (Real.exp_pos _).le hα.le
  have hf : ∀ i, e i * r i - (1 + ε) * l * e i ≤ K := by
    intro i
    by_cases h : r i ≤ (1 + ε) * l
    · have : e i * r i - (1 + ε) * l * e i = e i * (r i - (1 + ε) * l) := by ring
      rw [this]
      have : e i * (r i - (1 + ε) * l) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith)
      linarith
    · push_neg at h
      set t := r i - (1 + ε) * l with ht
      have ht0 : 0 < t := by linarith
      have hei : e i = Real.exp (-(α * ((1 + ε) * l))) * Real.exp (-(α * t)) := by
        rw [he]; simp only; rw [← Real.exp_add]; congr 1; rw [ht]; ring
      have h1 : α * t ≤ Real.exp (α * t) := by linarith [Real.add_one_le_exp (α * t)]
      have h2 : Real.exp (-(α * t)) * Real.exp (α * t) = 1 := by
        rw [← Real.exp_add]; simp
      have h3 : Real.exp (-(α * t)) * (α * t) ≤ 1 := by
        calc Real.exp (-(α * t)) * (α * t) ≤ Real.exp (-(α * t)) * Real.exp (α * t) :=
              mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
          _ = 1 := h2
      have h4 : Real.exp (-(α * t)) * t ≤ 1 / α := by
        rw [le_div_iff₀ hα]; linarith
      have : e i * r i - (1 + ε) * l * e i =
          Real.exp (-(α * ((1 + ε) * l))) * (Real.exp (-(α * t)) * t) := by
        rw [hei, ht]; ring
      rw [this, hK, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
  have hsplit := (Finset.add_sum_erase (univ : Finset (Fin m))
    (fun i => e i * r i - (1 + ε) * l * e i) (mem_univ i0))
  have hrest : ∑ i ∈ univ.erase i0, (e i * r i - (1 + ε) * l * e i) ≤ m * K := by
    calc ∑ i ∈ univ.erase i0, (e i * r i - (1 + ε) * l * e i)
        ≤ ∑ _i ∈ univ.erase i0, K := sum_le_sum (fun i _ => hf i)
      _ ≤ ∑ _i : Fin m, K := sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
          (fun _ _ _ => hK0)
      _ = m * K := by simp
  have hri0 : r i0 = l := by rw [hr]; exact hi0.symm
  have hi0' : e i0 * r i0 - (1 + ε) * l * e i0 = -(ε * l * Real.exp (-(α * l))) := by
    rw [he]; simp only; rw [hri0]; ring
  set w := α * ε * l with hwdef
  have hw' : (m : ℝ) * Real.exp (-w) ≤ w := by
    have := mul_le_mul_of_nonneg_right hw (Real.exp_pos (-w)).le
    rwa [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at this
  have hmK : (m : ℝ) * K ≤ ε * l * Real.exp (-(α * l)) := by
    have hsplitE : Real.exp (-(α * ((1 + ε) * l))) = Real.exp (-(α * l)) * Real.exp (-w) := by
      rw [← Real.exp_add]; congr 1; rw [hwdef]; ring
    rw [hK, hsplitE]
    have hE0 := Real.exp_pos (-(α * l))
    calc (m : ℝ) * (Real.exp (-(α * l)) * Real.exp (-w) / α)
        = Real.exp (-(α * l)) * ((m : ℝ) * Real.exp (-w)) / α := by ring
      _ ≤ Real.exp (-(α * l)) * w / α :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw' hE0.le) hα.le
      _ = ε * l * Real.exp (-(α * l)) := by rw [hwdef]; field_simp
  have htot : ∑ i, (e i * r i - (1 + ε) * l * e i) ≤ 0 := by
    have hs2 : ∑ i, (e i * r i - (1 + ε) * l * e i) = (e i0 * r i0 - (1 + ε) * l * e i0) +
        ∑ i ∈ univ.erase i0, (e i * r i - (1 + ε) * l * e i) := hsplit.symm
    rw [hs2, hi0']; linarith
  rw [sum_sub_distrib, ← mul_sum] at htot
  linarith

lemma e79_L31 {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hdata : IsCoveringData A b P)
    (ε : ℝ) (hε : 0 < ε) (hε6 : ε ≤ 1 / 6)
    (z : Fin n → ℝ) (y : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i) (hyb : 0 < ytb b y)
    (xt : Fin n → ℝ) (hmax : ∀ x' ∈ P, yAx A y x' ≤ yAx A y xt)
    (hC1 : C1 A b ε (lam A b z) y z) (hC2 : C2 A b ε y z (yAx A y xt)) :
    (lam A b z ≤ 1 - 3 * ε → ¬ ∃ x' ∈ P, ∀ i, b i ≤ rowVal A x' i) ∧
    (1 - 3 * ε ≤ lam A b z → ∀ x' ∈ P, (1 - 3 * ε) * lam A b x' ≤ lam A b z) := by
  have key : ∀ x' ∈ P, (1 - ε) * lam A b x' ≤ (1 + ε) * lam A b z + ε := by
    intro x' hx'
    have h1 : lam A b x' * ytb b y ≤ yAx A y x' := by
      unfold ytb yAx; rw [mul_sum]; apply sum_le_sum; intro i _
      have h := e79_lam_le A b x' i
      have hb := hdata.2.1 i
      rw [le_div_iff₀ hb] at h
      calc lam A b x' * (y i * b i) = y i * (lam A b x' * b i) := by ring
        _ ≤ y i * rowVal A x' i := mul_le_mul_of_nonneg_left h (hy i)
    have h2 := hmax x' hx'
    unfold C1 at hC1; unfold C2 at hC2
    have h3 : (1 - ε) * (lam A b x' * ytb b y) ≤ (1 - ε) * yAx A y xt :=
      mul_le_mul_of_nonneg_left (le_trans h1 h2) (by linarith)
    have h4 : ((1 - ε) * lam A b x') * ytb b y ≤ ((1 + ε) * lam A b z + ε) * ytb b y := by
      nlinarith
    exact le_of_mul_le_mul_right h4 hyb
  constructor
  · rintro hl ⟨x', hx', hb'⟩
    have h1 : 1 ≤ lam A b x' := e79_le_lam (fun i => by
      rw [le_div_iff₀ (hdata.2.1 i)]; linarith [hb' i])
    have := key x' hx'
    nlinarith
  · intro hl x' hx'
    have h := key x' hx'
    have h3 : 0 ≤ 1 - 3 * ε := by linarith
    have h5 : (1 - 3 * ε) * ((1 - ε) * lam A b x') ≤ (1 - 3 * ε) * ((1 + ε) * lam A b z + ε) :=
      mul_le_mul_of_nonneg_left h h3
    have h6 : (1 - 3 * ε) * ((1 + ε) * lam A b z + ε) ≤ (1 - ε) * lam A b z := by
      have hX : (1 - ε) * lam A b z - (1 - 3 * ε) * ((1 + ε) * lam A b z + ε) =
          ε * (lam A b z * (1 + 3 * ε) - (1 - 3 * ε)) := by ring
      have hY : 0 ≤ lam A b z * (1 + 3 * ε) - (1 - 3 * ε) := by nlinarith
      nlinarith [mul_nonneg hε.le hY]
    have h7 : (1 - ε) * ((1 - 3 * ε) * lam A b x') ≤ (1 - ε) * lam A b z := by nlinarith
    exact le_of_mul_le_mul_left h7 (by linarith)

end

section
open FracPackCover
open FracPackCover.Covering
open Finset
variable {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (orc : (Fin m → ℝ) → (Fin n → ℝ)) (ρ ε : ℝ) (x : Fin n → ℝ)

theorem e79_ic_result (hdata : IsCoveringData A b P) (hρ : WidthBound A b P ρ)
    (horc : IsMaxOracle A P orc) (hx : x ∈ P)
    (hlam : 0 < lam A b x) (hε : 0 < ε) (hε6 : ε ≤ 1 / 6) :
    ∃ x' : Fin n → ℝ, ∃ T c : ℕ, c ≤ T + 1 ∧
      (∀ F, T < F → improveCover A b orc ρ ε x F = some (x', c)) ∧
      (T : ℝ) ≤ 1 + 20 * ρ * ε⁻¹ ^ 3 * Real.log (4 * m * ε⁻¹) ∧
      (ε ≤ 1 / 12 → (∀ x'' ∈ P, (1 - 6 * ε) * lam A b x'' ≤ lam A b x) →
        (T : ℝ) ≤ 1 + 196 * ρ * ε⁻¹ ^ 2 * Real.log (4 * m * ε⁻¹)) ∧
      x' ∈ P ∧ 3 * lam A b x / 4 ≤ lam A b x' ∧
      (lam A b x' ≤ 2 * lam A b x →
        (lam A b x' ≤ 1 - 3 * ε → ¬ ∃ x'' ∈ P, ∀ i, b i ≤ rowVal A x'' i) ∧
        (1 - 3 * ε ≤ lam A b x' → ∀ x'' ∈ P, (1 - 3 * ε) * lam A b x'' ≤ lam A b x')) := by
  have hε1 : ε < 1 := by linarith
  obtain ⟨T, c, hc, hF, hreach, hnt, hT1, hT2⟩ :=
    e79_ic_spec A b P orc ρ ε x hdata hρ horc hx hlam hε hε1
  obtain ⟨hα, -, -, -, -, hαl⟩ := e79_params A b P ρ ε x hdata hρ hx hlam hε hε1
  obtain ⟨hL, -, hexpL⟩ := e79_log_ge (m := m) ε hε hε1
  have hmem := e79_iter_mem A b P orc ρ ε x hdata hρ horc hx hlam hε hε1 T
  have hge := e79_lam_ge A b P orc ρ ε x hdata hρ horc hx hlam hε hε1 T hreach
  refine ⟨_, T, c, hc, hF, hT1, hT2, hmem, hge, fun h2 => ?_⟩
  set α := coverAlpha m ε (lam A b x)
  set x' := coverIterate A b orc ρ ε x T
  have hC2 : C2 A b ε (dualY A b α x') x' (yAx A (dualY A b α x') (orc (dualY A b α x'))) := by
    by_contra h; exact hnt ⟨h2, h⟩
  have hy := e79_dualY_nonneg A b hdata.2.1 α x'
  have hl' : 0 < lam A b x' := by linarith
  have hw3 : 3 * Real.log (4 * m * ε⁻¹) ≤ α * ε * lam A b x' := by
    have : α * ε * lam A b x' ≥ α * ε * (3 * lam A b x / 4) :=
      mul_le_mul_of_nonneg_left hge (by positivity)
    have h' : α * ε * (3 * lam A b x / 4) = 3 / 4 * ε * (α * lam A b x) := by ring
    rw [h', hαl] at this
    have : 3 / 4 * ε * (4 * ε⁻¹ * Real.log (4 * ↑m * ε⁻¹)) = 3 * Real.log (4 * m * ε⁻¹) := by
      field_simp
    linarith
  have hm1 : (m : ℝ) ≤ 4 * m * ε⁻¹ := by
    have hm : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
    have hei : 1 < ε⁻¹ := by rw [lt_inv_comm₀ one_pos hε]; simpa using hε1
    nlinarith
  have hw : (m : ℝ) ≤ α * ε * lam A b x' * Real.exp (α * ε * lam A b x') := by
    have he1 : (m : ℝ) ≤ Real.exp (α * ε * lam A b x') := by
      calc (m : ℝ) ≤ 4 * m * ε⁻¹ := hm1
        _ = Real.exp (Real.log (4 * m * ε⁻¹)) := hexpL.symm
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    have : 1 ≤ α * ε * lam A b x' := by linarith
    nlinarith [Real.exp_pos (α * ε * lam A b x')]
  have hC1 := e79_C1 A b hdata.2.1 x' α ε hα hε hl' hw
  have hyb : 0 < ytb b (dualY A b α x') := by
    rw [e79_ytb_dualY A b hdata.2.1]
    exact Finset.sum_pos (fun i _ => Real.exp_pos _) univ_nonempty
  exact e79_L31 A b P hdata ε hε hε6 x' _ hy hyb _ (horc _ hy).2 hC1 hC2

end

section
open FracPackCover
open FracPackCover.Covering
open Finset
variable {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (orc : (Fin m → ℝ) → (Fin n → ℝ)) (ρ ε₀ : ℝ)

def E79Correct (out : CoverOutcome n) : Prop :=
  (∀ x, out = .approx x → x ∈ P ∧ ∀ i, (1 - ε₀) * b i ≤ rowVal A x i) ∧
  (out = .infeasible → ¬ ∃ x' ∈ P, ∀ i, b i ≤ rowVal A x' i)

lemma e79_ok_approx (hdata : IsCoveringData A b P) (x : Fin n → ℝ) (hx : x ∈ P)
    (h : 1 - ε₀ ≤ lam A b x) : E79Correct A b P ε₀ (.approx x) := by
  refine ⟨fun x' hx' => ?_, fun h' => absurd h' (by simp)⟩
  obtain rfl := CoverOutcome.approx.inj hx'
  refine ⟨hx, fun i => ?_⟩
  have h1 := e79_lam_le A b x i
  rw [le_div_iff₀ (hdata.2.1 i)] at h1
  calc (1 - ε₀) * b i ≤ lam A b x * b i := mul_le_mul_of_nonneg_right h (hdata.2.1 i).le
    _ ≤ _ := h1

lemma e79_ok_inf (h : ¬ ∃ x' ∈ P, ∀ i, b i ≤ rowVal A x' i) :
    E79Correct A b P ε₀ (CoverOutcome.infeasible) :=
  ⟨fun x hx => absurd hx (by simp), fun _ => h⟩

lemma e79_scaleEps_inv (k : ℕ) : (scaleEps k)⁻¹ = 6 * 2 ^ k := by
  apply inv_eq_of_mul_eq_one_right
  unfold scaleEps; rw [one_div_pow]; field_simp

theorem e79_scaling (hdata : IsCoveringData A b P) (hρ : WidthBound A b P ρ)
    (horc : IsMaxOracle A P orc) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1) (K : ℕ)
    (hK : ∀ k : ℕ, ε₀ < (1 / 2 : ℝ) ^ k → k ≤ K) (IF : ℕ)
    (hIF : ∀ k : ℕ, ε₀ < (1 / 2 : ℝ) ^ k →
      2 + 196 * ρ * Real.log (24 * m * ε₀⁻¹) * 36 * 4 ^ k ≤ (IF : ℝ)) :
    ∀ (f k : ℕ) (x : Fin n → ℝ) (calls : ℕ), 1 ≤ k → K + 1 ≤ k + f → x ∈ P → 1 / 2 < lam A b x →
      (∀ x'' ∈ P, (1 - (1 / 2 : ℝ) ^ k) * lam A b x'' ≤ lam A b x) → ε₀ < (1 / 2 : ℝ) ^ k →
      ∃ out c, scalingPhases A b orc ρ ε₀ IF f k x calls = some (out, calls + c) ∧
        E79Correct A b P ε₀ out ∧
        (c : ℝ) ≤ 2 * ((K : ℝ) + 1 - ((k : ℕ) : ℝ)) +
          196 * ρ * Real.log (24 * m * ε₀⁻¹) * 12 * (4 ^ (K + 1) - 4 ^ k) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  have hei : 1 < ε₀⁻¹ := by rw [lt_inv_comm₀ one_pos hε₀]; simpa using hε₀1
  have hL0 : 0 ≤ Real.log (24 * m * ε₀⁻¹) := Real.log_nonneg (by nlinarith)
  have hρ0 := hρ.1
  intro f
  induction f with
  | zero =>
    intro k x calls hk hKf _ _ _ hε
    have := hK k hε; omega
  | succ f ih =>
    intro k x calls hk hKf hx hl hopt hεk
    have hkK := hK k hεk
    have hs0 : 0 < scaleEps k := by unfold scaleEps; positivity
    have hpk : (1 / 2 : ℝ) ^ k ≤ (1 / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
    have h6 : 6 * scaleEps k = (1 / 2 : ℝ) ^ k := by unfold scaleEps; ring
    have h3 : 3 * scaleEps k = (1 / 2 : ℝ) ^ (k + 1) := by unfold scaleEps; ring
    have hs12 : scaleEps k ≤ 1 / 12 := by norm_num at hpk; linarith
    obtain ⟨x', T, c, hc, hF, -, hT2, hx'P, hge, hfin⟩ :=
      e79_ic_result A b P orc ρ (scaleEps k) x hdata hρ horc hx (by linarith) hs0 (by linarith)
    have hopt' : ∀ x'' ∈ P, (1 - 6 * scaleEps k) * lam A b x'' ≤ lam A b x := by
      rw [h6]; exact hopt
    have hT := hT2 hs12 hopt'
    have hinv := e79_scaleEps_inv k
    have h2k : (2 : ℝ) ^ k < ε₀⁻¹ := by
      have : ε₀ < ((2 : ℝ) ^ k)⁻¹ := by rw [← one_div, ← one_div_pow]; exact hεk
      exact (lt_inv_comm₀ hε₀ (by positivity)).mp this
    have hlog : Real.log (4 * m * (scaleEps k)⁻¹) ≤ Real.log (24 * m * ε₀⁻¹) := by
      rw [hinv]; apply Real.log_le_log (by positivity); nlinarith
    have hsq : ((scaleEps k)⁻¹) ^ 2 = 36 * 4 ^ k := by
      rw [hinv, mul_pow, ← pow_mul, mul_comm k 2, pow_mul]; norm_num
    have hTB : (T : ℝ) + 1 ≤ 2 + 196 * ρ * Real.log (24 * m * ε₀⁻¹) * 36 * 4 ^ k := by
      have h0 : 0 ≤ 196 * ρ * (36 * 4 ^ k) := by positivity
      have := mul_le_mul_of_nonneg_left hlog h0
      rw [hsq] at hT
      nlinarith
    have hTIF : T < IF := by
      have := hIF k hεk
      exact_mod_cast (by linarith : (T : ℝ) < IF)
    have hcB : (c : ℝ) ≤ 2 + 196 * ρ * Real.log (24 * m * ε₀⁻¹) * 36 * 4 ^ k := by
      have : (c : ℝ) ≤ T + 1 := by exact_mod_cast hc
      linarith
    have hΦnext : 0 ≤ 2 * ((K : ℝ) + 1 - ((k + 1 : ℕ) : ℝ)) +
        196 * ρ * Real.log (24 * m * ε₀⁻¹) * 12 * (4 ^ (K + 1) - 4 ^ (k + 1)) := by
      have h1 : ((k + 1 : ℕ) : ℝ) ≤ (K : ℝ) + 1 := by exact_mod_cast (by omega : k + 1 ≤ K + 1)
      have h2 : (4 : ℝ) ^ (k + 1) ≤ 4 ^ (K + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have : 0 ≤ 196 * ρ * Real.log (24 * m * ε₀⁻¹) * 12 := by positivity
      nlinarith [mul_nonneg this (sub_nonneg.mpr h2)]
    have hΦeq : 2 * ((K : ℝ) + 1 - ((k : ℕ) : ℝ)) +
        196 * ρ * Real.log (24 * m * ε₀⁻¹) * 12 * (4 ^ (K + 1) - 4 ^ k) =
        (2 + 196 * ρ * Real.log (24 * m * ε₀⁻¹) * 36 * 4 ^ k) +
        (2 * ((K : ℝ) + 1 - ((k + 1 : ℕ) : ℝ)) +
          196 * ρ * Real.log (24 * m * ε₀⁻¹) * 12 * (4 ^ (K + 1) - 4 ^ (k + 1))) := by
      push_cast; ring
    rw [scalingPhases, hF IF hTIF]
    dsimp only
    split_ifs with h1 h2
    · exact ⟨_, c, rfl, e79_ok_approx A b P ε₀ hdata x' hx'P h1, by rw [hΦeq]; linarith⟩
    · exact ⟨_, c, rfl, e79_ok_inf A b P ε₀ ((hfin h2.1).1 h2.2), by rw [hΦeq]; linarith⟩
    · push_neg at h1
      have hle : lam A b x' ≤ 2 * lam A b x := by
        by_contra hc'; push_neg at hc'; linarith
      have hgt : 1 - 3 * scaleEps k < lam A b x' := by
        by_contra hc'; push_neg at hc'; exact h2 ⟨hle, hc'⟩
      obtain ⟨out, c', heq, hok, hc'⟩ := ih (k + 1) x' (calls + c) (by omega) (by omega) hx'P
        (by linarith)
        (by intro x'' hx''; rw [← h3]; exact (hfin hle).2 hgt.le x'' hx'')
        (by rw [← h3]; linarith)
      refine ⟨out, c + c', by rw [heq, add_assoc], hok, ?_⟩
      push_cast at hc' ⊢
      rw [hΦeq]; push_cast; linarith

theorem e79_first (hdata : IsCoveringData A b P) (hρ : WidthBound A b P ρ)
    (horc : IsMaxOracle A P orc) (hε₀ : 0 < ε₀) (IF : ℕ) (S : ℝ) (hS0 : 0 ≤ S)
    (hIF1 : 2 + 4320 * ρ * Real.log (24 * m) ≤ (IF : ℝ))
    (hS : ∀ (x : Fin n → ℝ) (calls : ℕ), x ∈ P → 1 / 2 < lam A b x →
      (∀ x'' ∈ P, (1 - (1 / 2 : ℝ) ^ 1) * lam A b x'' ≤ lam A b x) → ε₀ < (1 / 2 : ℝ) ^ 1 →
      ∃ out c, scalingPhases A b orc ρ ε₀ IF IF 1 x calls = some (out, calls + c) ∧
        E79Correct A b P ε₀ out ∧ (c : ℝ) ≤ S) :
    ∀ (j f : ℕ) (x : Fin n → ℝ) (calls : ℕ), j + 1 ≤ f → x ∈ P → 0 < lam A b x → 1 ≤ 2 ^ j * lam A b x →
      ∃ out c, firstPhase A b orc ρ ε₀ IF f x calls = some (out, calls + c) ∧
        E79Correct A b P ε₀ out ∧
        (c : ℝ) ≤ ((j : ℝ) + 1) * (2 + 4320 * ρ * Real.log (24 * m)) + S := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  have hρ0 := hρ.1
  have hlog : 0 ≤ Real.log (24 * m) := Real.log_nonneg (by linarith)
  have hG : 0 ≤ 2 + 4320 * ρ * Real.log (24 * m) := by positivity
  intro j
  induction j with
  | zero =>
    intro f x calls hf hx hl h1
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rw [pow_zero, one_mul] at h1
    rw [firstPhase, if_pos h1]
    exact ⟨_, 0, rfl, e79_ok_approx A b P ε₀ hdata x hx (by linarith), by push_cast; nlinarith⟩
  | succ j ih =>
    intro f x calls hf hx hl h1
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have hjG : 0 ≤ ((j : ℝ) + 1) * (2 + 4320 * ρ * Real.log (24 * m)) := by positivity
    rw [firstPhase]
    by_cases hx1 : 1 ≤ lam A b x
    · rw [if_pos hx1]
      exact ⟨_, 0, rfl, e79_ok_approx A b P ε₀ hdata x hx (by linarith),
        by push_cast; nlinarith⟩
    rw [if_neg hx1]
    obtain ⟨x', T, c, hc, hF, hT1, -, hx'P, hge, hfin⟩ :=
      e79_ic_result A b P orc ρ (1 / 6) x hdata hρ horc hx hl (by norm_num) (by norm_num)
    have hT1' : (T : ℝ) + 1 ≤ 2 + 4320 * ρ * Real.log (24 * m) := by
      have e1 : (1 / 6 : ℝ)⁻¹ = 6 := by norm_num
      have e2 : 4 * (m : ℝ) * 6 = 24 * m := by ring
      rw [e1, e2] at hT1
      have e3 : (20 : ℝ) * ρ * 6 ^ 3 * Real.log (24 * m) = 4320 * ρ * Real.log (24 * m) := by
        ring
      linarith
    have hTIF : T < IF := by exact_mod_cast (by linarith : (T : ℝ) < IF)
    have hcG : (c : ℝ) ≤ 2 + 4320 * ρ * Real.log (24 * m) := by
      have : (c : ℝ) ≤ T + 1 := by exact_mod_cast hc
      linarith
    rw [hF IF hTIF]
    dsimp only
    split_ifs with h2 h3 h4 h5
    · exact ⟨_, c, rfl, e79_ok_approx A b P ε₀ hdata x' hx'P (by linarith),
        by push_cast; linarith⟩
    · have hpj : (0 : ℝ) < 2 ^ j := by positivity
      have := mul_le_mul_of_nonneg_left h3.le hpj.le
      rw [pow_succ] at h1
      obtain ⟨out, c', heq, hok, hc'⟩ := ih f' x' (calls + c) (by omega) hx'P (by linarith)
        (by nlinarith)
      exact ⟨out, c + c', by rw [heq, add_assoc], hok, by push_cast; linarith⟩
    · push_neg at h3
      exact ⟨_, c, rfl, e79_ok_inf A b P ε₀ ((hfin h3).1 (by norm_num; linarith)),
        by push_cast; linarith⟩
    · exact ⟨_, c, rfl, e79_ok_approx A b P ε₀ hdata x' hx'P (by linarith),
        by push_cast; linarith⟩
    · push_neg at h3 h4 h5
      obtain ⟨out, c', heq, hok, hc'⟩ := hS x' (calls + c) hx'P h4
        (by
          intro x'' hx''
          have := (hfin h3).2 (by norm_num; linarith) x'' hx''
          norm_num at this ⊢; linarith)
        (by norm_num; linarith)
      exact ⟨out, c + c', by rw [heq, add_assoc], hok, by push_cast; linarith⟩

end

section
open FracPackCover
open FracPackCover.Covering
open Finset

theorem e79_thm37 {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hdata : IsCoveringData A b P) (ρ : ℝ) (hρ : WidthBound A b P ρ)
    (orc : (Fin m → ℝ) → (Fin n → ℝ)) (horc : IsMaxOracle A P orc)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1) :
    let N : ℝ := (m : ℝ) + ((⌈Real.logb 2 m⌉₊ : ℝ) + 1) * (2 + 4320 * ρ * Real.log (24 * m)) +
      2 * (⌈Real.logb 2 ε₀⁻¹⌉₊ : ℝ) + 9408 * ρ * ε₀⁻¹ ^ 2 * Real.log (24 * m * ε₀⁻¹)
    ∃ out : CoverOutcome n, ∃ c : ℕ,
      coverAlgorithm A b orc ρ ε₀ ⌈N⌉₊ = some (out, c) ∧ (c : ℝ) ≤ N ∧
      (∀ x, out = .approx x → x ∈ P ∧ ∀ i, (1 - ε₀) * b i ≤ rowVal A x i) ∧
      (out = .infeasible → ¬ ∃ x' ∈ P, ∀ i, b i ≤ rowVal A x' i) := by
  intro N
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  have hm0 : (0 : ℝ) < m := by linarith
  have hρ0 := hρ.1
  have hei : 1 < ε₀⁻¹ := by rw [lt_inv_comm₀ one_pos hε₀]; simpa using hε₀1
  have hlog24 : 0 ≤ Real.log (24 * m) := Real.log_nonneg (by linarith)
  have hL0 : 0 ≤ Real.log (24 * m * ε₀⁻¹) := Real.log_nonneg (by nlinarith)
  have hG : 2 ≤ 2 + 4320 * ρ * Real.log (24 * m) := by
    have : 0 ≤ 4320 * ρ * Real.log (24 * m) := by positivity
    linarith
  have hexK : ∃ j : ℕ, (1 / 2 : ℝ) ^ (j + 1) ≤ ε₀ := by
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hε₀ (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨j, le_trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ j)) hj.le⟩
  classical
  have hK : ∀ k : ℕ, ε₀ < (1 / 2 : ℝ) ^ k → k ≤ Nat.find hexK := by
    intro k hk; by_contra hc; push_neg at hc
    have h1 := Nat.find_spec hexK
    have h2 : (1 / 2 : ℝ) ^ k ≤ (1 / 2) ^ (Nat.find hexK + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hc
    linarith
  have hKlt : ε₀ < (1 / 2 : ℝ) ^ (Nat.find hexK) := by
    rcases Nat.eq_zero_or_pos (Nat.find hexK) with h0 | h0
    · rw [h0]; simpa using hε₀1
    · have := Nat.find_min hexK (show Nat.find hexK - 1 < Nat.find hexK by omega)
      push_neg at this
      rwa [show Nat.find hexK - 1 + 1 = Nat.find hexK by omega] at this
  set K := Nat.find hexK with hKdef
  have h2K : (2 : ℝ) ^ K < ε₀⁻¹ := by
    have : ε₀ < ((2 : ℝ) ^ K)⁻¹ := by rw [← one_div, ← one_div_pow]; exact hKlt
    exact (lt_inv_comm₀ hε₀ (by positivity)).mp this
  have h4K : (4 : ℝ) ^ K ≤ ε₀⁻¹ ^ 2 := by
    have : (4 : ℝ) ^ K = ((2 : ℝ) ^ K) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this]; exact pow_le_pow_left₀ (by positivity) h2K.le 2
  have hKceil : (K : ℝ) ≤ (⌈Real.logb 2 ε₀⁻¹⌉₊ : ℝ) := by
    have : (K : ℝ) < Real.logb 2 ε₀⁻¹ := by
      rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity), Real.rpow_natCast]; exact h2K
    linarith [Nat.le_ceil (Real.logb 2 ε₀⁻¹)]
  set L₀ := Real.log (24 * m * ε₀⁻¹) with hL₀def
  set G := 2 + 4320 * ρ * Real.log (24 * m) with hGdef
  set J := ⌈Real.logb 2 m⌉₊ with hJdef
  set Φ1 : ℝ := 2 * ((K : ℝ) + 1 - ((1 : ℕ) : ℝ)) + 196 * ρ * L₀ * 12 * (4 ^ (K + 1) - 4 ^ 1)
    with hΦ1def
  have hp : 0 ≤ ρ * L₀ := by positivity
  have hΦ1 : Φ1 ≤ 2 * (⌈Real.logb 2 ε₀⁻¹⌉₊ : ℝ) + 9408 * ρ * ε₀⁻¹ ^ 2 * L₀ := by
    have : 196 * ρ * L₀ * 12 * (4 ^ (K + 1) - 4 ^ 1) ≤ 9408 * ρ * ε₀⁻¹ ^ 2 * L₀ := by
      rw [pow_succ]
      nlinarith [mul_le_mul_of_nonneg_left h4K hp]
    rw [hΦ1def]; push_cast; linarith
  have hΦ1nn : 0 ≤ Φ1 := by
    have h4 : (4 : ℝ) ^ 1 ≤ 4 ^ (K + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have : 0 ≤ 196 * ρ * L₀ * 12 := by positivity
    rw [hΦ1def]; push_cast
    nlinarith [mul_nonneg this (sub_nonneg.mpr h4)]
  have hNdef : N = (m : ℝ) + ((J : ℝ) + 1) * G + 2 * (⌈Real.logb 2 ε₀⁻¹⌉₊ : ℝ) +
      9408 * ρ * ε₀⁻¹ ^ 2 * L₀ := rfl
  have hJG : 2 * ((J : ℝ) + 1) ≤ ((J : ℝ) + 1) * G := by nlinarith
  have hS9 : 0 ≤ 9408 * ρ * ε₀⁻¹ ^ 2 * L₀ := by positivity
  have hceil := Nat.le_ceil N
  have hIF : ∀ k : ℕ, ε₀ < (1 / 2 : ℝ) ^ k →
      2 + 196 * ρ * L₀ * 36 * 4 ^ k ≤ ((⌈N⌉₊ : ℕ) : ℝ) := by
    intro k hk
    have hkK := hK k hk
    have h4k : (4 : ℝ) ^ k ≤ ε₀⁻¹ ^ 2 :=
      le_trans (pow_le_pow_right₀ (by norm_num) hkK) h4K
    have : 196 * ρ * L₀ * 36 * 4 ^ k ≤ 9408 * ρ * ε₀⁻¹ ^ 2 * L₀ := by
      have h0 : (0 : ℝ) ≤ 4 ^ k := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h4k hp, mul_nonneg hp h0]
    linarith
  have hIF1 : G ≤ ((⌈N⌉₊ : ℕ) : ℝ) := by nlinarith
  have hfuelS : K + 1 ≤ 1 + ⌈N⌉₊ := by
    have : (K : ℝ) ≤ (⌈N⌉₊ : ℝ) := by linarith
    exact_mod_cast (by linarith : (K : ℝ) + 1 ≤ 1 + (⌈N⌉₊ : ℝ))
  have hS : ∀ (x : Fin n → ℝ) (calls : ℕ), x ∈ P → 1 / 2 < lam A b x →
      (∀ x'' ∈ P, (1 - (1 / 2 : ℝ) ^ 1) * lam A b x'' ≤ lam A b x) → ε₀ < (1 / 2 : ℝ) ^ 1 →
      ∃ out c, scalingPhases A b orc ρ ε₀ ⌈N⌉₊ ⌈N⌉₊ 1 x calls = some (out, calls + c) ∧
        E79Correct A b P ε₀ out ∧ (c : ℝ) ≤ Φ1 :=
    fun x calls hx hl hopt hε =>
      e79_scaling A b P orc ρ ε₀ hdata hρ horc hε₀ hε₀1 K hK ⌈N⌉₊ hIF ⌈N⌉₊ 1 x calls le_rfl
        hfuelS hx hl hopt hε
  obtain ⟨hinit1, hinit2⟩ := FracPackCover.Covering.lemma_3_6 A b P hdata orc horc
  unfold coverAlgorithm
  cases hinit : initCover A b orc with
  | none =>
    refine ⟨.infeasible, m, rfl, by linarith, fun x hx => absurd hx (by simp), fun _ => hinit1 hinit⟩
  | some x =>
    obtain ⟨hxP, hxb⟩ := hinit2 x hinit
    have hlx : 1 / (m : ℝ) ≤ lam A b x := e79_le_lam (fun i => by
      rw [le_div_iff₀ (hdata.2.1 i)]; exact hxb i)
    have hmJ : (m : ℝ) ≤ 2 ^ J := by
      have : Real.logb 2 m ≤ J := Nat.le_ceil _
      rw [Real.logb_le_iff_le_rpow (by norm_num) hm0, Real.rpow_natCast] at this
      exact this
    have h2J : 1 ≤ 2 ^ J * lam A b x := by
      have h1 : (2 : ℝ) ^ J * (1 / m) ≤ 2 ^ J * lam A b x :=
        mul_le_mul_of_nonneg_left hlx (by positivity)
      have h2 : 1 ≤ (2 : ℝ) ^ J * (1 / m) := by
        rw [mul_one_div, le_div_iff₀ hm0]; linarith
      linarith
    have hfuelF : J + 1 ≤ ⌈N⌉₊ := by
      exact_mod_cast (by nlinarith : (J : ℝ) + 1 ≤ (⌈N⌉₊ : ℝ))
    obtain ⟨out, c, heq, hok, hc⟩ := e79_first A b P orc ρ ε₀ hdata hρ horc hε₀ ⌈N⌉₊ Φ1 hΦ1nn
      hIF1 hS J ⌈N⌉₊ x m hfuelF hxP (by
        have : (0 : ℝ) < 1 / m := by positivity
        linarith) h2J
    refine ⟨out, m + c, heq, ?_, hok.1, hok.2⟩
    push_cast
    rw [hNdef]
    linarith

end

section
open FracPackCover.Covering

theorem solution {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hdata : IsCoveringData A b P) (ρ : ℝ) (hρ : WidthBound A b P ρ)
    (orc : (Fin m → ℝ) → (Fin n → ℝ)) (horc : IsMaxOracle A P orc)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1) :
    let N : ℝ := (m : ℝ) + ((⌈Real.logb 2 m⌉₊ : ℝ) + 1) * (2 + 4320 * ρ * Real.log (24 * m)) +
      2 * (⌈Real.logb 2 ε₀⁻¹⌉₊ : ℝ) + 9408 * ρ * ε₀⁻¹ ^ 2 * Real.log (24 * m * ε₀⁻¹)
    ∃ out : CoverOutcome n, ∃ c : ℕ,
      coverAlgorithm A b orc ρ ε₀ ⌈N⌉₊ = some (out, c) ∧ (c : ℝ) ≤ N ∧
      (∀ x, out = .approx x → x ∈ P ∧ ∀ i, (1 - ε₀) * b i ≤ rowVal A x i) ∧
      (out = .infeasible → ¬ ∃ x' ∈ P, ∀ i, b i ≤ rowVal A x' i) := by
  exact e79_thm37 A b P hdata ρ hρ orc horc ε₀ hε₀ hε₀1

end
