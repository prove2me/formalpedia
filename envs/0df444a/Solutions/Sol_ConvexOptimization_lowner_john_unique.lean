-- Prove2me | solution 1 for ConvexOptimization.lowner_john_unique
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-16T05:38:05.497514+00:00
-- url     : https://prove2.me/submissions/ee7948df-0bae-4853-8984-9a76b72adcef

import Mathlib
import Definitions.Def_ConvexOptimization_ellipsoidBody
import Definitions.Def_ConvexOptimization_IsLownerJohn

open scoped RealInnerProductSpace ENNReal MatrixOrder
open MeasureTheory
open Matrix Unitary
open ConvexOptimization

namespace LJUAux

variable {nn : ℕ}

/-! ### Elementary dot-product algebra -/

theorem dot_expand (p q : Fin nn → ℝ) :
    (p + q) ⬝ᵥ (p + q) = p ⬝ᵥ p + 2 * (p ⬝ᵥ q) + q ⬝ᵥ q := by
  simp only [dotProduct, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem dot_expand_sub (p q : Fin nn → ℝ) :
    (p - q) ⬝ᵥ (p - q) = p ⬝ᵥ p - 2 * (p ⬝ᵥ q) + q ⬝ᵥ q := by
  simp only [dotProduct, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem dot_smul_self (c : ℝ) (u : Fin nn → ℝ) : (c • u) ⬝ᵥ (c • u) = c ^ 2 * (u ⬝ᵥ u) := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem dotProduct_self_nonneg (v : Fin nn → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem dotProduct_self_pos {v : Fin nn → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  rw [dotProduct]
  refine Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
  exact mul_self_pos.mpr (by simpa using hi)

/-- The midpoint of two points of the unit ball lies strictly inside, by the amount
prescribed by the parallelogram law. -/
theorem avg_dot_le (u v : Fin nn → ℝ) (hu : u ⬝ᵥ u ≤ 1) (hv : v ⬝ᵥ v ≤ 1) :
    ((2 : ℝ)⁻¹ • (u + v)) ⬝ᵥ ((2 : ℝ)⁻¹ • (u + v))
      ≤ 1 - (4 : ℝ)⁻¹ * ((u - v) ⬝ᵥ (u - v)) := by
  rw [dot_smul_self, dot_expand, dot_expand_sub]
  ring_nf
  linarith

theorem smul_mulVec (c : ℝ) (A : Matrix (Fin nn) (Fin nn) ℝ) (v : Fin nn → ℝ) :
    (c • A) *ᵥ v = c • (A *ᵥ v) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem dot_mulVec_left (A : Matrix (Fin nn) (Fin nn) ℝ) (p q : Fin nn → ℝ) :
    (A *ᵥ p) ⬝ᵥ q = p ⬝ᵥ (Aᵀ *ᵥ q) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-! ### Strict monotonicity of finite products -/

theorem prod_lt_prod_pos {ι : Type*} [Fintype ι] [DecidableEq ι] (f g : ι → ℝ)
    (hf : ∀ i, 0 < f i) (hle : ∀ i, f i ≤ g i) (i₀ : ι) (hlt : f i₀ < g i₀) :
    ∏ i, f i < ∏ i, g i := by
  classical
  rw [← Finset.prod_erase_mul _ f (Finset.mem_univ i₀),
    ← Finset.prod_erase_mul _ g (Finset.mem_univ i₀)]
  have h1 : 0 < ∏ i ∈ Finset.univ.erase i₀, f i := Finset.prod_pos fun i _ => hf i
  have h2 : ∏ i ∈ Finset.univ.erase i₀, f i ≤ ∏ i ∈ Finset.univ.erase i₀, g i :=
    Finset.prod_le_prod (fun i _ => (hf i).le) (fun i _ => hle i)
  have h3 : 0 < g i₀ := lt_of_lt_of_le (hf i₀) (hle i₀)
  calc (∏ i ∈ Finset.univ.erase i₀, f i) * f i₀
      < (∏ i ∈ Finset.univ.erase i₀, f i) * g i₀ := by
        exact mul_lt_mul_of_pos_left hlt h1
    _ ≤ (∏ i ∈ Finset.univ.erase i₀, g i) * g i₀ := mul_le_mul_of_nonneg_right h2 h3.le

/-! ### Determinants under unitary conjugation, and strict concavity of `log det` -/

theorem det_conj (U : Matrix.unitaryGroup (Fin nn) ℝ) (X : Matrix (Fin nn) (Fin nn) ℝ) :
    (conjStarAlgAut ℝ (Matrix (Fin nn) (Fin nn) ℝ) U X).det = X.det := by
  have h : (U : Matrix (Fin nn) (Fin nn) ℝ) * star (U : Matrix (Fin nn) (Fin nn) ℝ) = 1 := U.2.2
  have hd : (U : Matrix (Fin nn) (Fin nn) ℝ).det
      * (star (U : Matrix (Fin nn) (Fin nn) ℝ)).det = 1 := by
    rw [← Matrix.det_mul, h, Matrix.det_one]
  simp only [conjStarAlgAut_apply, Matrix.det_mul]
  linear_combination X.det * hd

/-- **Strict concavity of the determinant along the positive definite cone.**
If `M ≻ 0` has `det M = 1` and `det ((1 + M)/2) ≤ 1`, then `M = 1`.  This is the
arithmetic–geometric mean inequality applied to the eigenvalues of `M`. -/
theorem det_avg_eq_one (M : Matrix (Fin nn) (Fin nn) ℝ) (hM : M.PosDef) (hdet : M.det = 1)
    (hle : ((2 : ℝ)⁻¹ • ((1 : Matrix (Fin nn) (Fin nn) ℝ) + M)).det ≤ 1) : M = 1 := by
  classical
  have hH : M.IsHermitian := hM.isHermitian
  have hpos : ∀ i, 0 < hH.eigenvalues i := fun i => hM.eigenvalues_pos i
  have hprod : ∏ i, hH.eigenvalues i = 1 := by
    have h := hH.det_eq_prod_eigenvalues
    rw [hdet] at h
    simpa using h.symm
  set U := hH.eigenvectorUnitary with hUdef
  set D : Matrix (Fin nn) (Fin nn) ℝ :=
    Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) with hDdef
  have hspec : M = conjStarAlgAut ℝ (Matrix (Fin nn) (Fin nn) ℝ) U D := hH.spectral_theorem
  have hDeq : ((2 : ℝ)⁻¹ • ((1 : Matrix (Fin nn) (Fin nn) ℝ) + D))
      = Matrix.diagonal (fun i => (1 + hH.eigenvalues i) / 2) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp only [hDdef, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply_eq,
        Matrix.diagonal_apply_eq, Function.comp_apply, smul_eq_mul]
      simp
      ring
    · simp only [hDdef, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply_ne h,
        Matrix.diagonal_apply_ne _ h, smul_eq_mul]
      simp
  have hdetavg : ((2 : ℝ)⁻¹ • ((1 : Matrix (Fin nn) (Fin nn) ℝ) + M)).det
      = ∏ i, (1 + hH.eigenvalues i) / 2 := by
    have hkey : ((2 : ℝ)⁻¹ • ((1 : Matrix (Fin nn) (Fin nn) ℝ) + M))
        = conjStarAlgAut ℝ (Matrix (Fin nn) (Fin nn) ℝ) U ((2 : ℝ)⁻¹ • (1 + D)) := by
      rw [map_smul, map_add, map_one, ← hspec]
    rw [hkey, det_conj, hDeq, Matrix.det_diagonal]
  have hAM : ∀ i, Real.sqrt (hH.eigenvalues i) ≤ (1 + hH.eigenvalues i) / 2 := by
    intro i
    have h := Real.sq_sqrt (hpos i).le
    nlinarith [sq_nonneg (Real.sqrt (hH.eigenvalues i) - 1)]
  have hAMs : ∀ i, hH.eigenvalues i ≠ 1 →
      Real.sqrt (hH.eigenvalues i) < (1 + hH.eigenvalues i) / 2 := by
    intro i hi
    have h := Real.sq_sqrt (hpos i).le
    have hne : Real.sqrt (hH.eigenvalues i) - 1 ≠ 0 := by
      intro hs
      apply hi
      have : Real.sqrt (hH.eigenvalues i) = 1 := by linarith
      rw [← h, this]; ring
    have hsq : 0 < (Real.sqrt (hH.eigenvalues i) - 1) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
    nlinarith
  have hsq1 : (∏ i, Real.sqrt (hH.eigenvalues i)) ^ 2 = 1 := by
    rw [← Finset.prod_pow, Finset.prod_congr rfl fun i _ => Real.sq_sqrt (hpos i).le]
    exact hprod
  have hspos : 0 < ∏ i, Real.sqrt (hH.eigenvalues i) :=
    Finset.prod_pos fun i _ => Real.sqrt_pos.mpr (hpos i)
  have hs1 : ∏ i, Real.sqrt (hH.eigenvalues i) = 1 := by nlinarith
  have hall : ∀ i, hH.eigenvalues i = 1 := by
    intro i
    by_contra hi
    have hlt := prod_lt_prod_pos (fun j => Real.sqrt (hH.eigenvalues j))
      (fun j => (1 + hH.eigenvalues j) / 2) (fun j => Real.sqrt_pos.mpr (hpos j)) hAM i
      (hAMs i hi)
    rw [hs1] at hlt
    rw [hdetavg] at hle
    linarith
  have hDone : D = (1 : Matrix (Fin nn) (Fin nn) ℝ) := by
    rw [hDdef, ← Matrix.diagonal_one]
    congr 1
    funext i
    simpa using hall i
  rw [hspec, hDone, map_one]

end LJUAux

open LJUAux in
theorem solution {nn m : ℕ} (x : Fin m → Fin nn → ℝ)
    (A₁ A₂ : Matrix (Fin nn) (Fin nn) ℝ) (b₁ b₂ : Fin nn → ℝ)
    (h₁ : IsLownerJohn A₁ b₁ (Set.range x))
    (h₂ : IsLownerJohn A₂ b₂ (Set.range x)) :
    A₁ = A₂ ∧ b₁ = b₂ := by
  classical
  rcases Nat.eq_zero_or_pos nn with hnn0 | hnnpos
  · subst hnn0
    constructor
    · ext i j
      exact absurd i.isLt (by omega)
    · funext i
      exact absurd i.isLt (by omega)
  obtain ⟨hs₁, hpd₁, hcov₁, hopt₁⟩ := h₁
  obtain ⟨hs₂, hpd₂, hcov₂, hopt₂⟩ := h₂
  have hdet₁ : 0 < A₁.det := hpd₁.det_pos
  have hdeteq : A₁.det = A₂.det :=
    le_antisymm (hopt₂ A₁ b₁ hs₁ hpd₁ hcov₁) (hopt₁ A₂ b₂ hs₂ hpd₂ hcov₂)
  have hc₁ : ∀ i, (A₁ *ᵥ x i + b₁) ⬝ᵥ (A₁ *ᵥ x i + b₁) ≤ 1 := fun i => hcov₁ ⟨i, rfl⟩
  have hc₂ : ∀ i, (A₂ *ᵥ x i + b₂) ⬝ᵥ (A₂ *ᵥ x i + b₂) ≤ 1 := fun i => hcov₂ ⟨i, rfl⟩
  -- The midpoint ellipsoid is feasible.
  have hmid : ∀ (Ba Bb : Matrix (Fin nn) (Fin nn) ℝ) (ba bb : Fin nn → ℝ),
      (∀ i, (Ba *ᵥ x i + ba) ⬝ᵥ (Ba *ᵥ x i + ba) ≤ 1) →
      (∀ i, (Bb *ᵥ x i + bb) ⬝ᵥ (Bb *ᵥ x i + bb) ≤ 1) →
      ∀ i, (((2:ℝ)⁻¹ • (Ba + Bb)) *ᵥ x i + (2:ℝ)⁻¹ • (ba + bb))
        ⬝ᵥ (((2:ℝ)⁻¹ • (Ba + Bb)) *ᵥ x i + (2:ℝ)⁻¹ • (ba + bb))
        ≤ 1 - (4:ℝ)⁻¹ * (((Ba *ᵥ x i + ba) - (Bb *ᵥ x i + bb))
          ⬝ᵥ ((Ba *ᵥ x i + ba) - (Bb *ᵥ x i + bb))) := by
    intro Ba Bb ba bb ha hb i
    have hrw : ((2:ℝ)⁻¹ • (Ba + Bb)) *ᵥ x i + (2:ℝ)⁻¹ • (ba + bb)
        = (2:ℝ)⁻¹ • ((Ba *ᵥ x i + ba) + (Bb *ᵥ x i + bb)) := by
      rw [smul_mulVec, Matrix.add_mulVec]
      module
    rw [hrw]
    exact avg_dot_le _ _ (ha i) (hb i)
  -- Step 1: the two shape matrices agree.
  have hAsymm : ((2:ℝ)⁻¹ • (A₁ + A₂)).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.transpose_smul, Matrix.transpose_add, hs₁.eq, hs₂.eq]
  have hApd : ((2:ℝ)⁻¹ • (A₁ + A₂)).PosDef :=
    Matrix.PosDef.smul (hpd₁.add hpd₂) (by norm_num)
  have hAcov : Set.range x ⊆ ellipsoidBody ((2:ℝ)⁻¹ • (A₁ + A₂)) ((2:ℝ)⁻¹ • (b₁ + b₂)) := by
    rintro _ ⟨i, rfl⟩
    have h := hmid A₁ A₂ b₁ b₂ hc₁ hc₂ i
    have hnn := dotProduct_self_nonneg
      ((A₁ *ᵥ x i + b₁) - (A₂ *ᵥ x i + b₂))
    simp only [ellipsoidBody, Set.mem_setOf_eq]
    linarith
  have hAdet : ((2:ℝ)⁻¹ • (A₁ + A₂)).det ≤ A₁.det := hopt₁ _ _ hAsymm hApd hAcov
  -- Congruence: reduce to `det ((1 + M)/2) ≤ 1` with `det M = 1`.
  have hPsd₁ : A₁.PosSemidef := hpd₁.posSemidef
  have hSpsd : (CFC.sqrt A₁).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A₁)
  have hSsq : CFC.sqrt A₁ * CFC.sqrt A₁ = A₁ := by
    have h := CFC.sq_sqrt A₁ (Matrix.nonneg_iff_posSemidef.mpr hPsd₁)
    rwa [sq] at h
  set S : Matrix (Fin nn) (Fin nn) ℝ := CFC.sqrt A₁ with hSdef
  have hSsymm : S.IsSymm := hSpsd.isHermitian
  have hSdetsq : S.det * S.det = A₁.det := by rw [← Matrix.det_mul, hSsq]
  have hSdetne : S.det ≠ 0 := by
    intro h
    rw [h, mul_zero] at hSdetsq
    exact absurd hSdetsq.symm (ne_of_gt hdet₁)
  have hSunit : IsUnit S.det := isUnit_iff_ne_zero.mpr hSdetne
  have hSinvT : (S⁻¹)ᵀ = S⁻¹ := by rw [Matrix.transpose_nonsing_inv, hSsymm.eq]
  set M : Matrix (Fin nn) (Fin nn) ℝ := S⁻¹ * A₂ * S⁻¹ with hMdef
  have hSinv_ne : ∀ v : Fin nn → ℝ, v ≠ 0 → S⁻¹ *ᵥ v ≠ 0 := by
    intro v hv hz
    apply hv
    have : S *ᵥ (S⁻¹ *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv S hSunit, Matrix.one_mulVec]
    rw [hz, Matrix.mulVec_zero] at this
    exact this.symm
  have hMquad : ∀ v : Fin nn → ℝ,
      v ⬝ᵥ (M *ᵥ v) = (S⁻¹ *ᵥ v) ⬝ᵥ (A₂ *ᵥ (S⁻¹ *ᵥ v)) := by
    intro v
    rw [dot_mulVec_left, hSinvT, hMdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hMsymm : M.IsSymm := by
    unfold Matrix.IsSymm
    rw [hMdef, Matrix.transpose_mul, Matrix.transpose_mul, hSinvT, hs₂.eq, Matrix.mul_assoc]
  have hMpd : M.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · ext i j
      simp only [Matrix.conjTranspose_apply, star_trivial]
      exact congrFun (congrFun hMsymm i) j
    · intro v hv
      rw [show (star v : Fin nn → ℝ) = v from star_trivial v, hMquad]
      have := hpd₂.dotProduct_mulVec_pos (hSinv_ne v hv)
      rwa [show star (S⁻¹ *ᵥ v) = S⁻¹ *ᵥ v from star_trivial _] at this
  have hSMS : S * M * S = A₂ := by
    rw [hMdef, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul S hSunit,
      Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv S hSunit, Matrix.one_mul]
  have hdetM : M.det = 1 := by
    have h : A₂.det = S.det * M.det * S.det := by rw [← hSMS, Matrix.det_mul, Matrix.det_mul]
    rw [← hdeteq] at h
    have h4 : A₁.det * (1 - M.det) = 0 := by linear_combination h + M.det * hSdetsq
    rcases mul_eq_zero.mp h4 with h5 | h5
    · exact absurd h5 (ne_of_gt hdet₁)
    · linarith
  have havg : (2:ℝ)⁻¹ • (A₁ + A₂) = S * ((2:ℝ)⁻¹ • ((1 : Matrix (Fin nn) (Fin nn) ℝ) + M)) * S := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      hSsq, hSMS]
  have hdetle : ((2:ℝ)⁻¹ • ((1 : Matrix (Fin nn) (Fin nn) ℝ) + M)).det ≤ 1 := by
    have h : ((2:ℝ)⁻¹ • (A₁ + A₂)).det
        = A₁.det * ((2:ℝ)⁻¹ • ((1 : Matrix (Fin nn) (Fin nn) ℝ) + M)).det := by
      rw [havg, Matrix.det_mul, Matrix.det_mul, ← hSdetsq]
      ring
    rw [h] at hAdet
    nlinarith [hAdet, hdet₁]
  have hM1 : M = 1 := det_avg_eq_one M hMpd hdetM hdetle
  have hA12 : A₁ = A₂ := by rw [← hSMS, hM1, Matrix.mul_one, hSsq]
  refine ⟨hA12, ?_⟩
  -- Step 2: the centres agree.
  by_contra hbne
  have hene : b₁ - b₂ ≠ 0 := sub_ne_zero.mpr hbne
  have hepos : 0 < (b₁ - b₂) ⬝ᵥ (b₁ - b₂) := dotProduct_self_pos hene
  have hc₂' : ∀ i, (A₁ *ᵥ x i + b₂) ⬝ᵥ (A₁ *ᵥ x i + b₂) ≤ 1 := by
    intro i; rw [hA12]; exact hc₂ i
  set ρ : ℝ := 1 - (4:ℝ)⁻¹ * ((b₁ - b₂) ⬝ᵥ (b₁ - b₂)) with hρdef
  have hρlt : ρ < 1 := by rw [hρdef]; linarith
  have hcovmid : ∀ i, (A₁ *ᵥ x i + (2:ℝ)⁻¹ • (b₁ + b₂))
      ⬝ᵥ (A₁ *ᵥ x i + (2:ℝ)⁻¹ • (b₁ + b₂)) ≤ ρ := by
    intro i
    have h := hmid A₁ A₁ b₁ b₂ hc₁ hc₂' i
    have hdiff : (A₁ *ᵥ x i + b₁) - (A₁ *ᵥ x i + b₂) = b₁ - b₂ := by abel
    rw [hdiff] at h
    have hA : (2:ℝ)⁻¹ • (A₁ + A₁) = A₁ := by
      rw [← two_smul ℝ A₁, smul_smul]; norm_num
    rw [hA] at h
    rw [hρdef]
    exact h
  set σ : ℝ := (1 + max ρ 0) / 2 with hσdef
  have hσpos : 0 < σ := by
    rw [hσdef]
    have : (0 : ℝ) ≤ max ρ 0 := le_max_right _ _
    linarith
  have hσlt : σ < 1 := by
    rw [hσdef]
    have : max ρ 0 < 1 := max_lt hρlt one_pos
    linarith
  have hρσ : ρ ≤ σ := by
    rw [hσdef]
    rcases le_or_gt 0 ρ with h | h
    · rw [max_eq_left h]; linarith
    · rw [max_eq_right h.le]; linarith
  set t : ℝ := 1 / Real.sqrt σ with htdef
  have hsqσ : 0 < Real.sqrt σ := Real.sqrt_pos.mpr hσpos
  have hsqlt : Real.sqrt σ < 1 := by
    have h := Real.sqrt_lt_sqrt hσpos.le hσlt
    rwa [Real.sqrt_one] at h
  have htpos : 0 < t := by rw [htdef]; exact div_pos one_pos hsqσ
  have ht1 : 1 < t := by
    rw [htdef, lt_div_iff₀ hsqσ, one_mul]
    exact hsqlt
  have ht2 : t ^ 2 = 1 / σ := by
    rw [htdef, div_pow, one_pow, Real.sq_sqrt hσpos.le]
  -- The scaled midpoint ellipsoid is feasible and has a strictly larger determinant.
  have hcovt : Set.range x ⊆ ellipsoidBody (t • A₁) (t • ((2:ℝ)⁻¹ • (b₁ + b₂))) := by
    rintro _ ⟨i, rfl⟩
    have hrw : (t • A₁) *ᵥ x i + t • ((2:ℝ)⁻¹ • (b₁ + b₂))
        = t • (A₁ *ᵥ x i + (2:ℝ)⁻¹ • (b₁ + b₂)) := by
      rw [smul_mulVec]
      module
    simp only [ellipsoidBody, Set.mem_setOf_eq]
    rw [hrw, dot_smul_self, ht2]
    have h := hcovmid i
    have hd : 0 ≤ (A₁ *ᵥ x i + (2:ℝ)⁻¹ • (b₁ + b₂)) ⬝ᵥ (A₁ *ᵥ x i + (2:ℝ)⁻¹ • (b₁ + b₂)) :=
      dotProduct_self_nonneg _
    rw [div_mul_eq_mul_div, one_mul, div_le_one hσpos]
    linarith
  have htsymm : (t • A₁).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.transpose_smul, hs₁.eq]
  have htpd : (t • A₁).PosDef := Matrix.PosDef.smul hpd₁ htpos
  have hbig := hopt₁ (t • A₁) (t • ((2:ℝ)⁻¹ • (b₁ + b₂))) htsymm htpd hcovt
  rw [Matrix.det_smul, Fintype.card_fin] at hbig
  have htn : 1 < t ^ nn := one_lt_pow₀ ht1 (by omega)
  nlinarith [hbig, hdet₁, htn, mul_pos (show (0:ℝ) < t ^ nn - 1 by linarith) hdet₁]
