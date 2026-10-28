-- Prove2me | solution 1 for BoseGIE.evolvedState_entangled_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:25:42.867306+00:00
-- url     : https://prove2.me/submissions/7b0d187c-5293-4df5-ae08-ef183e03e97c

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_BoseGIE_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace QB_29c5

open BoseGIE

lemma expI (x : ℝ) : Complex.exp (↑x * Complex.I) = ↑(Real.cos x) + ↑(Real.sin x) * Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- Partial transpose on the second factor. -/
def ptT (ρ : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ) : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ :=
  Matrix.of fun p q => ρ (p.1, q.2) (q.1, p.2)

lemma ptT_kron (A B : Matrix Qubit Qubit ℂ) : ptT (A ⊗ₖ B) = A ⊗ₖ Bᵀ := by
  ext p q
  simp [ptT]

lemma ptT_sum {n : ℕ} (c : Fin n → ℂ) (M : Fin n → Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ) :
    ptT (∑ i, c i • M i) = ∑ i, c i • ptT (M i) := by
  ext p q
  simp [ptT, Matrix.sum_apply]

/-- The witness vector. -/
noncomputable def wv (α β : ℝ) : Qubit × Qubit → ℂ :=
  fun p => (!![-Complex.exp (α * Complex.I), 1; -1, Complex.exp (β * Complex.I)] : Matrix Qubit Qubit ℂ)
    p.1 p.2

lemma sep_nonneg (ρ : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ) (h : IsSeparable ρ)
    (x : Qubit × Qubit → ℂ) : 0 ≤ star x ⬝ᵥ (ptT ρ *ᵥ x) := by
  obtain ⟨n, p, ρ₁, ρ₂, hp, -, h1, h2, rfl⟩ := h
  rw [ptT_sum, Matrix.sum_mulVec, _root_.dotProduct_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [ptT_kron, Matrix.smul_mulVec, _root_.dotProduct_smul, smul_eq_mul]
  exact mul_nonneg (Complex.zero_le_real.mpr (hp i))
    (((h1 i).1.kronecker (h2 i).1.transpose).dotProduct_mulVec_nonneg x)

lemma Q_val (α β : ℝ) :
    star (wv α β) ⬝ᵥ (ptT (pureDM (psiEnd α β)) *ᵥ wv α β) = ((Real.cos (α + β) - 1 : ℝ) : ℂ) := by
  simp only [dotProduct, mulVec, ptT, pureDM, psiEnd, wv, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.of_apply, Pi.star_apply, expI, Real.cos_add]
  have h1 := Real.sin_sq_add_cos_sq α
  have h2 := Real.sin_sq_add_cos_sq β
  generalize Real.cos α = ca at *
  generalize Real.sin α = sa at *
  generalize Real.cos β = cb at *
  generalize Real.sin β = sb at *
  refine Complex.ext ?_ ?_ <;> simp [Complex.mul_re, Complex.mul_im]
  · linear_combination (-(1/2) * (sb^2 + cb^2)) * h1 + (-1/2) * h2
  · ring

/-- The half-normalized projector onto `(1, e^{iθ})`. -/
noncomputable def proj (θ : ℝ) : Matrix Qubit Qubit ℂ :=
  (1 / 2 : ℂ) • vecMulVec ![1, Complex.exp (θ * Complex.I)] (star ![1, Complex.exp (θ * Complex.I)])

lemma proj_apply (θ : ℝ) (i j : Qubit) :
    proj θ i j = (1 / 2 : ℂ) * (![1, Complex.exp (θ * Complex.I)] i *
      star (![1, Complex.exp (θ * Complex.I)] j)) := by
  simp only [proj, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, Pi.star_apply]

lemma proj_dm (θ : ℝ) : PeresTerno.IsDensityMatrix (proj θ) := by
  refine ⟨(posSemidef_vecMulVec_self_star _).smul (by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.zero_le_real.mpr (by norm_num)), ?_⟩
  have h := Real.sin_sq_add_cos_sq θ
  simp only [proj, Matrix.trace, Fin.sum_univ_two, Matrix.diag, Matrix.smul_apply, vecMulVec_apply,
    Pi.star_apply, expI]
  generalize Real.cos θ = c at *
  generalize Real.sin θ = s at *
  refine Complex.ext ?_ ?_ <;> simp [Complex.mul_re, Complex.mul_im]
  · linear_combination (1/2) * h
  · ring

lemma sep_of (α β : ℝ) (n : ℤ) (h : α + β = 2 * Real.pi * n) :
    IsSeparable (pureDM (psiEnd α β)) := by
  refine ⟨1, fun _ => 1, fun _ => proj β, fun _ => proj α, fun _ => zero_le_one, by simp,
    fun _ => proj_dm β, fun _ => proj_dm α, ?_⟩
  have hb : β = -α + n * (2 * Real.pi) := by linarith
  have hc : Real.cos β = Real.cos α := by rw [hb, Real.cos_add_int_mul_two_pi, Real.cos_neg]
  have hs : Real.sin β = -Real.sin α := by rw [hb, Real.sin_add_int_mul_two_pi, Real.sin_neg]
  have h1 := Real.sin_sq_add_cos_sq α
  simp only [Finset.univ_unique, Finset.sum_singleton, Complex.ofReal_one, one_smul]
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [Matrix.kronecker_apply, proj_apply, psiEnd, pureDM, Matrix.of_apply]
  simp only [expI, hc, hs]
  generalize Real.cos α = ca at *
  generalize Real.sin α = sa at *
  have hca : ca * (sa ^ 2 + ca ^ 2) = ca := by rw [h1, mul_one]
  have hsa : sa * (sa ^ 2 + ca ^ 2) = sa := by rw [h1, mul_one]
  have hsq : (sa ^ 2 + ca ^ 2) ^ 2 = 1 := by rw [h1, one_pow]
  ring_nf at hca hsa hsq
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    refine Complex.ext ?_ ?_ <;> simp [Complex.mul_re, Complex.mul_im] <;>
    linarith [hca, hsa, h1, hsq]

end QB_29c5

open QB_29c5 in
theorem solution (α β : ℝ) :
    ¬ BoseGIE.IsSeparable (BoseGIE.pureDM (BoseGIE.psiEnd α β)) ↔
      ∀ n : ℤ, α + β ≠ 2 * Real.pi * n := by
  constructor
  · intro hns n hn
    exact hns (sep_of α β n hn)
  · intro hn hs
    have h0 := sep_nonneg _ hs (wv α β)
    rw [Q_val, Complex.zero_le_real] at h0
    have hc : Real.cos (α + β) = 1 := le_antisymm (Real.cos_le_one _) (by linarith)
    obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).mp hc
    exact hn k (by rw [← hk]; ring)

