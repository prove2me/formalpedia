-- Prove2me | solution 1 for CauchyRiemannIndex.model_asymptotic_operator
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T11:16:36.412006+00:00
-- url     : https://prove2.me/submissions/ed7d4ab8-8242-41ad-9d8b-305deb316e0c

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Theorems.Thm_CauchyRiemannIndex_model_fundamentalSolution
import Theorems.Thm_CauchyRiemannIndex_czIndex_eq_of_isCZValue
import Theorems.Thm_CauchyRiemannIndex_model_path_isCZValue
import Theorems.Thm_CauchyRiemannIndex_asymptoticCZIndex_eq_czIndex
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_existsUnique
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_symplectic

open Matrix

namespace CRModel

open CauchyRiemannIndex

/-- The `2 × 2` matrix `[[a, b], [c, d]]` in `Mat 1`. -/
def m2 (a b c d : ℝ) : Mat 1 :=
  Matrix.fromBlocks (Matrix.of fun _ _ => a) (Matrix.of fun _ _ => b)
    (Matrix.of fun _ _ => c) (Matrix.of fun _ _ => d)

@[simp] lemma m2_11 (a b c d : ℝ) (i j : Fin 1) : m2 a b c d (Sum.inl i) (Sum.inl j) = a := rfl
@[simp] lemma m2_12 (a b c d : ℝ) (i j : Fin 1) : m2 a b c d (Sum.inl i) (Sum.inr j) = b := rfl
@[simp] lemma m2_21 (a b c d : ℝ) (i j : Fin 1) : m2 a b c d (Sum.inr i) (Sum.inl j) = c := rfl
@[simp] lemma m2_22 (a b c d : ℝ) (i j : Fin 1) : m2 a b c d (Sum.inr i) (Sum.inr j) = d := rfl

lemma m2_eta (A : Mat 1) : A = m2 (A (Sum.inl 0) (Sum.inl 0)) (A (Sum.inl 0) (Sum.inr 0))
    (A (Sum.inr 0) (Sum.inl 0)) (A (Sum.inr 0) (Sum.inr 0)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0] <;> rfl

lemma m2_mul (a b c d a' b' c' d' : ℝ) : m2 a b c d * m2 a' b' c' d' =
    m2 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type]

lemma m2_add (a b c d a' b' c' d' : ℝ) : m2 a b c d + m2 a' b' c' d' =
    m2 (a + a') (b + b') (c + c') (d + d') := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp

lemma m2_sub (a b c d a' b' c' d' : ℝ) : m2 a b c d - m2 a' b' c' d' =
    m2 (a - a') (b - b') (c - c') (d - d') := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp

lemma m2_smul (r a b c d : ℝ) : r • m2 a b c d = m2 (r * a) (r * b) (r * c) (r * d) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp

lemma m2_one : (1 : Mat 1) = m2 1 0 0 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0] <;> simp

lemma m2_J : J₀ 1 = m2 0 (-1) 1 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0] <;> simp [Matrix.J]

lemma m2_antilinear (β : ℂ) : antilinearMat β = m2 β.re β.im β.im (-β.re) := rfl

lemma m2_det (a b c d : ℝ) : (m2 a b c d).det = a * d - b * c := by
  rw [← Matrix.det_reindex_self finSumFinEquiv, Matrix.det_fin_two]
  have h0 : finSumFinEquiv.symm (0 : Fin 2) = (Sum.inl 0 : Fin 1 ⊕ Fin 1) := rfl
  have h1 : finSumFinEquiv.symm (1 : Fin 2) = (Sum.inr 0 : Fin 1 ⊕ Fin 1) := rfl
  simp [Matrix.reindex_apply, h0, h1]

lemma complexLinearDet_m2 (a b c d : ℝ) :
    complexLinearDet (m2 a b c d) = ⟨(a + d) / 2, (c - b) / 2⟩ := by
  unfold complexLinearDet complexLinearPart
  rw [Matrix.det_unique]
  apply Complex.ext <;>
    simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₁, Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.fromBlocks, m2] <;> ring

lemma hasDerivAt_m2 {a b c d : ℝ → ℝ} {a' b' c' d' x : ℝ} (ha : HasDerivAt a a' x)
    (hb : HasDerivAt b b' x) (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) :
    HasDerivAt (fun t => m2 (a t) (b t) (c t) (d t)) (m2 a' b' c' d') x := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  rcases i with i | i <;> rcases j with j | j <;> simpa

lemma continuous_m2 {X : Type*} [TopologicalSpace X] {a b c d : X → ℝ} (ha : Continuous a)
    (hb : Continuous b) (hc : Continuous c) (hd : Continuous d) :
    Continuous (fun t => m2 (a t) (b t) (c t) (d t)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  rcases i with i | i <;> rcases j with j | j <;> simpa

lemma m2_congr {a b c d a' b' c' d' : ℝ} (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') :
    m2 a b c d = m2 a' b' c' d' := by rw [ha, hb, hc, hd]

lemma m2_transpose (a b c d : ℝ) : (m2 a b c d)ᵀ = m2 a c b d := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp

lemma isSymplectic_m2 {a b c d : ℝ} (h : a * d - b * c = 1) : IsSymplectic (m2 a b c d) := by
  unfold IsSymplectic
  rw [SymplecticGroup.mem_iff, m2_transpose, show Matrix.J (Fin 1) ℝ = J₀ 1 from rfl, m2_J,
    m2_mul, m2_mul]
  refine m2_congr ?_ ?_ ?_ ?_ <;>
    first | ring1 | linear_combination h | linear_combination (-1 : ℝ) * h |
      linear_combination (2 : ℝ) * h | linear_combination (-2 : ℝ) * h

lemma complexLinearDet_m2_symm (a b d : ℝ) :
    complexLinearDet (m2 a b b d) = (((a + d) / 2 : ℝ) : ℂ) := by
  rw [complexLinearDet_m2]
  apply Complex.ext <;> simp only [Complex.ofReal_re, Complex.ofReal_im] <;> ring


end CRModel

namespace CRModel

open CauchyRiemannIndex

noncomputable section

/-- The model coefficient `S(t) = π k Id + σ · (z ↦ e^{2πikt} z̄)`. -/
def S (k : ℤ) (σ : ℝ) : ℝ → Mat 1 := fun t : ℝ => (Real.pi * k) • (1 : Mat 1) +
  σ • antilinearMat (Complex.exp (2 * Real.pi * k * t * Complex.I))

lemma S_eq (k : ℤ) (σ t : ℝ) : S k σ t =
    m2 (Real.pi * k + σ * Real.cos (2 * (Real.pi * k * t))) (σ * Real.sin (2 * (Real.pi * k * t)))
      (σ * Real.sin (2 * (Real.pi * k * t))) (Real.pi * k - σ * Real.cos (2 * (Real.pi * k * t))) := by
  have he : (2 * (Real.pi : ℂ) * (k : ℂ) * (t : ℂ) * Complex.I) =
      ((2 * (Real.pi * k * t) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [S, he, m2_antilinear, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, m2_one,
    m2_smul, m2_smul, m2_add]
  refine m2_congr ?_ ?_ ?_ ?_ <;> ring

/-- The explicit fundamental solution `Ψ(t) = R(πkt) H(σt)`. -/
def psi (k : ℤ) (σ t : ℝ) : Mat 1 :=
  m2 (Real.cos (Real.pi * k * t) * Real.cosh (σ * t) - Real.sin (Real.pi * k * t) * Real.sinh (σ * t))
    (Real.cos (Real.pi * k * t) * Real.sinh (σ * t) - Real.sin (Real.pi * k * t) * Real.cosh (σ * t))
    (Real.sin (Real.pi * k * t) * Real.cosh (σ * t) + Real.cos (Real.pi * k * t) * Real.sinh (σ * t))
    (Real.sin (Real.pi * k * t) * Real.sinh (σ * t) + Real.cos (Real.pi * k * t) * Real.cosh (σ * t))

lemma continuous_psi (k : ℤ) (σ : ℝ) : Continuous (psi k σ) := by
  unfold psi
  apply continuous_m2 <;> fun_prop

lemma sin_pi_k (k : ℤ) : Real.sin (Real.pi * k * 1) = 0 := by
  rw [mul_one, mul_comm]; exact Real.sin_int_mul_pi k

lemma cos_pi_k (k : ℤ) : Real.cos (Real.pi * k * 1) = 1 ∨ Real.cos (Real.pi * k * 1) = -1 := by
  have h := Real.sin_sq_add_cos_sq (Real.pi * k * 1)
  rw [sin_pi_k] at h
  exact mul_self_eq_one_iff.1 (by linear_combination h)

lemma psi_one (k : ℤ) (σ : ℝ) : psi k σ 1 =
    m2 (Real.cos (Real.pi * k * 1) * Real.cosh σ) (Real.cos (Real.pi * k * 1) * Real.sinh σ)
      (Real.cos (Real.pi * k * 1) * Real.sinh σ) (Real.cos (Real.pi * k * 1) * Real.cosh σ) := by
  rw [psi, sin_pi_k, mul_one]
  refine m2_congr ?_ ?_ ?_ ?_ <;> ring

lemma det_one_sub_psi_one (k : ℤ) {σ : ℝ} (hσ : 0 < σ) : (1 - psi k σ 1).det ≠ 0 := by
  have hch : 1 < Real.cosh σ := Real.one_lt_cosh.2 hσ.ne'
  have hsq := Real.cosh_sq σ
  rw [psi_one, m2_one, m2_sub, m2_det]
  rcases cos_pi_k k with h | h <;> rw [h]
  · intro h0; nlinarith
  · intro h0; nlinarith

lemma isSymLoop_S (k : ℤ) (σ : ℝ) : IsSymLoop (S k σ) := by
  refine ⟨?_, fun t => ?_, fun t => ?_⟩
  · have : S k σ = fun t => m2 (Real.pi * k + σ * Real.cos (2 * (Real.pi * k * t)))
        (σ * Real.sin (2 * (Real.pi * k * t))) (σ * Real.sin (2 * (Real.pi * k * t)))
        (Real.pi * k - σ * Real.cos (2 * (Real.pi * k * t))) := funext (S_eq k σ)
    rw [this]
    apply continuous_m2 <;> fun_prop
  · have h2 : 2 * (Real.pi * k * (t + 1)) = 2 * (Real.pi * k * t) + k * (2 * Real.pi) := by ring
    rw [S_eq, S_eq, h2, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
  · rw [S_eq, Matrix.IsSymm, m2_transpose]

end

end CRModel

namespace CRModel

open CauchyRiemannIndex

noncomputable section

theorem model_main (k : ℤ) (σ : ℝ) (hσ : 0 < σ) :
    IsNondegenerate (S k σ) ∧ asymptoticCZIndex (S k σ) = k := by
  have hΨ : IsFundamentalSolution (S k σ) (psi k σ) := model_fundamentalSolution k σ
  have hS := isSymLoop_S k σ
  have hnd : IsNondegenerate (S k σ) := fun Ψ h => by
    rw [(fundamentalSolution_existsUnique 1 (S k σ) hS.1).unique h hΨ]
    exact det_one_sub_psi_one k hσ
  refine ⟨hnd, ?_⟩
  let ψ : C(unitInterval, Mat 1) := ⟨fun t => psi k σ t, (continuous_psi k σ).comp continuous_subtype_val⟩
  rw [asymptoticCZIndex_eq_czIndex 1 (S k σ) hS hnd (psi k σ) hΨ ψ (fun _ => rfl)]
  exact czIndex_eq_of_isCZValue ψ (fun t => fundamentalSolution_symplectic 1 (S k σ) hS.2.2 _ hΨ t)
    (by simpa [ψ] using hΨ.1) (by simpa [ψ] using hnd _ hΨ) k
    (model_path_isCZValue k σ hσ ψ (fun _ => rfl))

end

end CRModel

open CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem solution (k : ℤ) (σ : ℝ) (hσ : 0 < σ) :
    IsNondegenerate (fun t : ℝ => (Real.pi * k) • (1 : Mat 1) +
        σ • antilinearMat (Complex.exp (2 * Real.pi * k * t * Complex.I))) ∧
      asymptoticCZIndex (fun t : ℝ => (Real.pi * k) • (1 : Mat 1) +
        σ • antilinearMat (Complex.exp (2 * Real.pi * k * t * Complex.I))) = k :=
  CRModel.model_main k σ hσ
