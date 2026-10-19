-- Prove2me | solution 1 for CauchyRiemannIndex.model_path_isCZValue
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T11:16:23.573691+00:00
-- url     : https://prove2.me/submissions/88c65228-002a-4400-8d1c-866f7da152e4

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.Prod

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

/-- `ρ̂(A) = e^{iθ}` when `det_ℂ C_A = r e^{iθ}` with `r > 0`. -/
lemma rhoHat_of_eq {A : Mat 1} {r θ : ℝ} (hr : 0 < r)
    (h : complexLinearDet A = (r : ℂ) * Complex.exp (θ * Complex.I)) :
    rhoHat A = Complex.exp (θ * Complex.I) := by
  unfold rhoHat
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr]
  have : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

lemma rhoHat_psi (k : ℤ) (σ t : ℝ) :
    rhoHat (psi k σ t) = Complex.exp (((Real.pi * k * t : ℝ) : ℂ) * Complex.I) := by
  apply rhoHat_of_eq (Real.cosh_pos (σ * t))
  rw [psi, complexLinearDet_m2]
  apply Complex.ext <;>
    simp only [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] <;> ring

lemma wminus_eq : Wminus 1 = m2 2 0 0 (1 / 2) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0] <;> simp [Wminus, Matrix.diagonal]

lemma wplus_eq : Wplus 1 = m2 (-1) 0 0 (-1) := by
  rw [Wplus, m2_one]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp

/-- The model path `ψ = Ψ|_{[0,1]}`. -/
def psiPath (k : ℤ) (σ : ℝ) : C(unitInterval, Mat 1) :=
  ⟨fun t => psi k σ t, (continuous_psi k σ).comp continuous_subtype_val⟩

lemma isCZValue_psiPath (k : ℤ) {σ : ℝ} (hσ : 0 < σ) : IsCZValue (psiPath k σ) k := by
  have hch : 1 < Real.cosh σ := Real.one_lt_cosh.2 hσ.ne'
  have hsh : 0 < Real.sinh σ := Real.sinh_pos_iff.2 hσ
  have hsq := Real.cosh_sq σ
  have hθ₁ : IsArgLift (fun t => rhoHat (psiPath k σ t)) (fun t => Real.pi * k * t) :=
    ⟨by fun_prop, fun t => rhoHat_psi k σ t⟩
  rcases cos_pi_k k with hε | hε
  · -- `Ψ(1) = H(σ)`: a symmetric path with trace `> 2` to `W⁻ = diag(2, 1/2)`
    let a : unitInterval → ℝ := fun s => (1 - s) * Real.cosh σ + 2 * s
    let b : unitInterval → ℝ := fun s => (1 - s) * Real.sinh σ
    have ha : ∀ s, 0 < a s := fun s => by
      have := s.2.1; have := s.2.2; simp only [a]; nlinarith
    have hac : Continuous a := by fun_prop
    have hbc : Continuous b := by fun_prop
    let χ : C(unitInterval, Mat 1) := ⟨fun s => m2 (a s) (b s) (b s) ((1 + b s ^ 2) / a s),
      continuous_m2 hac hbc hbc ((continuous_const.add (hbc.pow 2)).div hac fun s => (ha s).ne')⟩
    have hχ : ∀ s, χ s = m2 (a s) (b s) (b s) ((1 + b s ^ 2) / a s) := fun s => rfl
    refine ⟨χ, ⟨?_, fun s => ⟨?_, ?_⟩, Or.inr ?_⟩, _, fun _ => 0, hθ₁, ⟨continuous_const, fun s => ?_⟩, ?_⟩
    · show χ 0 = psi k σ 1
      rw [hχ, psi_one, hε]
      simp only [a, b, Set.Icc.coe_zero, sub_zero, one_mul, mul_zero, add_zero]
      refine m2_congr rfl rfl rfl ?_
      field_simp; linarith
    · rw [hχ]; apply isSymplectic_m2; field_simp [(ha s).ne']; ring
    · rw [hχ, m2_one, m2_sub, m2_det]
      have has := ha s
      have hpos : 0 < (a s - 1) ^ 2 + b s ^ 2 := by
        by_cases hs1 : (s : ℝ) = 1
        · have : a s = 2 := by simp only [a, hs1]; ring
          rw [this]; positivity
        · have : 0 < b s := mul_pos (by have := s.2.2; exact sub_pos.2 (lt_of_le_of_ne this hs1)) hsh
          positivity
      have e : (1 - a s) * (1 - (1 + b s ^ 2) / a s) - (0 - b s) * (0 - b s) =
          -(((a s - 1) ^ 2 + b s ^ 2) / a s) := by field_simp; ring
      rw [e]
      exact neg_ne_zero.2 (div_pos hpos has).ne'
    · rw [hχ, wminus_eq]
      simp only [a, b, Set.Icc.coe_one, sub_self, zero_mul, zero_add, mul_one]
      refine m2_congr rfl rfl rfl ?_
      norm_num
    · show rhoHat (χ s) = _
      have hd : 0 < (1 + b s ^ 2) / a s := by have := ha s; positivity
      have hpos : 0 < (a s + (1 + b s ^ 2) / a s) / 2 := by have := ha s; linarith
      rw [hχ]
      apply rhoHat_of_eq hpos
      rw [complexLinearDet_m2_symm, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    · simp only [Set.Icc.coe_one, Set.Icc.coe_zero]; ring
  · -- `Ψ(1) = -H(σ)`: the path `-H((1-s)σ)` to `W⁺ = -Id`
    let χ : C(unitInterval, Mat 1) := ⟨fun s => m2 (-Real.cosh ((1 - s) * σ)) (-Real.sinh ((1 - s) * σ))
      (-Real.sinh ((1 - s) * σ)) (-Real.cosh ((1 - s) * σ)), continuous_m2 (by fun_prop)
        (by fun_prop) (by fun_prop) (by fun_prop)⟩
    have hχ : ∀ s : unitInterval, χ s = m2 (-Real.cosh ((1 - s) * σ)) (-Real.sinh ((1 - s) * σ))
      (-Real.sinh ((1 - s) * σ)) (-Real.cosh ((1 - s) * σ)) := fun s => rfl
    refine ⟨χ, ⟨?_, fun s => ⟨?_, ?_⟩, Or.inl ?_⟩, _, fun _ => Real.pi, hθ₁,
      ⟨continuous_const, fun s => ?_⟩, ?_⟩
    · show χ 0 = psi k σ 1
      rw [hχ, psi_one, hε]
      simp only [Set.Icc.coe_zero, sub_zero, one_mul]
      refine m2_congr ?_ ?_ ?_ ?_ <;> ring
    · rw [hχ]; apply isSymplectic_m2
      have := Real.cosh_sq ((1 - (s : ℝ)) * σ); linear_combination this
    · rw [hχ, m2_one, m2_sub, m2_det]
      have := Real.cosh_sq ((1 - (s : ℝ)) * σ)
      have := Real.cosh_pos ((1 - (s : ℝ)) * σ)
      intro h0; nlinarith
    · rw [hχ, wplus_eq]
      simp
    · show rhoHat (χ s) = _
      rw [hχ]
      apply rhoHat_of_eq (Real.cosh_pos ((1 - (s : ℝ)) * σ))
      rw [complexLinearDet_m2_symm, Complex.exp_pi_mul_I]
      push_cast; ring
    · simp only [Set.Icc.coe_one, Set.Icc.coe_zero]; ring

lemma model_path_isCZValue_aux (k : ℤ) (σ : ℝ) (hσ : 0 < σ) (ψ : C(unitInterval, Mat 1))
    (hψ : ∀ t : unitInterval, ψ t = psi k σ t) : IsCZValue ψ k := by
  have : ψ = psiPath k σ := ContinuousMap.ext hψ
  subst this
  exact isCZValue_psiPath k hσ

end

end CRModel

open CauchyRiemannIndex

open Matrix

theorem solution (k : ℤ) (σ : ℝ) (hσ : 0 < σ) (ψ : C(unitInterval, Mat 1))
    (hψ : ∀ t : unitInterval, ψ t = Matrix.fromBlocks
      (Matrix.of fun _ _ => Real.cos (Real.pi * k * t) * Real.cosh (σ * t) -
        Real.sin (Real.pi * k * t) * Real.sinh (σ * t))
      (Matrix.of fun _ _ => Real.cos (Real.pi * k * t) * Real.sinh (σ * t) -
        Real.sin (Real.pi * k * t) * Real.cosh (σ * t))
      (Matrix.of fun _ _ => Real.sin (Real.pi * k * t) * Real.cosh (σ * t) +
        Real.cos (Real.pi * k * t) * Real.sinh (σ * t))
      (Matrix.of fun _ _ => Real.sin (Real.pi * k * t) * Real.sinh (σ * t) +
        Real.cos (Real.pi * k * t) * Real.cosh (σ * t))) :
    IsCZValue ψ k :=
  CRModel.model_path_isCZValue_aux k σ hσ ψ hψ
