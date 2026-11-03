-- Prove2me | solution 1 for ConleyZehnder.czIndex_one_eq_of_rhoHat_lift
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-02T16:03:08.296552+00:00
-- url     : https://prove2.me/submissions/129dbc7a-59b6-4265-b323-2b47e13ff8b5

import Definitions.Def_ConleyZehnder_Setting
import Theorems.Thm_ConleyZehnder_czValue_existsUnique
import Theorems.Thm_ConleyZehnder_argLift_exists_increment_unique
import Theorems.Thm_ConleyZehnder_rhoHat_path_continuous
import Theorems.Thm_ConleyZehnder_spStar_exists_path_to_W
import Theorems.Thm_ConleyZehnder_complexLinearDet_ne_zero
import Theorems.Thm_FiniteEnergyPlane_exists_int_forall_mem_Ioo_of_forall_ne

open ConleyZehnder Matrix unitInterval

namespace CZB1


theorem trace_mat1 (A : Mat 1) : A.trace = A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0 : Fin 1 ⊕ Fin 1) + A (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1) := by
  simp [Matrix.trace, Fintype.sum_sum_type]

theorem det_mat1 (A : Mat 1) : A.det = A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0 : Fin 1 ⊕ Fin 1) * A (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1) - A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1) * A (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0 : Fin 1 ⊕ Fin 1) := by
  rw [← Matrix.det_reindex_self finSumFinEquiv A, Matrix.det_fin_two]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]
  rfl

theorem cld_mat1 (A : Mat 1) :
    complexLinearDet A = ⟨(A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0 : Fin 1 ⊕ Fin 1) + A (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1)) / 2, (A (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0 : Fin 1 ⊕ Fin 1) - A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1)) / 2⟩ := by
  unfold complexLinearDet complexLinearPart
  rw [Matrix.det_unique]
  apply Complex.ext <;>
    simp [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₁,
      Matrix.toBlocks₂₁, Matrix.fromBlocks] <;> ring

theorem det_eq_one (A : Mat 1) (hA : IsSymplectic A) : A.det = 1 := by
  have h := (SymplecticGroup.mem_iff (A := A)).1 hA
  have h' := congrFun (congrFun h (Sum.inl 0 : Fin 1 ⊕ Fin 1)) (Sum.inr 0 : Fin 1 ⊕ Fin 1)
  simp [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks,
    Matrix.transpose_apply] at h'
  rw [det_mat1]
  linarith

theorem det_one_sub (A : Mat 1) (hA : IsSymplectic A) : (1 - A).det = 2 - A.trace := by
  have h := det_eq_one A hA
  rw [det_mat1] at h
  rw [det_mat1, trace_mat1]
  simp [Matrix.sub_apply, Matrix.one_apply]
  linarith

theorem rhoHat_re_pos (A : Mat 1) (hA : IsSymplectic A) (htr : 0 < A.trace) :
    0 < (rhoHat A).re := by
  have hne := complexLinearDet_ne_zero A hA
  have hn : 0 < ‖complexLinearDet A‖ := norm_pos_iff.2 hne
  unfold rhoHat
  rw [Complex.div_ofReal_re]
  apply div_pos _ hn
  rw [cld_mat1, trace_mat1] at *
  simp only
  linarith

theorem rhoHat_ne_one (A : Mat 1) (hA : IsSymplectic A) (htr : A.trace < 2) :
    rhoHat A ≠ 1 := by
  intro h1
  have hne := complexLinearDet_ne_zero A hA
  have hn : (‖complexLinearDet A‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hne
  have he : complexLinearDet A = (‖complexLinearDet A‖ : ℂ) := by
    unfold rhoHat at h1
    rw [div_eq_one_iff_eq hn] at h1
    exact h1
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  have hpos : 0 < ‖complexLinearDet A‖ := norm_pos_iff.2 hne
  rw [cld_mat1] at hre him hpos
  simp only [Complex.ofReal_re, Complex.ofReal_im] at hre him
  have hdet := det_eq_one A hA
  rw [det_mat1] at hdet
  rw [trace_mat1] at htr
  have hc : A (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0 : Fin 1 ⊕ Fin 1) = A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1) := by linarith
  rw [hc] at hdet
  have hs : 0 < A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0 : Fin 1 ⊕ Fin 1) + A (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1) := by linarith
  nlinarith [sq_nonneg (A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0 : Fin 1 ⊕ Fin 1) - A (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1)), sq_nonneg (A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1)), mul_pos hs (by linarith : (0:ℝ) < 2 - (A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0 : Fin 1 ⊕ Fin 1) + A (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1)))]

theorem trace_Wplus : (Wplus 1).trace = -2 := by
  simp [Wplus, Matrix.trace, Fintype.sum_sum_type] <;> norm_num

theorem trace_Wminus : (Wminus 1).trace = 5 / 2 := by
  simp [Wminus, Matrix.trace, Fintype.sum_sum_type] <;> norm_num

theorem rhoHat_Wplus : rhoHat (Wplus 1) = -1 := by
  have : complexLinearDet (Wplus 1) = -1 := by
    rw [cld_mat1]; apply Complex.ext <;> simp [Wplus] <;> try norm_num
  unfold rhoHat; rw [this]; simp

theorem rhoHat_Wminus : rhoHat (Wminus 1) = 1 := by
  have : complexLinearDet (Wminus 1) = (5 / 4 : ℝ) := by
    rw [cld_mat1]; apply Complex.ext <;> simp [Wminus] <;> try norm_num
  unfold rhoHat; rw [this]
  have : ‖((5 / 4 : ℝ) : ℂ)‖ = 5 / 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  rw [this]; simp

theorem rhoHat_one : rhoHat (1 : Mat 1) = 1 := by
  have : complexLinearDet (1 : Mat 1) = (1 : ℝ) := by
    rw [cld_mat1]; apply Complex.ext <;> simp [Matrix.one_apply] <;> try norm_num
  unfold rhoHat; rw [this]; simp

theorem czIndex_eq_of_value (ψ : C(unitInterval, Mat 1)) (hψ : ψ ∈ SP 1) {k : ℤ}
    (hk : IsCZValue ψ k) : czIndex ψ = k := by
  have hex : ∃ k, IsCZValue ψ k := ⟨k, hk⟩
  unfold czIndex
  rw [dif_pos hex]
  exact (czValue_existsUnique ψ hψ).unique hex.choose_spec hk

theorem exp_eq_exp_int {x y : ℝ} (h : Complex.exp (x * Complex.I) = Complex.exp (y * Complex.I)) :
    ∃ n : ℤ, x = y + 2 * Real.pi * n := by
  rw [Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simp at this
  linarith

theorem exp_eq_one_int {x : ℝ} (h : Complex.exp (x * Complex.I) = 1) :
    ∃ n : ℤ, x = 2 * Real.pi * n := by
  obtain ⟨n, hn⟩ := exp_eq_exp_int (y := 0) (by rw [h]; simp)
  exact ⟨n, by linarith⟩

theorem exp_eq_neg_one_int {x : ℝ} (h : Complex.exp (x * Complex.I) = -1) :
    ∃ n : ℤ, x = Real.pi + 2 * Real.pi * n := by
  obtain ⟨n, hn⟩ := exp_eq_exp_int (y := Real.pi)
    (by rw [h, Complex.exp_mul_I]; simp [← Complex.ofReal_cos, ← Complex.ofReal_sin])
  exact ⟨n, hn⟩

theorem int_eq_of_lt {z a : ℤ} (h1 : (a : ℝ) - 1 < z) (h2 : (z : ℝ) < a + 1) : z = a := by
  have h1' : a - 1 < z := by exact_mod_cast h1
  have h2' : z < a + 1 := by exact_mod_cast h2
  omega

/-- The Conley–Zehnder index of a path in `SP(1)` from the increment of a continuous argument of
`ρ̂` along it and the trace of its end point. -/
theorem czIndex_one_eq_of_rhoHat_lift (ψ : C(unitInterval, Mat 1)) (hψ : ψ ∈ SP 1)
    (θ : unitInterval → ℝ) (hθ : IsArgLift (fun t => rhoHat (ψ t)) θ) (k : ℤ) :
    (2 < (ψ 1).trace → |θ 1 - θ 0 - 2 * Real.pi * k| < Real.pi / 2 → czIndex ψ = 2 * k) ∧
    ((ψ 1).trace < 2 → 2 * Real.pi * k < θ 1 - θ 0 → θ 1 - θ 0 < 2 * Real.pi * k + 2 * Real.pi →
      czIndex ψ = 2 * k + 1) := by
  have hpi := Real.pi_pos
  obtain ⟨χ, hχ0, hχs, hχ1⟩ := spStar_exists_path_to_W (ψ 1) ⟨hψ.1 1, hψ.2.2⟩
  have hsymp : ∀ t, IsSymplectic (χ t) := fun t => (hχs t).1
  have htr2 : ∀ t, (χ t).trace ≠ 2 := fun t h => (hχs t).2 (by rw [det_one_sub _ (hsymp t), h]; ring)
  have htrc : Continuous fun t => (χ t).trace := by
    simp only [Matrix.trace, Matrix.diag]; fun_prop
  have hrc := rhoHat_path_continuous χ hsymp
  obtain ⟨θ₂, hθ₂⟩ := (argLift_exists_increment_unique hrc.1 hrc.2).1
  -- common relations between the lifts
  obtain ⟨n₀, hn₀⟩ : ∃ n : ℤ, θ 0 = 2 * Real.pi * n := by
    apply exp_eq_one_int
    rw [← hθ.2 0]; show rhoHat (ψ 0) = 1; rw [hψ.2.1]; exact rhoHat_one
  obtain ⟨n₁, hn₁⟩ : ∃ n : ℤ, θ₂ 0 = θ 1 + 2 * Real.pi * n := by
    apply exp_eq_exp_int
    rw [← hθ₂.2 0, ← hθ.2 1]; show rhoHat (χ 0) = rhoHat (ψ 1); rw [hχ0]
  -- trace keeps its side of 2 along χ
  have hside : ∀ t, (2 < (χ t).trace ↔ 2 < (ψ 1).trace) := by
    intro t
    have key : ∀ a b : unitInterval, 2 < (χ a).trace → (χ b).trace < 2 → False := by
      intro a b ha hb
      obtain ⟨y, hy⟩ := intermediate_value_univ b a htrc ⟨hb.le, ha.le⟩
      exact htr2 y hy
    rw [← hχ0]
    constructor
    · intro h
      rcases lt_or_gt_of_ne (htr2 0) with h0 | h0
      · exact (key t 0 h h0).elim
      · exact h0
    · intro h
      rcases lt_or_gt_of_ne (htr2 t) with h0 | h0
      · exact (key 0 t h h0).elim
      · exact h0
  constructor
  · intro htr hk
    have hpos : ∀ t, 2 < (χ t).trace := fun t => (hside t).2 htr
    have hW : χ 1 = Wminus 1 := by
      rcases hχ1 with h | h
      · have := hpos 1; rw [h, trace_Wplus] at this; norm_num at this
      · exact h
    -- cos θ₂ > 0 everywhere
    have hcos : ∀ t, 0 < Real.cos (θ₂ t) := by
      intro t
      have := rhoHat_re_pos (χ t) (hsymp t) (by linarith [hpos t])
      rw [show rhoHat (χ t) = _ from hθ₂.2 t, Complex.exp_mul_I] at this
      simpa [← Complex.ofReal_cos, ← Complex.ofReal_sin] using this
    obtain ⟨m, hm⟩ := FiniteEnergyPlane.exists_int_forall_mem_Ioo_of_forall_ne θ₂ hθ₂.1
      (Real.pi / 2) Real.pi hpi (by
        intro t m e
        have := hcos t
        rw [e, add_comm, Real.cos_add_pi_div_two, Real.sin_int_mul_pi] at this
        simp at this)
    obtain ⟨n₂, hn₂⟩ : ∃ n : ℤ, θ₂ 1 = 2 * Real.pi * n := by
      apply exp_eq_one_int
      rw [← hθ₂.2 1]; show rhoHat (χ 1) = 1; rw [hW]; exact rhoHat_Wminus
    -- the window is centred at θ₂ 1
    have hc : 2 * n₂ = m + 1 := by
      obtain ⟨a1, a2⟩ := hm 1
      rw [hn₂] at a1 a2
      apply int_eq_of_lt
      · push_cast
        nlinarith
      · push_cast
        nlinarith
    have hinc : |θ₂ 1 - θ₂ 0| < Real.pi / 2 := by
      obtain ⟨a1, a2⟩ := hm 0
      have hc' : (2 * n₂ : ℝ) = m + 1 := by exact_mod_cast hc
      rw [abs_lt]; constructor <;> nlinarith
    have hT : n₂ - n₀ - n₁ = k := by
      rw [abs_lt] at hk hinc
      apply int_eq_of_lt
      · push_cast; nlinarith
      · push_cast; nlinarith
    refine czIndex_eq_of_value ψ hψ ⟨χ, ⟨hχ0, hχs, hχ1⟩, θ, θ₂, hθ, hθ₂, ?_⟩
    rw [hn₀, hn₁, hn₂, ← hT]; push_cast; ring
  · intro htr hk1 hk2
    have hneg : ∀ t, ¬ 2 < (χ t).trace := fun t h => absurd ((hside t).1 h) (by linarith)
    have hlt : ∀ t, (χ t).trace < 2 := fun t =>
      lt_of_le_of_ne (not_lt.1 (hneg t)) (htr2 t)
    have hW : χ 1 = Wplus 1 := by
      rcases hχ1 with h | h
      · exact h
      · have := hlt 1; rw [h, trace_Wminus] at this; norm_num at this
    obtain ⟨m, hm⟩ := FiniteEnergyPlane.exists_int_forall_mem_Ioo_of_forall_ne θ₂ hθ₂.1
      0 (2 * Real.pi) (by linarith) (by
        intro t m e
        apply rhoHat_ne_one (χ t) (hsymp t) (hlt t)
        rw [show rhoHat (χ t) = _ from hθ₂.2 t, e]
        rw [Complex.exp_eq_one_iff]
        exact ⟨m, by push_cast; ring⟩)
    obtain ⟨n₂, hn₂⟩ : ∃ n : ℤ, θ₂ 1 = Real.pi + 2 * Real.pi * n := by
      apply exp_eq_neg_one_int
      rw [← hθ₂.2 1]; show rhoHat (χ 1) = -1; rw [hW]; exact rhoHat_Wplus
    have hc : n₂ = m := by
      obtain ⟨a1, a2⟩ := hm 1
      rw [hn₂] at a1 a2
      apply int_eq_of_lt
      · nlinarith
      · nlinarith
    have hinc : |θ₂ 1 - θ₂ 0| < Real.pi := by
      obtain ⟨a1, a2⟩ := hm 0
      have hc' : (n₂ : ℝ) = m := by exact_mod_cast hc
      rw [abs_lt]; constructor <;> nlinarith
    have hT : n₂ - n₀ - n₁ = k := by
      rw [abs_lt] at hinc
      apply int_eq_of_lt
      · push_cast; nlinarith
      · push_cast; nlinarith
    refine czIndex_eq_of_value ψ hψ ⟨χ, ⟨hχ0, hχs, hχ1⟩, θ, θ₂, hθ, hθ₂, ?_⟩
    rw [hn₀, hn₁, hn₂, ← hT]; push_cast; ring

end CZB1

open ConleyZehnder

theorem solution (ψ : C(unitInterval, Mat 1)) (hψ : ψ ∈ SP 1)
    (θ : unitInterval → ℝ) (hθ : IsArgLift (fun t => rhoHat (ψ t)) θ) (k : ℤ) :
    (2 < (ψ 1).trace → |θ 1 - θ 0 - 2 * Real.pi * k| < Real.pi / 2 → czIndex ψ = 2 * k) ∧
    ((ψ 1).trace < 2 → 2 * Real.pi * k < θ 1 - θ 0 → θ 1 - θ 0 < 2 * Real.pi * k + 2 * Real.pi →
      czIndex ψ = 2 * k + 1) :=
  CZB1.czIndex_one_eq_of_rhoHat_lift ψ hψ θ hθ k
