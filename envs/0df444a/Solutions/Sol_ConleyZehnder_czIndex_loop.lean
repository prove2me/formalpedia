-- Prove2me | solution 1 for ConleyZehnder.czIndex_loop
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-10T07:10:21.374756+00:00
-- url     : https://prove2.me/submissions/3cbe7ecd-f306-4730-8da0-ebd1440693e5

import Theorems.Thm_ConleyZehnder_czValue_existsUnique
import Theorems.Thm_ConleyZehnder_maslovValue_existsUnique
import Theorems.Thm_ConleyZehnder_czIndex_eq_of_family
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Loop axiom for the Conley–Zehnder index

The pointwise product `φ * ψ` of a based symplectic loop and a path in `SP(n)` is joined,
inside `SP(n)`, to the concatenation of `φ` and `ψ`. Concatenation adds argument increments
of `ρ̂`, and the Maslov index is that increment divided by `2π`, so
`μ_CZ(φψ) = μ_CZ(ψ) + 2 μ(φ)`.
-/

namespace CZLoop

open ConleyZehnder Classical

variable {n : ℕ}

lemma complexLinearPart_one : complexLinearPart (1 : Mat n) = 1 := by
  unfold complexLinearPart
  rw [mul_one, Matrix.J_squared (Fin n) ℝ, sub_neg_eq_add, ← two_smul ℝ (1 : Mat n), smul_smul]
  norm_num

lemma rhoHat_one : rhoHat (1 : Mat n) = 1 := by
  unfold rhoHat complexLinearDet
  rw [complexLinearPart_one]
  have hblocks : (1 : Mat n) =
      Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 1 :=
    Matrix.fromBlocks_one.symm
  rw [hblocks, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₁]
  simp [Matrix.map_one, Matrix.map_zero, Matrix.det_one, Complex.ofReal_one, Complex.ofReal_zero,
    smul_zero, add_zero, norm_one]

/-- First half of a concatenation, frozen at `1` after time `1/2`. -/
noncomputable def clampDouble (t : unitInterval) : unitInterval :=
  ⟨min (2 * (t : ℝ)) 1, by
    refine ⟨le_min (mul_nonneg zero_le_two t.2.1) zero_le_one, min_le_right _ _⟩⟩

/-- Second half of a concatenation, frozen at `0` before time `1/2`. -/
noncomputable def clampSecond (t : unitInterval) : unitInterval :=
  ⟨max (2 * (t : ℝ) - 1) 0, by
    refine ⟨le_max_right _ _, max_le (by linarith [t.2.2]) zero_le_one⟩⟩

lemma continuous_clampDouble : Continuous clampDouble := by
  refine Continuous.subtype_mk ?_ _
  fun_prop

lemma continuous_clampSecond : Continuous clampSecond := by
  refine Continuous.subtype_mk ?_ _
  fun_prop

lemma clampDouble_zero : clampDouble 0 = 0 := by
  apply Subtype.ext
  simp [clampDouble]

lemma clampSecond_zero : clampSecond 0 = 0 := by
  apply Subtype.ext
  simp [clampSecond]

lemma clampDouble_one : clampDouble 1 = 1 := by
  apply Subtype.ext
  simp [clampDouble]

lemma clampSecond_one : clampSecond 1 = 1 := by
  apply Subtype.ext
  simp [clampSecond]
  norm_num

lemma clampSecond_eq_zero_of_le {t : unitInterval} (ht : (t : ℝ) ≤ 1 / 2) : clampSecond t = 0 := by
  apply Subtype.ext
  simp only [clampSecond]
  exact max_eq_right (by linarith)

lemma clampDouble_eq_one_of_not_le {t : unitInterval} (ht : ¬ (t : ℝ) ≤ 1 / 2) :
    clampDouble t = 1 := by
  apply Subtype.ext
  simp only [clampDouble]
  exact min_eq_right (by linarith [lt_of_not_ge ht])

lemma continuous_pathConcat (φ ψ : C(unitInterval, Mat n)) (h : φ 1 = ψ 0) :
    Continuous (fun t : unitInterval =>
      if (t : ℝ) ≤ 1 / 2 then φ (clampDouble t) else ψ (clampSecond t)) := by
  refine Continuous.if_le (φ.continuous.comp continuous_clampDouble)
      (ψ.continuous.comp continuous_clampSecond) continuous_subtype_val continuous_const ?_
  intro t ht
  have hhalf : (t : ℝ) = 1 / 2 := ht
  have hd : clampDouble t = 1 := by
    apply Subtype.ext
    simp only [clampDouble, hhalf]
    norm_num
  have hs : clampSecond t = 0 := by
    apply Subtype.ext
    simp only [clampSecond, hhalf]
    norm_num
  simp [hd, hs, h]

noncomputable def pathConcat (φ ψ : C(unitInterval, Mat n)) (h : φ 1 = ψ 0) :
    C(unitInterval, Mat n) where
  toFun t := if (t : ℝ) ≤ 1 / 2 then φ (clampDouble t) else ψ (clampSecond t)
  continuous_toFun := continuous_pathConcat φ ψ h

@[simp] lemma pathConcat_apply (φ ψ : C(unitInterval, Mat n)) (h : φ 1 = ψ 0) (t : unitInterval) :
    pathConcat φ ψ h t =
      if (t : ℝ) ≤ 1 / 2 then φ (clampDouble t) else ψ (clampSecond t) := rfl

lemma pathConcat_one (φ ψ : C(unitInterval, Mat n)) (h : φ 1 = ψ 0) :
    pathConcat φ ψ h 1 = ψ 1 := by
  rw [pathConcat_apply, if_neg (by norm_num : ¬ ((1 : unitInterval) : ℝ) ≤ 1 / 2), clampSecond_one]

lemma pathConcat_mem_SP (φ ψ : C(unitInterval, Mat n)) (hφ : IsSymplecticLoop φ) (hψ : ψ ∈ SP n) :
    pathConcat φ ψ (hφ.2.2.trans hψ.2.1.symm) ∈ SP n := by
  refine ⟨?_, ?_, ?_⟩
  · intro t
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · rw [pathConcat_apply, if_pos ht]
      exact hφ.1 (clampDouble t)
    · rw [pathConcat_apply, if_neg ht]
      exact hψ.1 (clampSecond t)
  · rw [pathConcat_apply, if_pos (by norm_num : ((0 : unitInterval) : ℝ) ≤ 1 / 2),
      clampDouble_zero, hφ.2.1]
  · rw [pathConcat_one]
    exact hψ.2.2

/-- Convex combination that slides the concatenation onto the pointwise product. -/
noncomputable def sig1 (s t : unitInterval) : ℝ :=
  (1 - (s : ℝ)) * (clampDouble t : ℝ) + (s : ℝ) * (t : ℝ)

noncomputable def sig2 (s t : unitInterval) : ℝ :=
  (1 - (s : ℝ)) * (clampSecond t : ℝ) + (s : ℝ) * (t : ℝ)

lemma convex_bounds {a b u : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ (1 - u) * a + u * b ∧ (1 - u) * a + u * b ≤ 1 := by
  constructor <;> nlinarith

lemma sig1_mem (s t : unitInterval) : sig1 s t ∈ Set.Icc (0 : ℝ) 1 := by
  have h := convex_bounds (clampDouble t).2.1 (clampDouble t).2.2 t.2.1 t.2.2 s.2.1 s.2.2
  exact h

lemma sig2_mem (s t : unitInterval) : sig2 s t ∈ Set.Icc (0 : ℝ) 1 := by
  have h := convex_bounds (clampSecond t).2.1 (clampSecond t).2.2 t.2.1 t.2.2 s.2.1 s.2.2
  exact h

noncomputable def sig1u (s t : unitInterval) : unitInterval := ⟨sig1 s t, sig1_mem s t⟩

noncomputable def sig2u (s t : unitInterval) : unitInterval := ⟨sig2 s t, sig2_mem s t⟩

lemma continuous_sig1 : Continuous (fun p : unitInterval × unitInterval => sig1 p.1 p.2) := by
  unfold sig1
  fun_prop

lemma continuous_sig2 : Continuous (fun p : unitInterval × unitInterval => sig2 p.1 p.2) := by
  unfold sig2
  fun_prop

lemma continuous_sig1u : Continuous (fun p : unitInterval × unitInterval => sig1u p.1 p.2) :=
  Continuous.subtype_mk continuous_sig1 _

lemma continuous_sig2u : Continuous (fun p : unitInterval × unitInterval => sig2u p.1 p.2) :=
  Continuous.subtype_mk continuous_sig2 _

noncomputable def shuffle (φ ψ : C(unitInterval, Mat n)) :
    C(unitInterval × unitInterval, Mat n) where
  toFun p := φ (sig1u p.1 p.2) * ψ (sig2u p.1 p.2)
  continuous_toFun :=
    (φ.continuous.comp continuous_sig1u).mul (ψ.continuous.comp continuous_sig2u)

@[simp] lemma shuffle_apply (φ ψ : C(unitInterval, Mat n)) (s t : unitInterval) :
    shuffle φ ψ (s, t) = φ (sig1u s t) * ψ (sig2u s t) := rfl

lemma sig1_zero (t : unitInterval) : sig1 0 t = clampDouble t := by
  simp [sig1, sub_zero, one_mul, zero_mul, add_zero]

lemma sig2_zero (t : unitInterval) : sig2 0 t = clampSecond t := by
  simp [sig2, sub_zero, one_mul, zero_mul, add_zero]

lemma sig1_at_one (t : unitInterval) : sig1 1 t = t := by
  simp [sig1, sub_self, zero_mul, zero_add, one_mul]

lemma sig2_at_one (t : unitInterval) : sig2 1 t = t := by
  simp [sig2, sub_self, zero_mul, zero_add, one_mul]

lemma sig1_at_right (s : unitInterval) : sig1 s 1 = 1 := by
  simp [sig1, clampDouble_one]

lemma sig2_at_right (s : unitInterval) : sig2 s 1 = 1 := by
  simp [sig2, clampSecond_one]

lemma sig1_at_left (s : unitInterval) : sig1 s 0 = 0 := by
  simp [sig1, clampDouble_zero]

lemma sig2_at_left (s : unitInterval) : sig2 s 0 = 0 := by
  simp [sig2, clampSecond_zero]

lemma sig1u_zero (t : unitInterval) : sig1u 0 t = clampDouble t :=
  Subtype.ext (sig1_zero t)

lemma sig2u_zero (t : unitInterval) : sig2u 0 t = clampSecond t :=
  Subtype.ext (sig2_zero t)

lemma sig1u_at_one (t : unitInterval) : sig1u 1 t = t :=
  Subtype.ext (sig1_at_one t)

lemma sig2u_at_one (t : unitInterval) : sig2u 1 t = t :=
  Subtype.ext (sig2_at_one t)

lemma sig1u_right (s : unitInterval) : sig1u s 1 = 1 :=
  Subtype.ext (sig1_at_right s)

lemma sig2u_right (s : unitInterval) : sig2u s 1 = 1 :=
  Subtype.ext (sig2_at_right s)

lemma sig1u_left (s : unitInterval) : sig1u s 0 = 0 :=
  Subtype.ext (sig1_at_left s)

lemma sig2u_left (s : unitInterval) : sig2u s 0 = 0 :=
  Subtype.ext (sig2_at_left s)

lemma shuffle_zero (φ ψ : C(unitInterval, Mat n)) (hφ : IsSymplecticLoop φ) (hψ : ψ ∈ SP n)
    (t : unitInterval) :
    shuffle φ ψ (0, t) = pathConcat φ ψ (hφ.2.2.trans hψ.2.1.symm) t := by
  have hjoin : φ 1 = ψ 0 := hφ.2.2.trans hψ.2.1.symm
  rw [shuffle_apply, sig1u_zero, sig2u_zero]
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · rw [pathConcat_apply, if_pos ht, clampSecond_eq_zero_of_le ht, hψ.2.1, mul_one]
  · rw [pathConcat_apply, if_neg ht, clampDouble_eq_one_of_not_le ht, hφ.2.2, one_mul]

lemma shuffle_one (φ ψ : C(unitInterval, Mat n)) (t : unitInterval) :
    shuffle φ ψ (1, t) = (φ * ψ) t := by
  rw [shuffle_apply, sig1u_at_one, sig2u_at_one, ContinuousMap.mul_apply]

lemma shuffle_symplectic (φ ψ : C(unitInterval, Mat n)) (hφ : IsSymplecticLoop φ)
    (hψ : ψ ∈ SP n) (s t : unitInterval) : IsSymplectic (shuffle φ ψ (s, t)) := by
  rw [shuffle_apply, IsSymplectic]
  exact (Matrix.symplecticGroup (Fin n) ℝ).mul_mem (hφ.1 (sig1u s t)) (hψ.1 (sig2u s t))

lemma shuffle_start (φ ψ : C(unitInterval, Mat n)) (hφ : IsSymplecticLoop φ) (hψ : ψ ∈ SP n)
    (s : unitInterval) : shuffle φ ψ (s, 0) = 1 := by
  rw [shuffle_apply, sig1u_left, sig2u_left, hφ.2.1, hψ.2.1, mul_one]

lemma shuffle_end (φ ψ : C(unitInterval, Mat n)) (hφ : IsSymplecticLoop φ) (_hψ : ψ ∈ SP n)
    (s : unitInterval) : shuffle φ ψ (s, 1) = ψ 1 := by
  rw [shuffle_apply, sig1u_right, sig2u_right, hφ.2.2, one_mul]

/-- Argument of `ρ̂` along the concatenation, glued from the two lifts. -/
noncomputable def argConcat (θφ θψ : unitInterval → ℝ) (t : unitInterval) : ℝ :=
  if (t : ℝ) ≤ 1 / 2 then θφ (clampDouble t)
  else θφ 1 + θψ (clampSecond t) - θψ 0

lemma continuous_argConcat {θφ θψ : unitInterval → ℝ} (hφ : Continuous θφ) (hψ : Continuous θψ) :
    Continuous (argConcat θφ θψ) := by
  refine Continuous.if_le (hφ.comp continuous_clampDouble)
      ((continuous_const.add (hψ.comp continuous_clampSecond)).sub continuous_const)
      continuous_subtype_val continuous_const ?_
  intro t ht
  have hhalf : (t : ℝ) = 1 / 2 := ht
  have hd : clampDouble t = 1 := by
    apply Subtype.ext
    simp only [clampDouble, hhalf]
    norm_num
  have hs : clampSecond t = 0 := by
    apply Subtype.ext
    simp only [clampSecond, hhalf]
    norm_num
  simp [hd, hs]

lemma argConcat_delta (θφ θψ : unitInterval → ℝ) :
    argConcat θφ θψ 1 - argConcat θφ θψ 0 = (θφ 1 - θφ 0) + (θψ 1 - θψ 0) := by
  simp only [argConcat]
  rw [if_pos (by norm_num : ((0 : unitInterval) : ℝ) ≤ 1 / 2),
    if_neg (by norm_num : ¬ ((1 : unitInterval) : ℝ) ≤ 1 / 2),
    clampDouble_zero, clampSecond_one]
  ring

lemma exp_arg_split (a b c : ℝ) :
    Complex.exp (((a + b - c : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((a : ℂ) * Complex.I) * Complex.exp ((b : ℂ) * Complex.I) *
        (Complex.exp ((c : ℂ) * Complex.I))⁻¹ := by
  have hsum : (a + b - c : ℝ) = a + b + (-c) := by ring
  rw [hsum]
  push_cast
  rw [add_mul, add_mul, Complex.exp_add, Complex.exp_add, ← Complex.exp_neg, neg_mul]

lemma argConcat_lifts (φ ψ : C(unitInterval, Mat n)) (h : φ 1 = ψ 0)
    (θφ θψ : unitInterval → ℝ)
    (hθφ : IsArgLift (fun t => rhoHat (φ t)) θφ)
    (hθψ : IsArgLift (fun t => rhoHat (ψ t)) θψ)
    (hφ1 : φ 1 = 1) (hψ0 : ψ 0 = 1) (t : unitInterval) :
    rhoHat (pathConcat φ ψ h t) =
      Complex.exp (((argConcat θφ θψ t : ℝ) : ℂ) * Complex.I) := by
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · rw [pathConcat_apply, if_pos ht, argConcat, if_pos ht]
    exact hθφ.2 (clampDouble t)
  · rw [pathConcat_apply, if_neg ht, argConcat, if_neg ht, exp_arg_split]
    have hφexp : Complex.exp (((θφ 1 : ℝ) : ℂ) * Complex.I) = rhoHat (φ 1) := (hθφ.2 1).symm
    have hψexp : Complex.exp (((θψ (clampSecond t) : ℝ) : ℂ) * Complex.I) =
        rhoHat (ψ (clampSecond t)) := (hθψ.2 _).symm
    have h0exp : Complex.exp (((θψ 0 : ℝ) : ℂ) * Complex.I) = rhoHat (ψ 0) := (hθψ.2 0).symm
    rw [hφexp, hψexp, h0exp, hφ1, hψ0, rhoHat_one]
    simp [inv_one, one_mul, mul_one]

lemma isCZValue_czIndex (ψ : C(unitInterval, Mat n)) (hψ : ψ ∈ SP n) :
    IsCZValue ψ (czIndex ψ) := by
  have hexu := czValue_existsUnique ψ hψ
  have hex : ∃ k, IsCZValue ψ k := hexu.exists
  simpa [czIndex, dif_pos hex] using hex.choose_spec

lemma czIndex_unique_value (ψ : C(unitInterval, Mat n)) (hψ : ψ ∈ SP n) {k : ℤ}
    (hk : IsCZValue ψ k) : czIndex ψ = k :=
  (czValue_existsUnique ψ hψ).unique (isCZValue_czIndex ψ hψ) hk

lemma isMaslovValue_maslovIndex (φ : C(unitInterval, Mat n)) (hφ : IsSymplecticLoop φ) :
    IsMaslovValue φ (maslovIndex φ) := by
  have hexu := maslovValue_existsUnique φ hφ
  have hex : ∃ k, IsMaslovValue φ k := hexu.exists
  simpa [maslovIndex, dif_pos hex] using hex.choose_spec

lemma maslovIndex_unique_value (φ : C(unitInterval, Mat n)) (hφ : IsSymplecticLoop φ) {k : ℤ}
    (hk : IsMaslovValue φ k) : maslovIndex φ = k :=
  (maslovValue_existsUnique φ hφ).unique (isMaslovValue_maslovIndex φ hφ) hk

lemma czIndex_concat (φ ψ : C(unitInterval, Mat n)) (hφ : IsSymplecticLoop φ) (hψ : ψ ∈ SP n) :
    czIndex (pathConcat φ ψ (hφ.2.2.trans hψ.2.1.symm)) =
      czIndex ψ + 2 * maslovIndex φ := by
  rcases isCZValue_czIndex ψ hψ with ⟨χ, hχ, θψ, θχ, hθψ, hθχ, hsum⟩
  rcases isMaslovValue_maslovIndex φ hφ with ⟨θφ, hθφ, hΔφ⟩
  let γ := pathConcat φ ψ (hφ.2.2.trans hψ.2.1.symm)
  let θc : unitInterval → ℝ := argConcat θφ θψ
  have hcont : Continuous θc := continuous_argConcat hθφ.1 hθψ.1
  have hlift : IsArgLift (fun t => rhoHat (γ t)) θc := by
    refine ⟨hcont, ?_⟩
    intro t
    exact argConcat_lifts φ ψ _ θφ θψ hθφ hθψ hφ.2.2 hψ.2.1 t
  have hext : IsSpStarExtension γ χ := by
    refine ⟨?_, hχ.2.1, hχ.2.2⟩
    rw [hχ.1]
    exact (pathConcat_one φ ψ _).symm
  have hΔ : θc 1 - θc 0 = (θφ 1 - θφ 0) + (θψ 1 - θψ 0) := argConcat_delta θφ θψ
  have hval : IsCZValue γ (czIndex ψ + 2 * maslovIndex φ) := by
    refine ⟨χ, hext, θc, θχ, hlift, hθχ, ?_⟩
    have hr :
        2 * ((θφ 1 - θφ 0) + ((θψ 1 - θψ 0) + (θχ 1 - θχ 0))) =
          2 * Real.pi * ((czIndex ψ + 2 * maslovIndex φ : ℤ) : ℝ) := by
      calc
        2 * ((θφ 1 - θφ 0) + ((θψ 1 - θψ 0) + (θχ 1 - θχ 0)))
            = 2 * (θφ 1 - θφ 0) + 2 * ((θψ 1 - θψ 0) + (θχ 1 - θχ 0)) := by ring
        _ = 2 * (2 * Real.pi * (maslovIndex φ : ℝ)) +
              2 * Real.pi * (czIndex ψ : ℝ) := by rw [hΔφ, hsum]
        _ = 2 * Real.pi * ((czIndex ψ + 2 * maslovIndex φ : ℤ) : ℝ) := by
          push_cast
          ring
    calc
      2 * ((θc 1 - θc 0) + (θχ 1 - θχ 0))
          = 2 * ((θφ 1 - θφ 0) + (θψ 1 - θψ 0) + (θχ 1 - θχ 0)) := by rw [hΔ]
      _ = 2 * ((θφ 1 - θφ 0) + ((θψ 1 - θψ 0) + (θχ 1 - θχ 0))) := by ring
      _ = 2 * Real.pi * ((czIndex ψ + 2 * maslovIndex φ : ℤ) : ℝ) := hr
  exact czIndex_unique_value γ (pathConcat_mem_SP φ ψ hφ hψ) hval

lemma czIndex_mul_eq_concat (φ ψ : C(unitInterval, Mat n)) (hφ : IsSymplecticLoop φ)
    (hψ : ψ ∈ SP n) :
    czIndex (φ * ψ) = czIndex (pathConcat φ ψ (hφ.2.2.trans hψ.2.1.symm)) := by
  let H := shuffle φ ψ
  have hjoin : φ 1 = ψ 0 := hφ.2.2.trans hψ.2.1.symm
  exact czIndex_eq_of_family H (shuffle_symplectic φ ψ hφ hψ)
    (shuffle_start φ ψ hφ hψ)
    (fun s => by
      rw [shuffle_end φ ψ hφ hψ]
      exact hψ.2.2)
    (pathConcat φ ψ hjoin) (φ * ψ)
    (fun t => (shuffle_zero φ ψ hφ hψ t).symm)
    (fun t => (shuffle_one φ ψ t).symm)

theorem czIndex_loop (n : ℕ) : LoopAxiom (czIndex (n := n)) := by
  intro φ hφ ψ hψ
  have hmem : φ * ψ ∈ SP n := by
    refine ⟨?_, ?_, ?_⟩
    · intro t
      exact (Matrix.symplecticGroup (Fin n) ℝ).mul_mem (hφ.1 t) (hψ.1 t)
    · simp [hφ.2.1, hψ.2.1]
    · simpa [hφ.2.2] using hψ.2.2
  rw [czIndex_mul_eq_concat φ ψ hφ hψ, czIndex_concat φ ψ hφ hψ]

end CZLoop

open ConleyZehnder

theorem solution (n : ℕ) : LoopAxiom (czIndex (n := n)) :=
  CZLoop.czIndex_loop n
