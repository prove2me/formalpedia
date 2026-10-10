-- Prove2me | solution 1 for ConleyZehnder.czIndex_characterization
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-10T08:22:27.440179+00:00
-- url     : https://prove2.me/submissions/07684640-08b8-4e86-8fb7-e6d1badb896e

import Definitions.Def_ConleyZehnder_Setting
import Theorems.Thm_ConleyZehnder_czValue_existsUnique
import Theorems.Thm_ConleyZehnder_maslovValue_existsUnique
import Theorems.Thm_ConleyZehnder_czIndex_eq_of_family
import Theorems.Thm_ConleyZehnder_czIndex_homotopy
import Theorems.Thm_ConleyZehnder_czIndex_loop
import Theorems.Thm_ConleyZehnder_czIndex_signature
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Order.OrderClosed

/-!
# Characterization of the Conley–Zehnder index

`μ_CZ` satisfies the homotopy, loop, and signature axioms, and any integer invariant
of paths in `SP(n)` that satisfies the same three axioms agrees with `μ_CZ`.
-/


namespace CZSig

open ConleyZehnder Matrix NormedSpace

noncomputable section

variable {n : ℕ}

local instance : NormedAddCommGroup (Mat n) := Matrix.linftyOpNormedAddCommGroup
local instance : NormedSpace ℝ (Mat n) := Matrix.linftyOpNormedSpace
local instance : NormedRing (Mat n) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra

lemma hermitian_transpose {S : Mat n} (hS : S.IsHermitian) : Sᵀ = S := by
  simpa [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hS

lemma infSymm (S : Mat n) (hS : S.IsHermitian) :
    (J₀ n * S) * J₀ n + J₀ n * (J₀ n * S)ᵀ = 0 := by
  have hST : Sᵀ = S := hermitian_transpose hS
  simp only [transpose_mul, J_transpose, hST, Matrix.mul_neg, Matrix.mul_assoc]
  abel

lemma exp_transpose_smul (X : Mat n) (u : ℝ) : (exp (u • X))ᵀ = exp (u • Xᵀ) := by
  rw [← exp_transpose, transpose_smul]

/-- `exp (t • J₀ S)` is symplectic. -/
lemma exp_smul_isSymplectic (S : Mat n) (hS : S.IsHermitian) (t : ℝ) :
    IsSymplectic (exp (t • (J₀ n * S))) := by
  let X : Mat n := J₀ n * S
  have hX : X * J₀ n + J₀ n * Xᵀ = 0 := by simpa [X] using infSymm S hS
  have hX' : X * J₀ n = -(J₀ n * Xᵀ) := (add_eq_zero_iff_eq_neg).1 hX
  let f : ℝ → Mat n := fun u => exp (u • X) * J₀ n * exp (u • Xᵀ)
  have hzero : ∀ u, HasDerivAt f 0 u := by
    intro u
    have h1 : HasDerivAt (fun v : ℝ => exp (v • X)) (exp (u • X) * X) u :=
      hasDerivAt_exp_smul_const X u
    have h1' : HasDerivAt (fun v : ℝ => exp (v • Xᵀ)) (exp (u • Xᵀ) * Xᵀ) u :=
      hasDerivAt_exp_smul_const Xᵀ u
    have ha : HasDerivAt (fun v => exp (v • X) * J₀ n) ((exp (u • X) * X) * J₀ n) u :=
      h1.mul_const _
    have hmul : HasDerivAt f
        ((exp (u • X) * X) * J₀ n * exp (u • Xᵀ) +
          exp (u • X) * J₀ n * (exp (u • Xᵀ) * Xᵀ)) u :=
      ha.mul h1'
    have hFX : exp (u • Xᵀ) * Xᵀ = Xᵀ * exp (u • Xᵀ) :=
      ((Commute.refl Xᵀ).smul_left u).exp_left.eq
    set E : Mat n := exp (u • X)
    set F : Mat n := exp (u • Xᵀ)
    have hJX : J₀ n * Xᵀ = -(X * J₀ n) := by
      have hneg : -(J₀ n * Xᵀ) = X * J₀ n := hX'.symm
      calc
        J₀ n * Xᵀ = -(-(J₀ n * Xᵀ)) := by rw [neg_neg]
        _ = -(X * J₀ n) := by rw [hneg]
    have hsum :
        (E * X) * J₀ n * F + E * J₀ n * (F * Xᵀ) = 0 := by
      calc
        (E * X) * J₀ n * F + E * J₀ n * (F * Xᵀ)
          = E * (X * J₀ n) * F + E * J₀ n * (Xᵀ * F) := by
            rw [hFX]; simp only [Matrix.mul_assoc]
        _ = E * (X * J₀ n) * F + E * (J₀ n * Xᵀ) * F := by
            simp only [Matrix.mul_assoc]
        _ = E * (X * J₀ n) * F + E * (-(X * J₀ n)) * F := by rw [hJX]
        _ = E * (X * J₀ n) * F + -(E * (X * J₀ n) * F) := by
            simp [Matrix.mul_assoc]
        _ = 0 := add_neg_cancel _
    exact hmul.congr_deriv hsum
  have hconst : f t = f 0 := by
    have hle := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := f) (f' := fun _ : ℝ => (0 : Mat n)) (s := Set.univ) (C := 0) (x := t) (y := 0)
      (fun x _ => (hzero x).hasDerivWithinAt) (fun _ _ => by simp) (by trivial) (by trivial)
    exact (sub_eq_zero.1 (norm_le_zero_iff.1 (by simpa using hle))).symm
  have h0 : f 0 = J₀ n := by simp [f, exp_zero]
  rw [IsSymplectic, SymplecticGroup.mem_iff]
  calc
    exp (t • X) * J₀ n * (exp (t • X))ᵀ = exp (t • X) * J₀ n * exp (t • Xᵀ) := by
      rw [exp_transpose_smul]
    _ = f t := rfl
    _ = f 0 := hconst
    _ = J₀ n := h0

end

end CZSig


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


/-!
# Uniqueness of the Conley–Zehnder index

A path in `SP(n)` is joined to its prolongation out to `W⁺` or `W⁻`. That prolongation is
joined to the product of a based loop with the model path `exp(t J₀ S±)`. The loop axiom
removes the loop, and the signature axiom evaluates the model.
-/

namespace CZUnique

open ConleyZehnder Classical Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {n : ℕ}

local instance : NormedAlgebra ℚ (Mat n) := NormedAlgebra.restrictScalars ℚ ℝ (Mat n)

lemma const_of_deriv_zero {f : ℝ → Mat n} (hf : ∀ u, HasDerivAt f 0 u) (u : ℝ) : f u = f 0 := by
  have hle := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := fun _ : ℝ => (0 : Mat n)) (s := Set.univ) (C := 0) (x := u) (y := 0)
    (fun x _ => (hf x).hasDerivWithinAt) (fun _ _ => by simp) (by trivial) (by trivial)
  exact (sub_eq_zero.1 (norm_le_zero_iff.1 (by simpa using hle))).symm

lemma eq_exp_of_ode (X : Mat n) (g : ℝ → Mat n) (hg0 : g 0 = 1)
    (hg : ∀ u, HasDerivAt g (X * g u) u) (u : ℝ) : g u = exp (u • X) := by
  let p : ℝ → Mat n := fun v => exp (v • (-X)) * g v
  have hp : ∀ v, HasDerivAt p 0 v := by
    intro v
    have hmul := (hasDerivAt_exp_smul_const (-X) v).mul (hg v)
    refine hmul.congr_deriv ?_
    calc
      (exp (v • -X) * -X) * g v + exp (v • -X) * (X * g v)
          = exp (v • -X) * (-X * g v) + exp (v • -X) * (X * g v) := by
            rw [Matrix.mul_assoc]
      _ = exp (v • -X) * (-X * g v + X * g v) := by rw [← Matrix.mul_add]
      _ = exp (v • -X) * ((-X + X) * g v) := by rw [← Matrix.add_mul]
      _ = 0 := by simp
  have hconst := const_of_deriv_zero hp u
  have hp0 : p 0 = 1 := by simp [p, exp_zero, zero_smul, hg0]
  have hpu : exp (u • -X) * g u = 1 := by simpa [p] using hconst.trans hp0
  have hcomm : Commute (u • X) (u • -X) := by
    simpa [smul_neg] using (Commute.refl (u • X)).neg_right
  have hinv : exp (u • X) * exp (u • -X) = 1 := by
    rw [← exp_add_of_commute hcomm]
    simp [smul_neg, add_neg_cancel, exp_zero]
  calc
    g u = exp (u • X) * (exp (u • -X) * g u) := by
      rw [← Matrix.mul_assoc, hinv, one_mul]
    _ = exp (u • X) := by rw [hpu, mul_one]

def rot (u : ℝ) : Mat n := Real.cos u • (1 : Mat n) + Real.sin u • J₀ n

lemma hasDerivAt_rot (u : ℝ) : HasDerivAt (rot : ℝ → Mat n) (J₀ n * rot u) u := by
  have hg := ((Real.hasDerivAt_cos u).smul_const (1 : Mat n)).add
    ((Real.hasDerivAt_sin u).smul_const (J₀ n))
  have hEq : -Real.sin u • (1 : Mat n) + Real.cos u • J₀ n = J₀ n * rot u := by
    unfold rot
    rw [Matrix.mul_add,
      Matrix.mul_smul (J₀ n) (Real.cos u) (1 : Mat n),
      Matrix.mul_smul (J₀ n) (Real.sin u) (J₀ n),
      Matrix.mul_one, J_squared (Fin n) ℝ, smul_neg, ← neg_smul]
    exact add_comm _ _
  exact hg.congr_deriv hEq

lemma rot_zero : rot (n := n) (0 : ℝ) = 1 := by
  simp [rot, Real.cos_zero, Real.sin_zero, one_smul, zero_smul]

lemma exp_smul_J (u : ℝ) : exp (u • J₀ n) = rot u := by
  symm
  exact eq_exp_of_ode (J₀ n) rot rot_zero hasDerivAt_rot u

lemma exp_pi_J : exp ((Real.pi : ℝ) • J₀ n) = Wplus n := by
  rw [exp_smul_J, rot, Real.cos_pi, Real.sin_pi, Wplus]
  simp

def sPlus : Mat n := Real.pi • (1 : Mat n)

lemma sPlus_herm : (sPlus : Mat n).IsHermitian := by
  rw [sPlus, Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial, Matrix.transpose_smul,
    Matrix.transpose_one]

lemma sPlus_eigen (i : Fin n ⊕ Fin n) : sPlus_herm.eigenvalues i = Real.pi := by
  have hv := sPlus_herm.mulVec_eigenvectorBasis i
  have hv' : sPlus *ᵥ ⇑(sPlus_herm.eigenvectorBasis i) =
      Real.pi • ⇑(sPlus_herm.eigenvectorBasis i) := by
    unfold sPlus
    rw [smul_mulVec, one_mulVec]
  rw [hv'] at hv
  have hne : ⇑(sPlus_herm.eigenvectorBasis i) ≠ 0 := by
    intro hz
    rw [WithLp.ofLp_eq_zero] at hz
    have hnorm := sPlus_herm.eigenvectorBasis.orthonormal.norm_eq_one i
    rw [hz, norm_zero] at hnorm
    exact one_ne_zero hnorm.symm
  have hsub : (Real.pi - sPlus_herm.eigenvalues i) • ⇑(sPlus_herm.eigenvectorBasis i) = 0 := by
    rw [sub_smul, hv, sub_self]
  rcases smul_eq_zero.mp hsub with h0 | h0
  · exact (sub_eq_zero.mp h0).symm
  · exact absurd h0 hne

lemma sPlus_bound (i : Fin n ⊕ Fin n) : |sPlus_herm.eigenvalues i| < 2 * Real.pi := by
  rw [sPlus_eigen]
  have hp : 0 < Real.pi := Real.pi_pos
  rw [abs_of_pos hp]
  linarith

lemma sPlus_det : (sPlus : Mat n).det ≠ 0 := by
  rw [sPlus, det_smul, det_one]
  exact mul_ne_zero (pow_ne_zero _ Real.pi_ne_zero) one_ne_zero

def hamPath (S : Mat n) : C(unitInterval, Mat n) where
  toFun t := exp (((t : ℝ)) • (J₀ n * S))
  continuous_toFun := exp_continuous.comp <|
    continuous_subtype_val.smul continuous_const

lemma hamPath_apply (S : Mat n) (t : unitInterval) :
    hamPath S t = exp (((t : ℝ)) • (J₀ n * S)) := rfl

lemma ham_plus_one : hamPath sPlus 1 = Wplus n := by
  rw [hamPath_apply]
  have hJ : J₀ n * sPlus = Real.pi • J₀ n := by
    rw [sPlus, Matrix.mul_smul, Matrix.mul_one]
  rw [hJ, smul_smul]
  have hone : ((1 : unitInterval) : ℝ) = 1 := rfl
  rw [hone, one_mul]
  exact exp_pi_J

lemma det_one_sub_Wplus : ((1 : Mat n) - Wplus n).det ≠ 0 := by
  rw [Wplus, sub_neg_eq_add]
  have h2 : (1 : Mat n) + 1 = (2 : ℝ) • (1 : Mat n) := by rw [two_smul]
  rw [h2, Matrix.det_smul, Matrix.det_one]
  exact mul_ne_zero (pow_ne_zero _ two_ne_zero) one_ne_zero

lemma ham_plus_mem_SP : hamPath sPlus ∈ SP n := by
  refine ⟨?_, ?_, ?_⟩
  · intro t
    simpa [hamPath_apply, sPlus, Matrix.mul_smul, Matrix.mul_one] using
      CZSig.exp_smul_isSymplectic sPlus sPlus_herm (t : ℝ)
  · simp [hamPath_apply, zero_smul, exp_zero]
  · rw [ham_plus_one]
    exact det_one_sub_Wplus

/-- `S⁻`, in the `(q, p)` splitting: the `0`-plane carries `± log 2` and the rest is `π Id`. -/
def diagQ (j : Fin n) : ℝ := if j.val = 0 then 0 else Real.pi

def diagB (j : Fin n) : ℝ := if j.val = 0 then -Real.log 2 else 0

def sNeg : Mat n :=
  Matrix.fromBlocks (Matrix.diagonal diagQ) (Matrix.diagonal diagB)
    (Matrix.diagonal diagB) (Matrix.diagonal diagQ)

lemma sNeg_sq : sNeg ^ 2 =
    fromBlocks
      (diagonal fun j : Fin n => if j.val = 0 then (Real.log 2) ^ 2 else Real.pi ^ 2) 0 0
      (diagonal fun j : Fin n => if j.val = 0 then (Real.log 2) ^ 2 else Real.pi ^ 2) := by
  classical
  simp only [sNeg, pow_two, Matrix.fromBlocks_multiply]
  have hAB : diagonal (diagQ : Fin n → ℝ) * diagonal (diagB : Fin n → ℝ) = 0 := by
    ext j k
    simp only [Matrix.mul_diagonal, Matrix.diagonal_apply, Matrix.zero_apply, diagQ, diagB]
    by_cases hj : j = k
    · subst hj
      by_cases h0 : j.val = 0 <;> simp [h0]
    · simp [hj]
  have hBA : diagonal (diagB : Fin n → ℝ) * diagonal (diagQ : Fin n → ℝ) = 0 := by
    ext j k
    simp only [Matrix.mul_diagonal, Matrix.diagonal_apply, Matrix.zero_apply, diagQ, diagB]
    by_cases hj : j = k
    · subst hj
      by_cases h0 : j.val = 0 <;> simp [h0]
    · simp [hj]
  simp [hAB, hBA, Matrix.diagonal_mul_diagonal, diagQ, diagB]
  constructor <;> intro j <;> by_cases h0 : j.val = 0 <;> simp [h0]

def sNegSqEntry : Fin n ⊕ Fin n → ℝ
  | Sum.inl j => if j.val = 0 then (Real.log 2) ^ 2 else Real.pi ^ 2
  | Sum.inr j => if j.val = 0 then (Real.log 2) ^ 2 else Real.pi ^ 2

lemma sNeg_sq_diag : (sNeg : Mat n) ^ 2 = diagonal (sNegSqEntry : (Fin n ⊕ Fin n) → ℝ) := by
  rw [sNeg_sq, fromBlocks_diagonal]
  congr
  ext i
  cases i <;> rfl

lemma sNeg_herm : (sNeg : Mat n).IsHermitian := by
  rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial, sNeg]
  simp [fromBlocks_transpose, diagonal_transpose]

lemma sNegSqEntry_root (i : Fin n ⊕ Fin n) :
    (sNegSqEntry i - (Real.log 2) ^ 2) * (sNegSqEntry i - Real.pi ^ 2) = 0 := by
  cases i with
  | inl j =>
    by_cases h : j.val = 0 <;> simp [sNegSqEntry, h, sub_self]
  | inr j =>
    by_cases h : j.val = 0 <;> simp [sNegSqEntry, h, sub_self]

lemma sNeg_annihilator :
    ((sNeg : Mat n) ^ 2 - (Real.log 2) ^ 2 • (1 : Mat n)) *
      ((sNeg : Mat n) ^ 2 - Real.pi ^ 2 • (1 : Mat n)) = 0 := by
  have hone : (1 : Mat n) = diagonal fun _ : Fin n ⊕ Fin n => (1 : ℝ) := diagonal_one.symm
  rw [sNeg_sq_diag, hone, ← diagonal_smul, ← diagonal_smul, diagonal_sub, diagonal_sub,
    diagonal_mul_diagonal]
  ext i j
  simp only [diagonal_apply, Matrix.zero_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  by_cases hij : i = j
  · simp [hij, sNegSqEntry_root]
  · simp [hij]

lemma sNeg_eigen_sq (i : Fin n ⊕ Fin n) :
    sNeg_herm.eigenvalues i ^ 2 = (Real.log 2) ^ 2 ∨
      sNeg_herm.eigenvalues i ^ 2 = Real.pi ^ 2 := by
  let v := ⇑(sNeg_herm.eigenvectorBasis i)
  have hv := sNeg_herm.mulVec_eigenvectorBasis i
  have hv2 : (sNeg ^ 2) *ᵥ v =
      (sNeg_herm.eigenvalues i * sNeg_herm.eigenvalues i) • v := by
    rw [pow_two, ← mulVec_mulVec, hv, mulVec_smul, hv, smul_smul]
  have hact (c : ℝ) : (sNeg ^ 2 - c • (1 : Mat n)) *ᵥ v =
      (sNeg_herm.eigenvalues i * sNeg_herm.eigenvalues i - c) • v := by
    rw [sub_mulVec, hv2, smul_mulVec, one_mulVec, sub_smul]
  have hzero :
      ((sNeg_herm.eigenvalues i * sNeg_herm.eigenvalues i - (Real.log 2) ^ 2) *
        (sNeg_herm.eigenvalues i * sNeg_herm.eigenvalues i - Real.pi ^ 2)) • v = 0 := by
    have hmul := sNeg_annihilator (n := n)
    have : ((sNeg ^ 2 - (Real.log 2) ^ 2 • (1 : Mat n)) *
        (sNeg ^ 2 - Real.pi ^ 2 • (1 : Mat n))) *ᵥ v = 0 := by
      rw [hmul, zero_mulVec]
    rw [← mulVec_mulVec, hact, mulVec_smul, hact, smul_smul] at this
    simpa [mul_comm] using this
  have hne : v ≠ 0 := by
    intro hz
    have hnorm := sNeg_herm.eigenvectorBasis.orthonormal.norm_eq_one i
    rw [WithLp.ofLp_eq_zero] at hz
    rw [hz, norm_zero] at hnorm
    exact one_ne_zero hnorm.symm
  rcases smul_eq_zero.mp hzero with hprod | hv0
  · rcases mul_eq_zero.mp hprod with h | h
    · have h' := sub_eq_zero.mp h
      rw [← pow_two] at h'
      exact Or.inl h'
    · have h' := sub_eq_zero.mp h
      rw [← pow_two] at h'
      exact Or.inr h'
  · exact absurd hv0 hne

lemma abs_log_two_lt : |Real.log 2| < 2 * Real.pi := by
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  rw [abs_of_pos hpos]
  have hlog : Real.log 2 < 1 := by
    have h2 : (1 : ℝ) + 1 < Real.exp 1 := Real.add_one_lt_exp (by norm_num)
    exact (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).mpr (by linarith)
  linarith [Real.two_le_pi, hlog]

lemma sNeg_bound (i : Fin n ⊕ Fin n) : |sNeg_herm.eigenvalues i| < 2 * Real.pi := by
  rcases sNeg_eigen_sq i with h | h
  · rw [sq_eq_sq_iff_abs_eq_abs] at h
    rw [h]
    exact abs_log_two_lt
  · rw [sq_eq_sq_iff_abs_eq_abs] at h
    rw [h, abs_of_pos Real.pi_pos]
    linarith [Real.pi_pos]

lemma sNeg_det : (sNeg : Mat n).det ≠ 0 := by
  rw [sNeg_herm.det_eq_prod_eigenvalues]
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro i _
  intro hz
  have hz0 : sNeg_herm.eigenvalues i = 0 := by exact_mod_cast hz
  rcases sNeg_eigen_sq i with h | h
  · rw [hz0, zero_pow (by decide : 2 ≠ 0)] at h
    exact (ne_of_gt (pow_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2)) 2)) h.symm
  · rw [hz0, zero_pow (by decide : 2 ≠ 0)] at h
    exact (ne_of_gt (pow_pos Real.pi_pos 2)) h.symm

def diagP (j : Fin n) : ℝ := if j.val = 0 then 0 else 1

def diagL (j : Fin n) : ℝ := if j.val = 0 then Real.log 2 else 0

def blockD : Matrix (Fin n) (Fin n) ℝ := diagonal diagP

def blockL : Matrix (Fin n) (Fin n) ℝ := diagonal diagL

def planeProj : Mat n := fromBlocks blockD 0 0 blockD

def planeRot : Mat n := fromBlocks 0 (-blockD) blockD 0

def xLog : Mat n := fromBlocks blockL 0 0 (-blockL)

lemma diagQ_eq_pi (j : Fin n) : diagQ j = Real.pi * diagP j := by
  simp only [diagQ, diagP]
  by_cases h : j.val = 0 <;> simp [h]

lemma diagB_eq_neg (j : Fin n) : diagB j = -diagL j := by
  simp only [diagB, diagL]
  by_cases h : j.val = 0 <;> simp [h]

lemma blockA_eq : diagonal (diagQ : Fin n → ℝ) = Real.pi • blockD := by
  rw [blockD, ← diagonal_smul]
  congr
  ext j
  simpa [Pi.smul_apply, smul_eq_mul] using diagQ_eq_pi j

lemma blockB_eq : diagonal (diagB : Fin n → ℝ) = -blockL := by
  ext j k
  simp only [blockL, diagonal_apply, neg_apply, diagB, diagL]
  by_cases hij : j = k
  · subst hij
    by_cases h0 : j.val = 0 <;> simp [diagL, h0]
  · simp [hij]

lemma blockD_sq : (blockD : Matrix (Fin n) (Fin n) ℝ) * blockD = blockD := by
  rw [blockD, diagonal_mul_diagonal]
  congr
  ext j
  simp only [diagP]
  by_cases h : j.val = 0 <;> simp [h]

lemma blockL_mul_D : (blockL : Matrix (Fin n) (Fin n) ℝ) * blockD = 0 := by
  rw [blockL, blockD, diagonal_mul_diagonal]
  ext j k
  simp only [diagonal_apply, Matrix.zero_apply, diagL, diagP]
  by_cases hij : j = k
  · subst hij
    by_cases h0 : j.val = 0 <;> simp [h0]
  · simp [hij]

lemma blockD_mul_L : (blockD : Matrix (Fin n) (Fin n) ℝ) * blockL = 0 := by
  rw [blockD, blockL, diagonal_mul_diagonal]
  ext j k
  simp only [diagonal_apply, Matrix.zero_apply, diagL, diagP]
  by_cases hij : j = k
  · subst hij
    by_cases h0 : j.val = 0 <;> simp [h0]
  · simp [hij]

lemma planeRot_sq : (planeRot : Mat n) * planeRot = -planeProj := by
  rw [planeRot, planeProj, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg,
    neg_zero, blockD_sq, fromBlocks_neg]

lemma planeRot_mul_proj : (planeRot : Mat n) * planeProj = planeRot := by
  rw [planeRot, planeProj, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg,
    neg_zero, blockD_sq]

lemma xLog_mul_rot : (xLog : Mat n) * planeRot = 0 := by
  rw [xLog, planeRot, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg,
    neg_zero, zero_mul, blockL_mul_D, fromBlocks_zero]

lemma rot_mul_xLog : (planeRot : Mat n) * xLog = 0 := by
  rw [planeRot, xLog, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg,
    neg_zero, mul_zero, neg_neg, blockD_mul_L, fromBlocks_zero]

lemma xLog_comm : Commute (xLog : Mat n) (Real.pi • planeRot) := by
  rw [Commute, SemiconjBy, Matrix.mul_smul, Matrix.smul_mul, xLog_mul_rot, rot_mul_xLog]

lemma j_mul_sNeg : J₀ n * (sNeg : Mat n) = xLog + Real.pi • planeRot := by
  rw [show J₀ n = fromBlocks 0 (-1) 1 0 by rfl, sNeg, xLog, planeRot, fromBlocks_multiply,
    blockA_eq, blockB_eq, fromBlocks_smul, fromBlocks_add]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.one_mul, Matrix.neg_mul,
    Matrix.mul_one, neg_neg, smul_zero, smul_neg]

noncomputable def gRot (θ : ℝ) : Mat n :=
  (1 - planeProj) + Real.cos θ • planeProj + Real.sin θ • planeRot

lemma gRot_zero : gRot (n := n) 0 = 1 := by
  simp [gRot, Real.cos_zero, Real.sin_zero, one_smul, zero_smul, sub_add_cancel]

lemma planeRot_mul_g (θ : ℝ) :
    (planeRot : Mat n) * gRot θ = -Real.sin θ • planeProj + Real.cos θ • planeRot := by
  rw [gRot, Matrix.mul_add, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul,
    Matrix.mul_smul, planeRot_sq, planeRot_mul_proj, smul_neg, sub_self, zero_add, ← neg_smul]
  abel

lemma hasDerivAt_gRot (θ : ℝ) : HasDerivAt (gRot : ℝ → Mat n) (planeRot * gRot θ) θ := by
  have hconst : HasDerivAt (fun _ : ℝ => (1 - planeProj : Mat n)) 0 θ := hasDerivAt_const _ _
  have hg := (hconst.add ((Real.hasDerivAt_cos θ).smul_const planeProj)).add
    ((Real.hasDerivAt_sin θ).smul_const planeRot)
  refine hg.congr_deriv ?_
  rw [planeRot_mul_g, zero_add]

lemma exp_planeRot (θ : ℝ) : exp (θ • (planeRot : Mat n)) = gRot θ := by
  symm
  exact eq_exp_of_ode planeRot gRot gRot_zero hasDerivAt_gRot θ

lemma exp_pi_planeRot : exp (Real.pi • (planeRot : Mat n)) = 1 - (2 : ℝ) • planeProj := by
  rw [exp_planeRot, gRot, Real.cos_pi, Real.sin_pi]
  simp [neg_one_smul, zero_smul, sub_eq_add_neg, two_smul]
  abel

lemma xLog_diag : (xLog : Mat n) = diagonal (Sum.elim diagL fun j : Fin n => -diagL j) := by
  rw [xLog, blockL, diagonal_neg, fromBlocks_diagonal]

lemma exp_xLog : exp (xLog : Mat n) =
    diagonal (Sum.elim (fun j : Fin n => Real.exp (diagL j))
      (fun j : Fin n => Real.exp (-diagL j))) := by
  rw [xLog_diag, Matrix.exp_diagonal]
  congr 1
  ext i
  rw [Pi.coe_exp, Real.exp_eq_exp_ℝ]
  cases i <;> rfl

lemma exp_diagL (j : Fin n) : Real.exp (diagL j) = if j.val = 0 then 2 else 1 := by
  simp only [diagL]
  by_cases h : j.val = 0
  · simp [h, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  · simp [h, Real.exp_zero]

lemma exp_neg_diagL (j : Fin n) : Real.exp (-diagL j) = if j.val = 0 then (1 / 2 : ℝ) else 1 := by
  simp only [diagL]
  by_cases h : j.val = 0
  · simp [h, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div]
  · simp [h, neg_zero, Real.exp_zero]

lemma signProj : (1 : Mat n) - (2 : ℝ) • (planeProj : Mat n) =
    diagonal (Sum.elim (fun j : Fin n => if j.val = 0 then (1 : ℝ) else -1)
      (fun j : Fin n => if j.val = 0 then (1 : ℝ) else -1)) := by
  have hP : (planeProj : Mat n) = diagonal (Sum.elim diagP diagP) := by
    rw [planeProj, blockD, fromBlocks_diagonal]
  rw [hP, ← diagonal_one, ← diagonal_smul, diagonal_sub]
  congr
  ext i
  cases i with
  | inl j =>
    simp only [Sum.elim, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, diagP]
    by_cases h : j.val = 0 <;> simp [h] <;> norm_num
  | inr j =>
    simp only [Sum.elim, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, diagP]
    by_cases h : j.val = 0 <;> simp [h] <;> norm_num

lemma ham_neg_one : hamPath sNeg 1 = Wminus n := by
  rw [hamPath_apply]
  have hone : ((1 : unitInterval) : ℝ) = 1 := rfl
  rw [hone, one_smul, j_mul_sNeg, exp_add_of_commute xLog_comm, exp_xLog, exp_pi_planeRot,
    signProj, diagonal_mul_diagonal, Wminus]
  congr
  ext i
  cases i with
  | inl j =>
    simp only [Sum.elim, exp_diagL]
    by_cases h : j.val = 0 <;> simp [h]
  | inr j =>
    simp only [Sum.elim, exp_neg_diagL]
    by_cases h : j.val = 0 <;> simp [h]

lemma ham_neg_mem_SP : hamPath sNeg ∈ SP n := by
  refine ⟨?_, ?_, ?_⟩
  · intro t
    simpa [hamPath_apply] using CZSig.exp_smul_isSymplectic sNeg sNeg_herm (t : ℝ)
  · simp [hamPath_apply, zero_smul, exp_zero]
  · rw [ham_neg_one]
    have h1 : (1 : Mat n) = diagonal fun _ : Fin n ⊕ Fin n => (1 : ℝ) := diagonal_one.symm
    rw [h1, Wminus, diagonal_sub, det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro i _
    cases i with
    | inl j =>
      by_cases h : j.val = 0 <;> simp [h] <;> norm_num
    | inr j =>
      by_cases h : j.val = 0 <;> simp [h] <;> norm_num

/-! ### Paths in one component of `SP(n)` have the same index -/

lemma mu_of_family {μ : C(unitInterval, Mat n) → ℤ} (hμ : HomotopyAxiom μ)
    (H : C(unitInterval × unitInterval, Mat n))
    (hsym : ∀ s t, IsSymplectic (H (s, t))) (h0 : ∀ s, H (s, 0) = 1)
    (h1 : ∀ s, (1 - H (s, 1)).det ≠ 0) :
    μ (H.curry 1) = μ (H.curry 0) := by
  have hmem : ∀ s, H.curry s ∈ SP n := by
    intro s
    refine ⟨fun t => by simpa [ContinuousMap.curry_apply] using hsym s t,
      by simpa [ContinuousMap.curry_apply] using h0 s,
      by simpa [ContinuousMap.curry_apply] using h1 s⟩
  have hpre : IsPreconnected (Set.range H.curry) := isPreconnected_range H.curry.continuous
  have hsubset : Set.range H.curry ⊆ SP n := by
    rintro _ ⟨s, rfl⟩
    exact hmem s
  have hx : H.curry 0 ∈ Set.range H.curry := ⟨0, rfl⟩
  exact hμ _ (hmem 0) _ ((hpre.subset_connectedComponentIn hx hsubset) ⟨1, rfl⟩)

lemma cz_of_family (H : C(unitInterval × unitInterval, Mat n))
    (hsym : ∀ s t, IsSymplectic (H (s, t))) (h0 : ∀ s, H (s, 0) = 1)
    (h1 : ∀ s, (1 - H (s, 1)).det ≠ 0) :
    czIndex (H.curry 1) = czIndex (H.curry 0) :=
  czIndex_eq_of_family H hsym h0 h1 (H.curry 0) (H.curry 1)
    (fun t => by simp [ContinuousMap.curry_apply])
    (fun t => by simp [ContinuousMap.curry_apply])

def prolongScale (s t : unitInterval) : ℝ := (1 + (s : ℝ)) * (t : ℝ)

def prolongLeft (s t : unitInterval) : unitInterval :=
  ⟨min (prolongScale s t) 1, by
    refine ⟨le_min (mul_nonneg (by linarith [s.2.1]) t.2.1) zero_le_one, min_le_right _ _⟩⟩

def prolongRight (s t : unitInterval) : unitInterval :=
  ⟨max (prolongScale s t - 1) 0, by
    refine ⟨le_max_right _ _, max_le ?_ zero_le_one⟩
    have h2 : prolongScale s t ≤ 2 := by
      simp only [prolongScale]
      nlinarith [s.2.1, s.2.2, t.2.1, t.2.2]
    linarith⟩

lemma continuous_prolongScale :
    Continuous (fun p : unitInterval × unitInterval => prolongScale p.1 p.2) := by
  unfold prolongScale
  fun_prop

lemma continuous_prolongLeft :
    Continuous (fun p : unitInterval × unitInterval => prolongLeft p.1 p.2) :=
  Continuous.subtype_mk (continuous_prolongScale.min continuous_const) _

lemma continuous_prolongRight :
    Continuous (fun p : unitInterval × unitInterval => prolongRight p.1 p.2) :=
  Continuous.subtype_mk ((continuous_prolongScale.sub continuous_const).max continuous_const) _

noncomputable def prolongFam (ψ χ : C(unitInterval, Mat n)) (_h : χ 0 = ψ 1) :
    C(unitInterval × unitInterval, Mat n) where
  toFun p :=
    if prolongScale p.1 p.2 ≤ 1 then ψ (prolongLeft p.1 p.2) else χ (prolongRight p.1 p.2)
  continuous_toFun := by
    refine Continuous.if_le (ψ.continuous.comp continuous_prolongLeft)
      (χ.continuous.comp continuous_prolongRight) continuous_prolongScale continuous_const ?_
    intro p hp
    have hL : prolongLeft p.1 p.2 = 1 := by
      apply Subtype.ext
      simp [prolongLeft, hp, min_self]
    have hR : prolongRight p.1 p.2 = 0 := by
      apply Subtype.ext
      simp [prolongRight, hp]
    simp [hL, hR, _h]

@[simp] lemma prolongFam_apply (ψ χ : C(unitInterval, Mat n)) (h : χ 0 = ψ 1)
    (s t : unitInterval) :
    prolongFam ψ χ h (s, t) =
      if prolongScale s t ≤ 1 then ψ (prolongLeft s t) else χ (prolongRight s t) := rfl

lemma prolong_at_zero (ψ χ : C(unitInterval, Mat n)) (h : χ 0 = ψ 1) (t : unitInterval) :
    prolongFam ψ χ h (0, t) = ψ t := by
  have hs : prolongScale 0 t = (t : ℝ) := by simp [prolongScale]
  rw [prolongFam_apply, if_pos (by simpa [hs] using t.2.2)]
  congr 1
  apply Subtype.ext
  simp [prolongLeft, hs, min_eq_left t.2.2]

lemma prolong_at_one (ψ χ : C(unitInterval, Mat n)) (h : χ 0 = ψ 1) (t : unitInterval) :
    prolongFam ψ χ h (1, t) = CZLoop.pathConcat ψ χ h.symm t := by
  have hone : ((1 : unitInterval) : ℝ) = 1 := rfl
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · have hle : prolongScale 1 t ≤ 1 := by
      simp only [prolongScale, hone]
      linarith
    rw [prolongFam_apply, if_pos hle, CZLoop.pathConcat_apply, if_pos ht]
    congr 1
    apply Subtype.ext
    simp only [prolongLeft, prolongScale, CZLoop.clampDouble, hone]
    norm_num
  · have hgt : ¬ prolongScale 1 t ≤ 1 := by
      simp only [prolongScale, hone]
      linarith
    rw [prolongFam_apply, if_neg hgt, CZLoop.pathConcat_apply, if_neg ht]
    congr 1
    apply Subtype.ext
    simp only [prolongRight, prolongScale, CZLoop.clampSecond, hone]
    norm_num

lemma prolong_symplectic {ψ χ : C(unitInterval, Mat n)} (hψ : ψ ∈ SP n)
    (hχ : IsSpStarExtension ψ χ) (s t : unitInterval) :
    IsSymplectic (prolongFam ψ χ hχ.1 (s, t)) := by
  by_cases hle : prolongScale s t ≤ 1
  · rw [prolongFam_apply, if_pos hle]
    exact hψ.1 _
  · rw [prolongFam_apply, if_neg hle]
    exact (hχ.2.1 _).1

lemma prolong_start {ψ χ : C(unitInterval, Mat n)} (hψ : ψ ∈ SP n) (h : χ 0 = ψ 1)
    (s : unitInterval) : prolongFam ψ χ h (s, 0) = 1 := by
  have hz : prolongScale s 0 = 0 := by simp [prolongScale]
  rw [prolongFam_apply, if_pos (by simp [hz])]
  have hL : prolongLeft s 0 = 0 := by
    apply Subtype.ext
    simp [prolongLeft, hz]
  rw [hL, hψ.2.1]

lemma prolong_end {ψ χ : C(unitInterval, Mat n)} (h : χ 0 = ψ 1) (s : unitInterval) :
    prolongFam ψ χ h (s, 1) = χ s := by
  have hscale : prolongScale s 1 = 1 + (s : ℝ) := by simp [prolongScale]
  by_cases hle : prolongScale s 1 ≤ 1
  · have hs0 : (s : ℝ) = 0 := by rw [hscale] at hle; linarith [s.2.1]
    have hs : s = 0 := Subtype.ext hs0
    rw [prolongFam_apply, if_pos hle, hs]
    have hL : prolongLeft 0 1 = 1 := by
      apply Subtype.ext
      simp only [prolongLeft, prolongScale]
      norm_num
    rw [hL, ← h]
  · rw [prolongFam_apply, if_neg hle]
    congr 1
    apply Subtype.ext
    simp only [prolongRight, hscale, add_sub_cancel_left]
    exact max_eq_left s.2.1

def revPath (β : C(unitInterval, Mat n)) : C(unitInterval, Mat n) :=
  β.comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩

lemma revPath_apply (β : C(unitInterval, Mat n)) (t : unitInterval) :
    revPath β t = β (unitInterval.symm t) := rfl

lemma revPath_zero (β : C(unitInterval, Mat n)) : revPath β 0 = β 1 := by
  simp [revPath_apply, unitInterval.symm_zero]

lemma revPath_one (β : C(unitInterval, Mat n)) : revPath β 1 = β 0 := by
  simp [revPath_apply, unitInterval.symm_one]

lemma model_agree {μ : C(unitInterval, Mat n) → ℤ} (hS : SignatureAxiom μ) {S : Mat n}
    (hSmat : S.IsHermitian) (hdet : S.det ≠ 0)
    (hbound : ∀ i, |hSmat.eigenvalues i| < 2 * Real.pi) :
    μ (hamPath S) = czIndex (hamPath S) := by
  have hμ := hS S hSmat hdet hbound (hamPath S) (fun t => hamPath_apply S t)
  have hcz := czIndex_signature n S hSmat hdet hbound (hamPath S) (fun t => hamPath_apply S t)
  have h := hμ.trans hcz.symm
  rw [← sub_eq_zero, ← mul_sub] at h
  rcases mul_eq_zero.mp h with h2 | h0
  · exact absurd h2 (by decide : (2 : ℤ) ≠ 0)
  · exact sub_eq_zero.mp h0

def cancel1 (t : unitInterval) : unitInterval :=
  ⟨min (4 * (t : ℝ)) 1, by
    refine ⟨le_min (mul_nonneg (by norm_num) t.2.1) zero_le_one, min_le_right _ _⟩⟩

def cancelRaw2 (s t : unitInterval) : ℝ :=
  1 - (1 - (s : ℝ)) * (4 * (t : ℝ) - 1)

def cancel2 (s t : unitInterval) : unitInterval :=
  ⟨min (max (cancelRaw2 s t) 0) 1, by
    refine ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩⟩

def cancelRaw3 (s t : unitInterval) : ℝ :=
  (s : ℝ) + (1 - (s : ℝ)) * (2 * (t : ℝ) - 1)

def cancel3 (s t : unitInterval) : unitInterval :=
  ⟨min (max (cancelRaw3 s t) 0) 1, by
    refine ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩⟩

lemma continuous_cancel1 : Continuous cancel1 := by
  refine Continuous.subtype_mk ?_ _
  fun_prop

lemma continuous_cancelRaw2 :
    Continuous (fun p : unitInterval × unitInterval => cancelRaw2 p.1 p.2) := by
  unfold cancelRaw2
  fun_prop

lemma continuous_cancelRaw3 :
    Continuous (fun p : unitInterval × unitInterval => cancelRaw3 p.1 p.2) := by
  unfold cancelRaw3
  fun_prop

lemma continuous_cancel2 :
    Continuous (fun p : unitInterval × unitInterval => cancel2 p.1 p.2) :=
  Continuous.subtype_mk ((continuous_cancelRaw2.max continuous_const).min continuous_const) _

lemma continuous_cancel3 :
    Continuous (fun p : unitInterval × unitInterval => cancel3 p.1 p.2) :=
  Continuous.subtype_mk ((continuous_cancelRaw3.max continuous_const).min continuous_const) _

lemma cancel1_quarter {t : unitInterval} (ht : (t : ℝ) = 1 / 4) : cancel1 t = 1 := by
  apply Subtype.ext
  simp [cancel1, ht]

lemma cancel2_quarter {s t : unitInterval} (ht : (t : ℝ) = 1 / 4) : cancel2 s t = 1 := by
  apply Subtype.ext
  simp only [cancel2, cancelRaw2, ht]
  norm_num

lemma cancel2_half {s t : unitInterval} (ht : (t : ℝ) = 1 / 2) : (cancel2 s t : ℝ) = s := by
  have hraw : cancelRaw2 s t = s := by
    simp only [cancelRaw2, ht]
    ring
  simp only [cancel2, hraw, max_eq_left s.2.1, min_eq_left s.2.2]

lemma cancel3_half {s t : unitInterval} (ht : (t : ℝ) = 1 / 2) : (cancel3 s t : ℝ) = s := by
  have hraw : cancelRaw3 s t = s := by
    simp only [cancelRaw3, ht]
    ring
  simp only [cancel3, hraw, max_eq_left s.2.1, min_eq_left s.2.2]

lemma cancel3_one (s : unitInterval) : cancel3 s 1 = 1 := by
  apply Subtype.ext
  have hone : ((1 : unitInterval) : ℝ) = 1 := rfl
  simp only [cancel3, cancelRaw3, hone]
  ring_nf
  simp [max_eq_left (zero_le_one : (0 : ℝ) ≤ 1), min_self]

noncomputable def cancelFam (γ β : C(unitInterval, Mat n)) (h : γ 1 = β 1) :
    C(unitInterval × unitInterval, Mat n) where
  toFun p :=
    if (p.2 : ℝ) ≤ 1 / 4 then γ (cancel1 p.2)
    else if (p.2 : ℝ) ≤ 1 / 2 then β (cancel2 p.1 p.2)
    else β (cancel3 p.1 p.2)
  continuous_toFun := by
    refine Continuous.if_le
      (γ.continuous.comp (continuous_cancel1.comp continuous_snd))
      (Continuous.if_le (β.continuous.comp continuous_cancel2)
        (β.continuous.comp continuous_cancel3)
        (continuous_subtype_val.comp continuous_snd) continuous_const ?_)
      (continuous_subtype_val.comp continuous_snd) continuous_const ?_
    · intro p hp
      congr 1
      apply Subtype.ext
      exact (cancel2_half hp).trans (cancel3_half hp).symm
    · intro p hp
      rw [if_pos (show (p.2 : ℝ) ≤ 1 / 2 by linarith [hp])]
      rw [cancel1_quarter hp, cancel2_quarter hp, h]

@[simp] lemma cancelFam_apply (γ β : C(unitInterval, Mat n)) (h : γ 1 = β 1)
    (s t : unitInterval) : cancelFam γ β h (s, t) =
      if (t : ℝ) ≤ 1 / 4 then γ (cancel1 t)
      else if (t : ℝ) ≤ 1 / 2 then β (cancel2 s t) else β (cancel3 s t) := rfl

def reparamF (t : unitInterval) : unitInterval :=
  if (t : ℝ) ≤ 1 / 4 then cancel1 t else 1

lemma continuous_reparamF : Continuous reparamF := by
  refine Continuous.if_le continuous_cancel1 continuous_const continuous_subtype_val
    continuous_const ?_
  intro t ht
  exact cancel1_quarter ht

def reparamMix (s t : unitInterval) : unitInterval :=
  ⟨(1 - (s : ℝ)) * (t : ℝ) + (s : ℝ) * (reparamF t : ℝ),
    CZLoop.convex_bounds t.2.1 t.2.2 (reparamF t).2.1 (reparamF t).2.2 s.2.1 s.2.2⟩

lemma continuous_reparamMix :
    Continuous (fun p : unitInterval × unitInterval => reparamMix p.1 p.2) := by
  refine Continuous.subtype_mk ?_ _
  change Continuous (fun p : unitInterval × unitInterval =>
    (1 - (p.1 : ℝ)) * (p.2 : ℝ) + (p.1 : ℝ) * (reparamF p.2 : ℝ))
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp continuous_snd)).add
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp (continuous_reparamF.comp continuous_snd)))

noncomputable def reparamFam (γ : C(unitInterval, Mat n)) :
    C(unitInterval × unitInterval, Mat n) where
  toFun p := γ (reparamMix p.1 p.2)
  continuous_toFun := γ.continuous.comp continuous_reparamMix

lemma reparamMix_zero (t : unitInterval) : reparamMix 0 t = t := by
  apply Subtype.ext
  simp [reparamMix]

lemma reparamMix_one (t : unitInterval) : reparamMix 1 t = reparamF t := by
  apply Subtype.ext
  simp [reparamMix]

lemma reparamMix_left (s : unitInterval) : reparamMix s 0 = 0 := by
  apply Subtype.ext
  have h0 : reparamF 0 = 0 := by
    rw [reparamF, if_pos (by norm_num : ((0 : unitInterval) : ℝ) ≤ 1 / 4)]
    apply Subtype.ext
    simp [cancel1]
  simp [reparamMix, h0]

lemma reparamMix_right (s : unitInterval) : reparamMix s 1 = 1 := by
  apply Subtype.ext
  have h1 : reparamF 1 = 1 := by
    rw [reparamF, if_neg (by norm_num : ¬ ((1 : unitInterval) : ℝ) ≤ 1 / 4)]
  simp [reparamMix, h1]

lemma cancel1_zero : cancel1 0 = 0 := by
  apply Subtype.ext
  simp [cancel1]

lemma cancel_at_one {γ β : C(unitInterval, Mat n)} (h : γ 1 = β 1) (t : unitInterval) :
    cancelFam γ β h (1, t) = γ (reparamF t) := by
  by_cases ht : (t : ℝ) ≤ 1 / 4
  · rw [cancelFam_apply, if_pos ht, reparamF, if_pos ht]
  · rw [cancelFam_apply, if_neg ht, reparamF, if_neg ht]
    by_cases ht2 : (t : ℝ) ≤ 1 / 2
    · rw [if_pos ht2]
      have hc : cancel2 1 t = 1 := by
        apply Subtype.ext
        have hone : ((1 : unitInterval) : ℝ) = 1 := rfl
        have hraw : cancelRaw2 1 t = 1 := by
          simp only [cancelRaw2, hone]
          ring
        simp [cancel2, hraw]
      rw [hc, ← h]
    · rw [if_neg ht2]
      have hc : cancel3 1 t = 1 := by
        apply Subtype.ext
        have hone : ((1 : unitInterval) : ℝ) = 1 := rfl
        simp only [cancel3, cancelRaw3, hone]
        ring_nf
        simp
      rw [hc, ← h]

lemma reduce_to_model {μ : C(unitInterval, Mat n) → ℤ}
    (hH : HomotopyAxiom μ) (hL : LoopAxiom μ)
    {γ β : C(unitInterval, Mat n)} (hγ : γ ∈ SP n) (hβ : β ∈ SP n)
    (hend : β 1 = γ 1) (hmodel : μ β = czIndex β) :
    μ γ = czIndex γ := by
  have hrev : γ 1 = (revPath β) 0 := by rw [revPath_zero, hend]
  let φ := CZLoop.pathConcat γ (revPath β) hrev
  have hφ : IsSymplecticLoop φ := by
    refine ⟨?_, ?_, ?_⟩
    · intro t
      by_cases ht : (t : ℝ) ≤ 1 / 2
      · rw [CZLoop.pathConcat_apply, if_pos ht]
        exact hγ.1 _
      · rw [CZLoop.pathConcat_apply, if_neg ht, revPath_apply]
        exact hβ.1 _
    · rw [CZLoop.pathConcat_apply,
        if_pos (by norm_num : ((0 : unitInterval) : ℝ) ≤ 1 / 2),
        CZLoop.clampDouble_zero, hγ.2.1]
    · rw [CZLoop.pathConcat_one, revPath_one, hβ.2.1]
  let δ := CZLoop.pathConcat φ β (hφ.2.2.trans hβ.2.1.symm)
  have hsymShuffle := fun s t => CZLoop.shuffle_symplectic φ β hφ hβ s t
  have hstartShuffle := fun s => CZLoop.shuffle_start φ β hφ hβ s
  have hendShuffle : ∀ s, (1 - CZLoop.shuffle φ β (s, 1)).det ≠ 0 := by
    intro s
    rw [CZLoop.shuffle_end φ β hφ hβ s]
    exact hβ.2.2
  have hshuffleμ := mu_of_family hH (CZLoop.shuffle φ β) hsymShuffle hstartShuffle hendShuffle
  have hδmap : (CZLoop.shuffle φ β).curry 0 = δ := by
    ext t
    rw [ContinuousMap.curry_apply, CZLoop.shuffle_zero φ β hφ hβ]
  have hprod : (CZLoop.shuffle φ β).curry 1 = φ * β := by
    ext t
    rw [ContinuousMap.curry_apply, CZLoop.shuffle_one]
  have hμprod : μ (φ * β) = μ δ := by simpa [hδmap, hprod] using hshuffleμ
  have hczprod : czIndex (φ * β) = czIndex δ := by
    simpa [hδmap, hprod] using
      cz_of_family (CZLoop.shuffle φ β) hsymShuffle hstartShuffle hendShuffle
  have hsame : μ (φ * β) = czIndex (φ * β) := by
    rw [hL φ hφ β hβ, czIndex_loop n φ hφ β hβ, hmodel]
  have hδsame : μ δ = czIndex δ := hμprod.symm.trans (hsame.trans hczprod)
  have hcancel0 : ∀ t, cancelFam γ β hend.symm (0, t) = δ t := by
    intro t
    by_cases ht : (t : ℝ) ≤ 1 / 4
    · have ht2 : (t : ℝ) ≤ 1 / 2 := by linarith
      rw [cancelFam_apply, if_pos ht, CZLoop.pathConcat_apply, if_pos ht2]
      have hmid : (CZLoop.clampDouble t : ℝ) ≤ 1 / 2 := by
        simp only [CZLoop.clampDouble]
        have h2 : 2 * (t : ℝ) ≤ 1 := by linarith
        rw [min_eq_left h2]
        linarith
      rw [CZLoop.pathConcat_apply, if_pos hmid]
      congr 1
      apply Subtype.ext
      simp only [cancel1, CZLoop.clampDouble]
      have h2 : 2 * (t : ℝ) ≤ 1 := by linarith
      rw [min_eq_left h2]
      have hmul : 2 * (2 * (t : ℝ)) = 4 * (t : ℝ) := by ring
      rw [hmul]
    · by_cases ht2 : (t : ℝ) ≤ 1 / 2
      · rw [cancelFam_apply, if_neg ht, if_pos ht2, CZLoop.pathConcat_apply, if_pos ht2]
        have hmid : ¬ (CZLoop.clampDouble t : ℝ) ≤ 1 / 2 := by
          simp only [CZLoop.clampDouble]
          have h2 : 2 * (t : ℝ) ≤ 1 := by linarith
          rw [min_eq_left h2]
          linarith
        rw [CZLoop.pathConcat_apply, if_neg hmid, revPath_apply]
        congr 1
        apply Subtype.ext
        have hz : ((0 : unitInterval) : ℝ) = 0 := rfl
        have hraw : cancelRaw2 0 t = 2 - 4 * (t : ℝ) := by
          simp only [cancelRaw2, hz]
          ring
        have h2 : 2 * (t : ℝ) ≤ 1 := by linarith
        have hpos : 0 ≤ 4 * (t : ℝ) - 1 := by linarith
        have hlo : 0 ≤ 2 - 4 * (t : ℝ) := by linarith
        have hhi : 2 - 4 * (t : ℝ) ≤ 1 := by linarith [t.2.2]
        have hlhs : (cancel2 0 t : ℝ) = 2 - 4 * (t : ℝ) := by
          simp only [cancel2, hraw, max_eq_left hlo, min_eq_left hhi]
        have hclamp : (CZLoop.clampSecond (CZLoop.clampDouble t) : ℝ) = 4 * (t : ℝ) - 1 := by
          simp only [CZLoop.clampDouble, CZLoop.clampSecond, min_eq_left h2]
          have hpos' : 0 ≤ 2 * (2 * (t : ℝ)) - 1 := by linarith
          rw [max_eq_left hpos']
          ring
        rw [hlhs, unitInterval.coe_symm_eq, hclamp]
        ring
      · rw [cancelFam_apply, if_neg ht, if_neg ht2, CZLoop.pathConcat_apply, if_neg ht2]
        congr 1
        apply Subtype.ext
        have hz : ((0 : unitInterval) : ℝ) = 0 := rfl
        have hraw : cancelRaw3 0 t = 2 * (t : ℝ) - 1 := by
          simp only [cancelRaw3, hz]
          ring
        have hlo : 0 ≤ 2 * (t : ℝ) - 1 := by linarith
        have hhi : 2 * (t : ℝ) - 1 ≤ 1 := by linarith [t.2.2]
        simp only [cancel3, hraw, CZLoop.clampSecond, max_eq_left hlo, min_eq_left hhi]
  let H := cancelFam γ β hend.symm
  have hsymC : ∀ s t, IsSymplectic (H (s, t)) := by
    intro s t
    by_cases ht : (t : ℝ) ≤ 1 / 4
    · rw [show H (s, t) = cancelFam γ β hend.symm (s, t) from rfl, cancelFam_apply, if_pos ht]
      exact hγ.1 _
    · by_cases ht2 : (t : ℝ) ≤ 1 / 2
      · rw [show H (s, t) = cancelFam γ β hend.symm (s, t) from rfl, cancelFam_apply,
          if_neg ht, if_pos ht2]
        exact hβ.1 _
      · rw [show H (s, t) = cancelFam γ β hend.symm (s, t) from rfl, cancelFam_apply,
          if_neg ht, if_neg ht2]
        exact hβ.1 _
  have h0C : ∀ s, H (s, 0) = 1 := by
    intro s
    rw [show H (s, 0) = cancelFam γ β hend.symm (s, 0) from rfl, cancelFam_apply,
      if_pos (by norm_num : ((0 : unitInterval) : ℝ) ≤ 1 / 4), cancel1_zero, hγ.2.1]
  have h1C : ∀ s, (1 - H (s, 1)).det ≠ 0 := by
    intro s
    rw [show H (s, 1) = cancelFam γ β hend.symm (s, 1) from rfl, cancelFam_apply,
      if_neg (by norm_num : ¬ ((1 : unitInterval) : ℝ) ≤ 1 / 4),
      if_neg (by norm_num : ¬ ((1 : unitInterval) : ℝ) ≤ 1 / 2), cancel3_one]
    exact hβ.2.2
  have hμC := mu_of_family hH H hsymC h0C h1C
  have hczC := cz_of_family H hsymC h0C h1C
  have hmap0 : H.curry 0 = δ := by
    apply ContinuousMap.ext
    intro t
    rw [ContinuousMap.curry_apply, hcancel0]
  have hmap1 : H.curry 1 = (reparamFam γ).curry 1 := by
    apply ContinuousMap.ext
    intro t
    rw [ContinuousMap.curry_apply, ContinuousMap.curry_apply, cancel_at_one hend.symm]
    change γ (reparamF t) = γ (reparamMix 1 t)
    rw [reparamMix_one]
  let R := reparamFam γ
  have hsymR : ∀ s t, IsSymplectic (R (s, t)) := by
    intro s t
    change IsSymplectic (γ (reparamMix s t))
    exact hγ.1 _
  have h0R : ∀ s, R (s, 0) = 1 := by
    intro s
    change γ (reparamMix s 0) = 1
    rw [reparamMix_left, hγ.2.1]
  have h1R : ∀ s, (1 - R (s, 1)).det ≠ 0 := by
    intro s
    change (1 - γ (reparamMix s 1)).det ≠ 0
    rw [reparamMix_right]
    exact hγ.2.2
  have hμR := mu_of_family hH R hsymR h0R h1R
  have hczR := cz_of_family R hsymR h0R h1R
  have hR0 : R.curry 0 = γ := by
    apply ContinuousMap.ext
    intro t
    rw [ContinuousMap.curry_apply]
    change γ (reparamMix 0 t) = γ t
    rw [reparamMix_zero]
  have hchainμ : μ δ = μ γ := by
    have h1 : μ (H.curry 1) = μ (R.curry 1) := by rw [hmap1]
    have hleft : μ (H.curry 1) = μ δ := by rw [hmap0] at hμC; exact hμC
    have hright : μ (R.curry 1) = μ γ := by rw [hR0] at hμR; exact hμR
    exact hleft.symm.trans (h1.trans hright)
  have hchaincz : czIndex δ = czIndex γ := by
    have h1 : czIndex (H.curry 1) = czIndex (R.curry 1) := by rw [hmap1]
    have hleft : czIndex (H.curry 1) = czIndex δ := by rw [hmap0] at hczC; exact hczC
    have hright : czIndex (R.curry 1) = czIndex γ := by rw [hR0] at hczR; exact hczR
    exact hleft.symm.trans (h1.trans hright)
  rw [← hchainμ, ← hchaincz, hδsame]

theorem czIndex_unique {μ : C(unitInterval, Mat n) → ℤ}
    (hH : HomotopyAxiom μ) (hL : LoopAxiom μ) (hS : SignatureAxiom μ)
    {ψ : C(unitInterval, Mat n)} (hψ : ψ ∈ SP n) : μ ψ = czIndex ψ := by
  obtain ⟨k, hk⟩ := (czValue_existsUnique ψ hψ).exists
  obtain ⟨χ, hχ, _⟩ := hk
  have hjoin : χ 0 = ψ 1 := hχ.1
  let γ := CZLoop.pathConcat ψ χ hjoin.symm
  have hγ : γ ∈ SP n := by
    refine ⟨?_, ?_, ?_⟩
    · intro t
      by_cases ht : (t : ℝ) ≤ 1 / 2
      · rw [CZLoop.pathConcat_apply, if_pos ht]
        exact hψ.1 _
      · rw [CZLoop.pathConcat_apply, if_neg ht]
        exact (hχ.2.1 _).1
    · rw [CZLoop.pathConcat_apply,
        if_pos (by norm_num : ((0 : unitInterval) : ℝ) ≤ 1 / 2),
        CZLoop.clampDouble_zero, hψ.2.1]
    · rw [CZLoop.pathConcat_one]
      exact (hχ.2.1 1).2
  have hμγ : μ γ = μ ψ := by
    let H := prolongFam ψ χ hjoin
    have hμ := mu_of_family hH H (prolong_symplectic hψ hχ) (prolong_start hψ hjoin)
      (fun s => by rw [prolong_end]; exact (hχ.2.1 s).2)
    have h0 : H.curry 0 = ψ := by
      apply ContinuousMap.ext
      intro t
      rw [ContinuousMap.curry_apply, prolong_at_zero]
    have h1 : H.curry 1 = γ := by
      apply ContinuousMap.ext
      intro t
      rw [ContinuousMap.curry_apply, prolong_at_one]
    simpa [h0, h1] using hμ
  have hczγ : czIndex γ = czIndex ψ := by
    let H := prolongFam ψ χ hjoin
    have hcz := cz_of_family H (prolong_symplectic hψ hχ) (prolong_start hψ hjoin)
      (fun s => by rw [prolong_end]; exact (hχ.2.1 s).2)
    have h0 : H.curry 0 = ψ := by
      apply ContinuousMap.ext
      intro t
      rw [ContinuousMap.curry_apply, prolong_at_zero]
    have h1 : H.curry 1 = γ := by
      apply ContinuousMap.ext
      intro t
      rw [ContinuousMap.curry_apply, prolong_at_one]
    simpa [h0, h1] using hcz
  rcases hχ.2.2 with hw | hw
  · have hend : hamPath sPlus 1 = γ 1 := by
      rw [ham_plus_one, CZLoop.pathConcat_one]
      exact hw.symm
    have hmodel := model_agree hS sPlus_herm sPlus_det sPlus_bound
    have hred := reduce_to_model hH hL hγ ham_plus_mem_SP hend hmodel
    rw [← hμγ, ← hczγ, hred]
  · have hend : hamPath sNeg 1 = γ 1 := by
      rw [ham_neg_one, CZLoop.pathConcat_one]
      exact hw.symm
    have hmodel := model_agree hS sNeg_herm sNeg_det sNeg_bound
    have hred := reduce_to_model hH hL hγ ham_neg_mem_SP hend hmodel
    rw [← hμγ, ← hczγ, hred]

end

end CZUnique

open ConleyZehnder

theorem solution (n : ℕ) :
    (HomotopyAxiom (czIndex (n := n)) ∧ LoopAxiom (czIndex (n := n)) ∧
      SignatureAxiom (czIndex (n := n))) ∧
    ∀ μ : C(unitInterval, Mat n) → ℤ, HomotopyAxiom μ → LoopAxiom μ → SignatureAxiom μ →
      ∀ ψ ∈ SP n, μ ψ = czIndex ψ :=
  ⟨⟨czIndex_homotopy n, czIndex_loop n, czIndex_signature n⟩,
    fun μ hH hL hS ψ hψ => CZUnique.czIndex_unique hH hL hS hψ⟩
