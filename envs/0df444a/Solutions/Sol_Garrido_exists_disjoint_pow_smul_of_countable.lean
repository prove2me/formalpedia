-- Prove2me | solution 1 for Garrido.exists_disjoint_pow_smul_of_countable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T14:08:01.180736+00:00
-- url     : https://prove2.me/submissions/e6eb0699-527d-4c0e-8d4b-4228416bed1a

import Mathlib
import Definitions.Def_Garrido_BanachTarski
import Definitions.Def_Garrido_Equidecomposability
import Definitions.Def_Garrido_Amenability
import Definitions.Def_Chou_Classes

universe u

namespace Garrido.BT

open scoped ENNReal Pointwise
open Set

/-! ### Reduced words -/

section Words

variable {α : Type*} [DecidableEq α]
set_option linter.unusedSectionVars false

end Words

/-! ### Equidecomposition lemmas (copied from proofs/EQ_Sec1.lean) -/

/-! ### The paradox from an equivariant map to `F₂` -/

/-! ### Amenable groups have no free subgroup of rank two -/

end Garrido.BT


namespace Garrido.BT

open Matrix

end Garrido.BT


namespace Garrido.BT

open Matrix

/-! ### Transfer of equidecompositions from an invariant subtype -/

section Transfer

open Set

variable {G H Y : Type*} [Group G] [MulAction G Y] [Group H]

end Transfer

/-! ### The sphere is uncountable -/

/-! ### Theorem 1.7 (Hausdorff) -/

end Garrido.BT


namespace Garrido.BT

open scoped Pointwise
open Real Matrix

/-! ## Part 2: absorbing a set with disjoint orbit translates -/

/-! ## Part 1: rotations -/

/-- A set of reals any two of whose elements differ by an integer multiple of `c` is countable. -/
theorem countable_of_sub_mem_zmultiples (S : Set ℝ) (c : ℝ)
    (h : ∀ a ∈ S, ∀ b ∈ S, ∃ k : ℤ, a - b = k * c) : S.Countable := by
  rcases S.eq_empty_or_nonempty with hS | ⟨b, hb⟩
  · rw [hS]; exact Set.countable_empty
  · refine (Set.countable_range (fun k : ℤ => b + k * c)).mono ?_
    intro a ha
    obtain ⟨k, hk⟩ := h a ha b hb
    exact ⟨k, by simp only; linarith⟩

/-- Rotation by `θ` about the third coordinate axis. -/
noncomputable def Rz (θ : ℝ) : specialOrthogonalGroup (Fin 3) ℝ :=
  ⟨!![cos θ, -sin θ, 0; sin θ, cos θ, 0; 0, 0, 1], by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [sin_sq_add_cos_sq θ]
    · simp [Matrix.det_fin_three]; nlinarith [sin_sq_add_cos_sq θ]⟩

/-- Rotation by `φ` about the first coordinate axis. -/
noncomputable def Rx (φ : ℝ) : specialOrthogonalGroup (Fin 3) ℝ :=
  ⟨!![1, 0, 0; 0, cos φ, -sin φ; 0, sin φ, cos φ], by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [sin_sq_add_cos_sq φ]
    · simp [Matrix.det_fin_three]; nlinarith [sin_sq_add_cos_sq φ]⟩

theorem Rz_add (a b : ℝ) : Rz (a + b) = Rz a * Rz b := by
  apply Subtype.ext
  change !![cos (a + b), -sin (a + b), 0; sin (a + b), cos (a + b), 0; 0, 0, 1] =
    !![cos a, -sin a, 0; sin a, cos a, 0; 0, 0, 1] * !![cos b, -sin b, 0; sin b, cos b, 0; 0, 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, cos_add, sin_add] <;> ring

theorem Rz_zero : Rz 0 = 1 := by
  apply Subtype.ext
  change !![cos 0, -sin 0, 0; sin 0, cos 0, 0; 0, 0, 1] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem Rz_pow (θ : ℝ) (n : ℕ) : Rz θ ^ n = Rz (n * θ) := by
  induction n with
  | zero => simp [Rz_zero]
  | succ n ih => rw [pow_succ, ih, ← Rz_add]; congr 1; push_cast; ring

theorem Rz_smul_apply (θ : ℝ) (x : Sphere 2) :
    (Rz θ • x).1 0 = cos θ * x.1 0 - sin θ * x.1 1 ∧
    (Rz θ • x).1 1 = sin θ * x.1 0 + cos θ * x.1 1 := by
  change (!![cos θ, -sin θ, 0; sin θ, cos θ, 0; 0, 0, 1] *ᵥ x.1.ofLp) 0 = _ ∧
    (!![cos θ, -sin θ, 0; sin θ, cos θ, 0; 0, 0, 1] *ᵥ x.1.ofLp) 1 = _
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

theorem Rx_smul_apply (φ : ℝ) (x : Sphere 2) :
    (Rx φ • x).1 0 = x.1 0 ∧
    (Rx φ • x).1 1 = cos φ * x.1 1 - sin φ * x.1 2 := by
  change (!![1, 0, 0; 0, cos φ, -sin φ; 0, sin φ, cos φ] *ᵥ x.1.ofLp) 0 = _ ∧
    (!![1, 0, 0; 0, cos φ, -sin φ; 0, sin φ, cos φ] *ᵥ x.1.ofLp) 1 = _
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- A point off the third axis fixed by `Rz t` forces `cos t = 1`. -/
theorem cos_eq_one_of_Rz_smul_eq (t : ℝ) (p : Sphere 2) (hp : ¬(p.1 0 = 0 ∧ p.1 1 = 0))
    (h : Rz t • p = p) : cos t = 1 := by
  obtain ⟨h0, h1⟩ := Rz_smul_apply t p
  rw [h] at h0 h1
  have key : (cos t - 1) * (p.1 0 ^ 2 + p.1 1 ^ 2) = 0 := by
    linear_combination (-(p.1 0)) * h0 - p.1 1 * h1
  have hpos : p.1 0 ^ 2 + p.1 1 ^ 2 ≠ 0 := by
    intro h2
    exact hp ⟨by nlinarith [sq_nonneg (p.1 0), sq_nonneg (p.1 1)],
      by nlinarith [sq_nonneg (p.1 0), sq_nonneg (p.1 1)]⟩
  have := (mul_eq_zero.1 key).resolve_right hpos
  linarith

/-- For `p` off the axis, `{θ | Rz θ ^ n • p = q}` is countable. -/
theorem countable_Rz_pow (p q : Sphere 2) (hp : ¬(p.1 0 = 0 ∧ p.1 1 = 0)) (n : ℕ) (hn : 0 < n) :
    {θ : ℝ | Rz θ ^ n • p = q}.Countable := by
  apply countable_of_sub_mem_zmultiples _ (2 * π / n)
  intro a ha b hb
  simp only [Set.mem_ofPred_eq, Rz_pow] at ha hb
  have hfix : Rz (n * a - n * b) • p = p := by
    have : Rz (n * a - n * b) = Rz (-(n * b)) * Rz (n * a) := by rw [← Rz_add]; ring_nf
    rw [this, mul_smul, ha, ← hb, ← mul_smul, ← Rz_add]
    simp [Rz_zero]
  obtain ⟨k, hk⟩ := (cos_eq_one_iff _).1 (cos_eq_one_of_Rz_smul_eq _ p hp hfix)
  refine ⟨k, ?_⟩
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  linarith

/-- For `x` on the sphere, the set of `φ` for which `Rx φ • x` lies on the third axis is
countable. -/
theorem countable_Rx_axis (x : Sphere 2) :
    {φ : ℝ | (Rx φ • x).1 0 = 0 ∧ (Rx φ • x).1 1 = 0}.Countable := by
  apply countable_of_sub_mem_zmultiples _ π
  intro a ha b hb
  simp only [Set.mem_ofPred_eq, Rx_smul_apply] at ha hb
  obtain ⟨hx0, ha1⟩ := ha
  obtain ⟨-, hb1⟩ := hb
  have hnorm : x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2 = 1 := by
    have h1 : ‖x.1‖ = 1 := mem_sphere_zero_iff_norm.1 x.2
    have := EuclideanSpace.real_norm_sq_eq x.1
    rw [h1, Fin.sum_univ_three] at this
    linarith
  have e1 : sin (a - b) * x.1 1 = 0 := by
    rw [sin_sub]; linear_combination (-(sin b)) * ha1 + sin a * hb1
  have e2 : sin (a - b) * x.1 2 = 0 := by
    rw [sin_sub]; linear_combination (-(cos b)) * ha1 + cos a * hb1
  have hs : sin (a - b) = 0 := by
    have : sin (a - b) ^ 2 * (x.1 1 ^ 2 + x.1 2 ^ 2) = 0 := by
      linear_combination (sin (a - b) * x.1 1) * e1 + (sin (a - b) * x.1 2) * e2
    rw [hx0] at hnorm
    have h' : x.1 1 ^ 2 + x.1 2 ^ 2 = 1 := by linarith
    rw [h', mul_one] at this
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  obtain ⟨k, hk⟩ := (sin_eq_zero_iff).1 hs
  exact ⟨k, by linarith⟩

theorem exists_real_not_mem_of_countable {S : Set ℝ} (hS : S.Countable) : ∃ θ : ℝ, θ ∉ S := by
  by_contra h
  push Not at h
  exact Cardinal.not_countable_real (hS.mono fun x _ => h x)

theorem exists_disjoint_pow_smul_of_countable' (D : Set (Sphere 2)) (hD : D.Countable) :
    ∃ ρ : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ n : ℕ, 0 < n → Disjoint ((ρ ^ n) • D) D := by
  -- Step 1: rotate `D` off the third axis.
  obtain ⟨φ, hφ⟩ := exists_real_not_mem_of_countable
    (hD.biUnion fun x _ => countable_Rx_axis x)
  set g := Rx φ
  set D' : Set (Sphere 2) := g • D with hD'
  have hD'c : D'.Countable := hD.image _
  have hoff : ∀ p ∈ D', ¬(p.1 0 = 0 ∧ p.1 1 = 0) := by
    rintro _ ⟨x, hx, rfl⟩ h
    exact hφ (Set.mem_biUnion hx h)
  -- Step 2: choose the angle.
  have hbad : (⋃ p ∈ D', ⋃ q ∈ D', ⋃ n : ℕ, ⋃ (_ : 0 < n), {θ : ℝ | Rz θ ^ n • p = q}).Countable :=
    hD'c.biUnion fun p hp => hD'c.biUnion fun q _ => Set.countable_iUnion fun n =>
      Set.countable_iUnion fun hn => countable_Rz_pow p q (hoff p hp) n hn
  obtain ⟨θ, hθ⟩ := exists_real_not_mem_of_countable hbad
  have hdisj : ∀ n : ℕ, 0 < n → Disjoint ((Rz θ ^ n) • D') D' := by
    intro n hn
    rw [Set.disjoint_left]
    rintro _ ⟨p, hp, rfl⟩ hq
    exact hθ (Set.mem_biUnion hp (Set.mem_biUnion hq
      (Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨hn, rfl⟩⟩)))
  -- Step 3: conjugate back.
  refine ⟨g⁻¹ * Rz θ * g, fun n hn => ?_⟩
  have hpow : (g⁻¹ * Rz θ * g) ^ n = g⁻¹ * Rz θ ^ n * g := by
    have := map_pow (MulAut.conj g⁻¹) (Rz θ) n
    simpa [MulAut.conj_apply] using this.symm
  rw [hpow, ← Set.disjoint_smul_set (a := g), ← mul_smul]
  have hg : g * (g⁻¹ * Rz θ ^ n * g) = Rz θ ^ n * g := by group
  rw [hg, mul_smul]
  exact hdisj n hn

end Garrido.BT


namespace Garrido.BT

open scoped Pointwise
open Set

end Garrido.BT

namespace Garrido.BT

open Matrix

end Garrido.BT

namespace Garrido.BT

open Matrix Set
open scoped ENNReal Pointwise

end Garrido.BT


/-! Garrido, Corollary 1.10 (Banach–Tarski for balls and for ℝ³) and the p. 1 consequence. -/

namespace Garrido.BT
open scoped ENNReal Pointwise
open Set Matrix

/-! ## The radial projection -/

/-! ## Absorbing the centre -/

/-! ## The targets -/

end Garrido.BT


/-! ## Composition: every milestone, with no hypotheses -/

namespace Garrido.BT.Final

open Garrido
open scoped ENNReal Pointwise

theorem exists_disjoint_pow_smul_of_countable (D : Set (Sphere 2)) (hD : D.Countable) :
    ∃ ρ : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ n : ℕ, 0 < n → Disjoint ((ρ ^ n) • D) D :=
  Garrido.BT.exists_disjoint_pow_smul_of_countable' D hD

end Garrido.BT.Final

open Garrido
open scoped ENNReal Pointwise

theorem solution (D : Set (Sphere 2)) (hD : D.Countable) :
    ∃ ρ : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ n : ℕ, 0 < n → Disjoint ((ρ ^ n) • D) D :=
  Garrido.BT.Final.exists_disjoint_pow_smul_of_countable D hD
