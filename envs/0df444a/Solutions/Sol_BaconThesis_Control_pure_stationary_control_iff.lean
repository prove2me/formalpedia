-- Prove2me | solution 1 for BaconThesis.Control.pure_stationary_control_iff
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T23:06:54.2156+00:00
-- url     : https://prove2.me/submissions/2602d844-c743-4773-9cda-ed50e35e2cc5

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_BaconThesis_Control_IsFixedBasis
import Definitions.Def_BaconThesis_Control_evol
import Definitions.Def_BaconThesis_Control_coeffOp
import Definitions.Def_BaconThesis_Control_HA
import Definitions.Def_BaconThesis_Control_StationaryControlMixed
import Definitions.Def_BaconThesis_Control_StationaryControlPure

open scoped Matrix Kronecker ComplexOrder

set_option linter.unusedSectionVars false

namespace BaconThesis.Control.SolMpure

open BaconThesis.Control

section calculus

variable {T : Type} [Fintype T] [DecidableEq T]

/-- The generator `X ↦ -i [H, X]` of the evolution. -/
def gen (H X : Matrix T T ℂ) : Matrix T T ℂ := (-Complex.I) • (H * X - X * H)

private lemma evol_eq (H : Matrix T T ℂ) (t : ℝ) :
    evol H t = NormedSpace.exp (t • ((-Complex.I) • H)) := by
  rw [evol]
  congr 1
  rw [← Complex.coe_smul, smul_smul]
  congr 1
  ring

private lemma evol_conjTranspose (H : Matrix T T ℂ) (hH : H.IsHermitian) (t : ℝ) :
    (evol H t)ᴴ = NormedSpace.exp (t • (Complex.I • H)) := by
  have hs : star (-(Complex.I * (t : ℂ))) = (t : ℂ) * Complex.I := by simp [mul_comm]
  rw [evol, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hH.eq, hs, ← Complex.coe_smul,
    smul_smul]

private lemma evol_zero (H : Matrix T T ℂ) : evol H 0 = 1 := by simp [evol]

private lemma evol_mul_conjTranspose (H : Matrix T T ℂ) (hH : H.IsHermitian) (t : ℝ) :
    evol H t * (evol H t)ᴴ = 1 := by
  rw [evol_conjTranspose H hH, evol_eq, ← Matrix.exp_add_of_commute]
  · rw [← smul_add, ← add_smul]
    simp
  · exact ((Commute.refl H).smul_left _ |>.smul_right _).smul_left _ |>.smul_right _

private lemma conjTranspose_mul_evol (H : Matrix T T ℂ) (hH : H.IsHermitian) (t : ℝ) :
    (evol H t)ᴴ * evol H t = 1 := by
  rw [evol_conjTranspose H hH, evol_eq, ← Matrix.exp_add_of_commute]
  · rw [← smul_add, ← add_smul]
    simp
  · exact ((Commute.refl H).smul_left _ |>.smul_right _).smul_left _ |>.smul_right _

open scoped Matrix.Norms.Operator in
private lemma hasDerivAt_evol (H : Matrix T T ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => evol H t) (((-Complex.I) • H) * evol H t) t := by
  simp_rw [evol_eq]
  exact hasDerivAt_exp_smul_const' ((-Complex.I) • H) t

open scoped Matrix.Norms.Operator in
private lemma hasDerivAt_evol_conjTranspose (H : Matrix T T ℂ) (hH : H.IsHermitian) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (evol H t)ᴴ) ((evol H t)ᴴ * (Complex.I • H)) t := by
  simp_rw [evol_conjTranspose H hH]
  exact hasDerivAt_exp_smul_const (Complex.I • H) t

open scoped Matrix.Norms.Operator in
private lemma hasDerivAt_conj (H R : Matrix T T ℂ) (hH : H.IsHermitian) (t : ℝ) :
    HasDerivAt (fun t : ℝ => evol H t * R * (evol H t)ᴴ)
      (gen H (evol H t * R * (evol H t)ᴴ)) t := by
  refine (((hasDerivAt_evol H t).mul_const R).mul
    (hasDerivAt_evol_conjTranspose H hH t)).congr_deriv ?_
  change (-Complex.I • H) * evol H t * R * (evol H t)ᴴ +
      evol H t * R * ((evol H t)ᴴ * (Complex.I • H)) =
    -Complex.I • (H * (evol H t * R * (evol H t)ᴴ) - evol H t * R * (evol H t)ᴴ * H)
  generalize evol H t = U
  generalize Uᴴ = V
  simp only [smul_mul_assoc, mul_smul_comm, smul_sub, mul_assoc]
  module

end calculus

section spanning

variable {n : Type} [Fintype n] [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V]

private lemma linear_eq_zero_of_single (L : Matrix n n ℂ →ₗ[ℂ] V)
    (h : ∀ i j, L (Matrix.single i j 1) = 0) (X : Matrix n n ℂ) : L X = 0 := by
  rw [Matrix.matrix_eq_sum_single X, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  have : Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this, map_smul, h, smul_zero]

private lemma exists_normalize (w : n → ℂ) (hw : w ≠ 0) :
    ∃ a : ℂ, a ≠ 0 ∧ star (a • w) ⬝ᵥ (a • w) = 1 := by
  have hx : star w ⬝ᵥ w ≠ 0 := mt dotProduct_star_self_eq_zero.mp hw
  have hnn : 0 ≤ star w ⬝ᵥ w := dotProduct_star_self_nonneg w
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hnn
  set r : ℝ := (star w ⬝ᵥ w).re with hr
  have hxr : star w ⬝ᵥ w = (r : ℂ) := Complex.ext rfl (by simpa using him.symm)
  have hrpos : 0 < r := lt_of_le_of_ne hre fun h => hx (by rw [hxr, ← h]; simp)
  have hs : (Real.sqrt r : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hrpos).ne'
  refine ⟨(Real.sqrt r : ℂ)⁻¹, inv_ne_zero hs, ?_⟩
  rw [star_smul, smul_dotProduct, dotProduct_smul, hxr, smul_eq_mul, smul_eq_mul]
  have h2 : (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = (r : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hrpos.le
  have hstar : star ((Real.sqrt r : ℂ)⁻¹) = (Real.sqrt r : ℂ)⁻¹ := by simp
  rw [hstar, ← h2]
  field_simp

/-- A linear functional that vanishes on every density operator is zero. -/
private lemma functional_eq_zero_of_density (L : Matrix n n ℂ →ₗ[ℂ] ℂ)
    (h : ∀ ρ, WildeQIT.IsDensityOperator ρ → L ρ = 0) (X : Matrix n n ℂ) : L X = 0 := by
  have hq : ∀ v : n → ℂ, L (Matrix.vecMulVec v (star v)) = 0 := by
    intro v
    by_cases hv : v = 0
    · subst hv
      have : Matrix.vecMulVec (0 : n → ℂ) (star (0 : n → ℂ)) = 0 := by ext; simp [Matrix.vecMulVec_apply]
      rw [this, map_zero]
    obtain ⟨a, ha, hav⟩ := exists_normalize v hv
    have hρ : WildeQIT.IsDensityOperator (Matrix.vecMulVec (a • v) (star (a • v))) :=
      ⟨Matrix.posSemidef_vecMulVec_self_star _, by
        rw [Matrix.trace_vecMulVec, dotProduct_comm]; exact hav⟩
    have h1 := h _ hρ
    rw [star_smul, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, map_smul, map_smul] at h1
    exact (smul_eq_zero.mp ((smul_eq_zero.mp h1).resolve_left ha)).resolve_left
      (star_ne_zero.mpr ha)
  have hB : ∀ u v : n → ℂ, L (Matrix.vecMulVec u (star v)) = 0 := by
    intro u v
    have h1 := hq (u + v)
    have h2 := hq (u + Complex.I • v)
    simp only [star_add, star_smul, Matrix.add_vecMulVec, Matrix.vecMulVec_add,
      Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, map_add, map_smul, hq u, hq v,
      Complex.star_def, Complex.conj_I] at h1 h2
    simp only [smul_eq_mul] at h1 h2
    linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2 : ℂ) * h2 +
      ((L (Matrix.vecMulVec u (star v)) - L (Matrix.vecMulVec v (star u))) / 2) * Complex.I_sq
  refine linear_eq_zero_of_single L (fun i j => ?_) X
  have := hB (Pi.single i 1) (Pi.single j 1)
  rwa [Matrix.single_eq_single_vecMulVec_single, show (Pi.single j (1 : ℂ) : n → ℂ) =
    star (Pi.single j (1 : ℂ) : n → ℂ) from by ext k; simp [Pi.single_apply, apply_ite]]

/-- A matrix-valued linear map that vanishes on every density operator is zero. -/
private lemma linear_eq_zero_of_density {m : Type} (L : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (h : ∀ ρ, WildeQIT.IsDensityOperator ρ → L ρ = 0) (X : Matrix n n ℂ) : L X = 0 := by
  ext i j
  exact functional_eq_zero_of_density ((Matrix.entryLinearMap ℂ ℂ i j).comp L)
    (fun ρ hρ => by simp [h ρ hρ]) X

end spanning

section basis

variable {s a κ : Type} [Fintype s] [DecidableEq s] [Fintype a] [DecidableEq a] [Fintype κ]
  [DecidableEq κ]

/-- The partial trace over the system as a linear map. -/
private def ptl : Matrix (s × a) (s × a) ℂ →ₗ[ℂ] Matrix a a ℂ where
  toFun := WildeQIT.partialTraceLeft
  map_add' X Y := by ext; simp [WildeQIT.partialTraceLeft, Finset.sum_add_distrib]
  map_smul' c X := by ext; simp [WildeQIT.partialTraceLeft, Finset.mul_sum]

private lemma ptl_kronecker (A : Matrix s s ℂ) (X : Matrix a a ℂ) :
    ptl (A ⊗ₖ X) = A.trace • X := by
  ext k l
  simp [ptl, WildeQIT.partialTraceLeft, Matrix.trace, Finset.sum_mul]

private lemma sum_kron (G : κ → Matrix s s ℂ) (X : Matrix a a ℂ) :
    ∑ α, G α ⊗ₖ X = (∑ α, G α) ⊗ₖ X := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [Matrix.sum_apply, Finset.sum_mul]

/-- Coefficient extraction against a trace-orthonormal Hermitian family. -/
private lemma coeff_sum (F : κ → Matrix s s ℂ) (i0 : κ) (hF : IsFixedBasis F i0)
    (C : κ → Matrix a a ℂ) (β : κ) :
    ptl ((F β ⊗ₖ (1 : Matrix a a ℂ)) * ∑ α, F α ⊗ₖ C α) = C β := by
  obtain ⟨hherm, -, -, horth, -⟩ := hF
  rw [Finset.mul_sum, map_sum]
  simp only [← Matrix.mul_kronecker_mul, Matrix.one_mul, ptl_kronecker]
  have : ∀ α, (F β * F α).trace = if β = α then 1 else 0 := by
    intro α
    have := horth β α
    rwa [(hherm β).eq] at this
  simp [this]

private lemma expand_single (F : κ → Matrix s s ℂ) (i0 : κ) (hF : IsFixedBasis F i0)
    (A : Matrix s s ℂ) : A = ∑ α, (F α * A).trace • F α := by
  obtain ⟨hherm, -, -, horth, hspan⟩ := hF
  have hA : A ∈ Submodule.span ℂ (Set.range F) := by rw [hspan]; trivial
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hA
  have ht : ∀ α β, (F α * F β).trace = if α = β then 1 else 0 := by
    intro α β
    have := horth α β
    rwa [(hherm α).eq] at this
  have hcoef : ∀ α, (F α * A).trace = g α := by
    intro α
    rw [← hg, Finset.mul_sum, Matrix.trace_sum]
    simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, ht]
    simp
  simp only [hcoef]
  exact hg.symm

/-- The fixed-basis expansion `H = Σ_α F_α ⊗ A_α`. -/
private lemma expansion (F : κ → Matrix s s ℂ) (i0 : κ) (hF : IsFixedBasis F i0)
    (H : Matrix (s × a) (s × a) ℂ) : H = ∑ α, F α ⊗ₖ coeffOp H F α := by
  let L : Matrix (s × a) (s × a) ℂ →ₗ[ℂ] Matrix (s × a) (s × a) ℂ :=
    { toFun := fun H => H - ∑ α, F α ⊗ₖ ptl ((F α ⊗ₖ (1 : Matrix a a ℂ)) * H)
      map_add' := fun X Y => by
        simp only [Matrix.mul_add, map_add, Matrix.kronecker_add, Finset.sum_add_distrib]
        abel
      map_smul' := fun c X => by
        simp only [Matrix.mul_smul, map_smul, Matrix.kronecker_smul, ← Finset.smul_sum,
          RingHom.id_apply, smul_sub] }
  have hL : L H = 0 := by
    refine linear_eq_zero_of_single L (fun p q => ?_) H
    obtain ⟨i, k⟩ := p
    obtain ⟨j, l⟩ := q
    change Matrix.single (i, k) (j, l) (1 : ℂ) - ∑ α, F α ⊗ₖ
      ptl ((F α ⊗ₖ (1 : Matrix a a ℂ)) * Matrix.single (i, k) (j, l) 1) = 0
    have h1 : Matrix.single (i, k) (j, l) (1 : ℂ) =
        Matrix.single i j (1 : ℂ) ⊗ₖ Matrix.single k l (1 : ℂ) := by
      rw [Matrix.single_kronecker_single, mul_one]
    rw [h1]
    simp only [← Matrix.mul_kronecker_mul, Matrix.one_mul, ptl_kronecker, Matrix.kronecker_smul,
      ← Matrix.smul_kronecker]
    rw [sum_kron, ← expand_single F i0 hF, sub_self]
  have := sub_eq_zero.mp hL
  exact this

private lemma sub_kron (A B : Matrix s s ℂ) (X : Matrix a a ℂ) :
    (A - B) ⊗ₖ X = A ⊗ₖ X - B ⊗ₖ X := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [sub_mul]

private lemma kron_sub (A : Matrix s s ℂ) (X Y : Matrix a a ℂ) :
    A ⊗ₖ (X - Y) = A ⊗ₖ X - A ⊗ₖ Y := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [mul_sub]

/-- The `(k, l)` apparatus slice of an operator on system and apparatus. -/
private def slice (k l : a) : Matrix (s × a) (s × a) ℂ →ₗ[ℂ] Matrix s s ℂ where
  toFun Z := Matrix.of fun i j => Z (i, k) (j, l)
  map_add' X Y := by ext; simp
  map_smul' c X := by ext; simp

private lemma slice_kronecker (k l : a) (B : Matrix s s ℂ) (D : Matrix a a ℂ) :
    slice k l (B ⊗ₖ D) = D k l • B := by
  ext i j
  simp [slice, mul_comm]

/-- `Z ↦ Z ⊗ ρ` as a real-linear map. -/
private def kronR (ρa : Matrix a a ℂ) : Matrix s s ℂ →ₗ[ℝ] Matrix (s × a) (s × a) ℂ where
  toFun Z := Z ⊗ₖ ρa
  map_add' _ _ := Matrix.add_kronecker _ _ _
  map_smul' r X := Matrix.smul_kronecker r X ρa

open scoped Matrix.Norms.Operator in
private lemma hasDerivAt_kron (Ha X : Matrix s s ℂ) (hHa : Ha.IsHermitian) (ρa : Matrix a a ℂ)
    (t : ℝ) :
    HasDerivAt (fun t : ℝ => (evol Ha t * X * (evol Ha t)ᴴ) ⊗ₖ ρa)
      ((gen Ha (evol Ha t * X * (evol Ha t)ᴴ)) ⊗ₖ ρa) t :=
  ((LinearMap.toContinuousLinearMap (kronR (s := s) ρa)).hasFDerivAt).comp_hasDerivAt t
    (hasDerivAt_conj Ha X hHa t)

private lemma gen_kron (Ha Y : Matrix s s ℂ) (ρa : Matrix a a ℂ) :
    (gen Ha Y) ⊗ₖ ρa = (-Complex.I) • ((Ha * Y) ⊗ₖ ρa - (Y * Ha) ⊗ₖ ρa) := by
  rw [gen, Matrix.smul_kronecker, sub_kron]

open scoped Matrix.Norms.Operator in
/-- If `ad_H (X ⊗ ρ) = (ad_{H_a} X) ⊗ ρ` for all `X`, the evolutions agree on `X ⊗ ρ`. -/
private lemma conj_eq_of_comm (H : Matrix (s × a) (s × a) ℂ) (hH : H.IsHermitian)
    (Ha : Matrix s s ℂ) (hHa : Ha.IsHermitian) (ρa : Matrix a a ℂ)
    (key : ∀ X : Matrix s s ℂ,
      H * (X ⊗ₖ ρa) - (X ⊗ₖ ρa) * H = (Ha * X) ⊗ₖ ρa - (X * Ha) ⊗ₖ ρa)
    (X : Matrix s s ℂ) (t : ℝ) :
    evol H t * (X ⊗ₖ ρa) * (evol H t)ᴴ = (evol Ha t * X * (evol Ha t)ᴴ) ⊗ₖ ρa := by
  set Φ : ℝ → Matrix (s × a) (s × a) ℂ := fun t =>
    (evol H t)ᴴ * ((evol Ha t * X * (evol Ha t)ᴴ) ⊗ₖ ρa) * evol H t with hΦ
  have hder : ∀ t, HasDerivAt Φ 0 t := by
    intro t
    have hm := hasDerivAt_kron Ha X hHa ρa t
    rw [gen_kron, ← key] at hm
    refine (((hasDerivAt_evol_conjTranspose H hH t).mul hm).mul
      (hasDerivAt_evol H t)).congr_deriv ?_
    change ((evol H t)ᴴ * (Complex.I • H) * ((evol Ha t * X * (evol Ha t)ᴴ) ⊗ₖ ρa) +
        (evol H t)ᴴ * (-Complex.I • (H * ((evol Ha t * X * (evol Ha t)ᴴ) ⊗ₖ ρa) -
          ((evol Ha t * X * (evol Ha t)ᴴ) ⊗ₖ ρa) * H))) * evol H t +
      (evol H t)ᴴ * ((evol Ha t * X * (evol Ha t)ᴴ) ⊗ₖ ρa) * ((-Complex.I • H) * evol H t) = 0
    generalize (evol Ha t * X * (evol Ha t)ᴴ) ⊗ₖ ρa = m
    generalize evol H t = U
    generalize Uᴴ = V
    simp only [smul_mul_assoc, mul_smul_comm, mul_sub, sub_mul, smul_sub, mul_assoc, add_mul]
    module
  have hconst : Φ t = Φ 0 :=
    is_const_of_deriv_eq_zero (fun t => (hder t).differentiableAt) (fun t => (hder t).deriv) t 0
  have h0 : Φ 0 = X ⊗ₖ ρa := by simp [hΦ, evol_zero]
  rw [h0] at hconst
  rw [← hconst, hΦ]
  simp only [← Matrix.mul_assoc]
  rw [evol_mul_conjTranspose H hH, Matrix.one_mul, Matrix.mul_assoc, evol_mul_conjTranspose H hH,
    Matrix.mul_one]

open scoped Matrix.Norms.Operator in
/-- Differentiating the control condition at `t = 0`. -/
private lemma comm_of_conj_eq (H : Matrix (s × a) (s × a) ℂ) (hH : H.IsHermitian)
    (Ha : Matrix s s ℂ) (hHa : Ha.IsHermitian) (ρ : Matrix s s ℂ) (ρa : Matrix a a ℂ)
    (h : ∀ t : ℝ,
      evol H t * (ρ ⊗ₖ ρa) * (evol H t)ᴴ = (evol Ha t * ρ * (evol Ha t)ᴴ) ⊗ₖ ρa) :
    H * (ρ ⊗ₖ ρa) - (ρ ⊗ₖ ρa) * H = (Ha * ρ) ⊗ₖ ρa - (ρ * Ha) ⊗ₖ ρa := by
  have h1 := hasDerivAt_conj H (ρ ⊗ₖ ρa) hH 0
  have h2 := hasDerivAt_kron Ha ρ hHa ρa 0
  rw [← show (fun t : ℝ => evol H t * (ρ ⊗ₖ ρa) * (evol H t)ᴴ) =
    fun t : ℝ => (evol Ha t * ρ * (evol Ha t)ᴴ) ⊗ₖ ρa from funext h] at h2
  have e := h1.unique h2
  rw [gen_kron] at e
  simp only [evol_zero, Matrix.one_mul, Matrix.mul_one, Matrix.conjTranspose_one, gen] at e
  exact smul_right_injective _ (neg_ne_zero.mpr Complex.I_ne_zero) e

end basis


section pure

variable {s a κ : Type} [Fintype s] [DecidableEq s] [Fintype a] [DecidableEq a] [Fintype κ]
  [DecidableEq κ]

lemma star_dot_mulVec (A : Matrix a a ℂ) (u v : a → ℂ) :
    star (star u ⬝ᵥ A *ᵥ v) = star v ⬝ᵥ Aᴴ *ᵥ u := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.star_dotProduct_star, Matrix.star_vecMul, star_star]

/-- An eigenvector of a Hermitian matrix has a real eigenvalue, and its projector commutes. -/
lemma eig_real (M : Matrix a a ℂ) (hM : Mᴴ = M) (v : a → ℂ) (hv : star v ⬝ᵥ v = 1) (c : ℂ)
    (h : M *ᵥ v = c • v) : star c = c ∧
      M * Matrix.vecMulVec v (star v) = c • Matrix.vecMulVec v (star v) ∧
      Matrix.vecMulVec v (star v) * M = c • Matrix.vecMulVec v (star v) := by
  have hc : star v ⬝ᵥ M *ᵥ v = c := by rw [h, dotProduct_smul, hv, smul_eq_mul, mul_one]
  have hr : star c = c := by
    conv_lhs => rw [← hc, star_dot_mulVec, hM]
    exact hc
  refine ⟨hr, ?_, ?_⟩
  · rw [Matrix.mul_vecMulVec, h, Matrix.smul_vecMulVec]
  · have : star v ᵥ* M = c • star v := by
      conv_lhs => rw [← hM, ← Matrix.star_mulVec, h, star_smul, hr]
    rw [Matrix.vecMulVec_mul, this, Matrix.vecMulVec_smul]

/-- Sufficiency of the eigenvector conditions (3.4) for pure state stationary control. -/
lemma suff (H : Matrix (s × a) (s × a) ℂ) (hH : H.IsHermitian)
    (F : κ → Matrix s s ℂ) (i0 : κ) (hF : IsFixedBasis F i0)
    (v : a → ℂ) (hv : star v ⬝ᵥ v = 1) (c : κ → ℂ) (lam : ℂ)
    (hc : ∀ α, α ≠ i0 → coeffOp H F α *ᵥ v = c α • v) (hl : HA H *ᵥ v = lam • v)
    (Ha : Matrix s s ℂ)
    (hHa : Ha = lam • (1 : Matrix s s ℂ) + ∑ α ∈ Finset.univ.erase i0, c α • F α) :
    Ha.IsHermitian ∧
      ∀ t : ℝ, ∀ X : Matrix s s ℂ,
        evol H t * (X ⊗ₖ Matrix.vecMulVec v (star v)) * (evol H t)ᴴ =
          (evol Ha t * X * (evol Ha t)ᴴ) ⊗ₖ Matrix.vecMulVec v (star v) := by
  classical
  have hexp := expansion F i0 hF H
  obtain ⟨A, hA⟩ : ∃ A : κ → Matrix a a ℂ, A = fun α => coeffOp H F α := ⟨_, rfl⟩
  have hAα : ∀ α, coeffOp H F α = A α := fun α => by rw [hA]
  simp only [hAα] at hexp hc
  have hF' := hF
  obtain ⟨hherm, hF0, htr0, horth, hspan⟩ := hF
  have hAherm : ∀ α, (A α)ᴴ = A α := by
    intro α
    have h1 : H = ∑ β, F β ⊗ₖ (A β)ᴴ := by
      have := congrArg Matrix.conjTranspose hexp
      rw [hH.eq, Matrix.conjTranspose_sum] at this
      simpa [Matrix.conjTranspose_kronecker, (hherm _).eq] using this
    have h2 := coeff_sum F i0 hF' (fun β => (A β)ᴴ) α
    rw [← h1] at h2
    rw [← h2, ← hAα]
    rfl
  have hne : Nonempty s := by
    rcases isEmpty_or_nonempty s with h | h
    · have := horth i0 i0
      simp [Matrix.trace] at this
    · exact h
  obtain ⟨r, hr⟩ : ∃ r : ℂ, r = (Real.sqrt (Fintype.card s) : ℂ) := ⟨_, rfl⟩
  have hr2 : r * r = (Fintype.card s : ℂ) := by
    rw [hr]
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hcard : (Fintype.card s : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hr0 : r ≠ 0 := fun h => hcard (by rw [← hr2, h, mul_zero])
  have hrs : star r = r := by rw [hr]; simp
  have hHA : HA H = r⁻¹ • A i0 := by
    have hA0 : A i0 = r⁻¹ • ptl H := by
      rw [← hAα]
      change ptl ((F i0 ⊗ₖ (1 : Matrix a a ℂ)) * H) = _
      rw [hF0, ← hr, Matrix.smul_kronecker, Matrix.one_kronecker_one, Matrix.smul_mul,
        Matrix.one_mul, map_smul]
    rw [hA0, smul_smul, ← mul_inv, hr2]
    rfl
  have hA0 : A i0 = r • HA H := by
    rw [hHA, smul_smul, mul_inv_cancel₀ hr0, one_smul]
  have hHAherm : (HA H)ᴴ = HA H := by
    rw [hHA, Matrix.conjTranspose_smul, hAherm, star_inv₀, hrs]
  set P := Matrix.vecMulVec v (star v) with hP
  obtain ⟨hlr, hHAP, hPHA⟩ := eig_real (HA H) hHAherm v hv lam hl
  have hA0comm : A i0 * P = P * A i0 := by
    rw [hA0, Matrix.smul_mul, Matrix.mul_smul, hHAP, hPHA]
  have hcα : ∀ α, α ≠ i0 → star (c α) = c α ∧ A α * P = c α • P ∧ P * A α = c α • P :=
    fun α hα => eig_real (A α) (hAherm α) v hv (c α) (hc α hα)
  set cc : κ → ℂ := fun α => if α = i0 then 0 else c α with hcc
  have hsum : ∑ α ∈ Finset.univ.erase i0, c α • F α = ∑ α, cc α • F α := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i0)]
    simp only [hcc, if_pos rfl, zero_smul, add_zero]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [if_neg (Finset.ne_of_mem_erase hα)]
  have hHaH : Ha.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [hHa, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hlr,
      Matrix.conjTranspose_sum]
    congr 1
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [Matrix.conjTranspose_smul, (hherm α).eq, (hcα α (Finset.ne_of_mem_erase hα)).1]
  have lhs : ∀ X : Matrix s s ℂ,
      H * (X ⊗ₖ P) - (X ⊗ₖ P) * H =
        ∑ α, ((F α * X) ⊗ₖ (A α * P) - (X * F α) ⊗ₖ (P * A α)) := by
    intro X
    conv_lhs => rw [hexp]
    simp only [Finset.sum_mul, Finset.mul_sum, ← Matrix.mul_kronecker_mul,
      ← Finset.sum_sub_distrib]
  have rhs : ∀ X : Matrix s s ℂ,
      (Ha * X) ⊗ₖ P - (X * Ha) ⊗ₖ P =
        ∑ α, ((F α * X) ⊗ₖ (cc α • P) - (X * F α) ⊗ₖ (cc α • P)) := by
    intro X
    have e : (Ha * X) ⊗ₖ P - (X * Ha) ⊗ₖ P =
        ((∑ α, cc α • F α) * X) ⊗ₖ P - (X * ∑ α, cc α • F α) ⊗ₖ P := by
      rw [hHa, hsum, Matrix.add_mul, Matrix.mul_add, Matrix.add_kronecker, Matrix.add_kronecker,
        Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
      abel
    rw [e]
    simp only [Finset.sum_mul, Finset.mul_sum, ← sum_kron, ← Finset.sum_sub_distrib,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_kronecker, Matrix.kronecker_smul]
  have key : ∀ X : Matrix s s ℂ,
      H * (X ⊗ₖ P) - (X ⊗ₖ P) * H = (Ha * X) ⊗ₖ P - (X * Ha) ⊗ₖ P := by
    intro X
    rw [lhs, rhs]
    refine Finset.sum_congr rfl fun α _ => ?_
    by_cases hα : α = i0
    · subst hα
      have hcomm0 : F α * X = X * F α := by
        rw [hF0, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
      simp [hcc, hA0comm, hcomm0]
    · obtain ⟨-, h1, h2⟩ := hcα α hα
      rw [h1, h2]
      simp [hcc, hα]
  exact ⟨hHaH, fun t X => conj_eq_of_comm H hH Ha hHaH P key X t⟩


theorem mixed_iff
    (H : Matrix (s × a) (s × a) ℂ) (hH : H.IsHermitian)
    (F : κ → Matrix s s ℂ) (i0 : κ) (hF : IsFixedBasis F i0)
    (M : Set (Matrix a a ℂ)) (hM : ∀ ρa ∈ M, WildeQIT.IsDensityOperator ρa) :
    StationaryControlMixed H M ↔
      ∀ ρa ∈ M, (∀ α, α ≠ i0 → ∃ c : ℂ, coeffOp H F α * ρa = c • ρa) ∧
        HA H * ρa = ρa * HA H := by
  classical
  have hexp := expansion F i0 hF H
  obtain ⟨A, hA⟩ : ∃ A : κ → Matrix a a ℂ, A = fun α => coeffOp H F α := ⟨_, rfl⟩
  have hAα : ∀ α, coeffOp H F α = A α := fun α => by rw [hA]
  simp only [hAα] at hexp ⊢
  have hF' := hF
  obtain ⟨hherm, hF0, htr0, horth, hspan⟩ := hF
  have ht : ∀ α β, (F α * F β).trace = if α = β then 1 else 0 := by
    intro α β
    have := horth α β
    rwa [(hherm α).eq] at this
  -- the `A_α` are Hermitian
  have hAherm : ∀ α, (A α)ᴴ = A α := by
    intro α
    have h1 : H = ∑ β, F β ⊗ₖ (A β)ᴴ := by
      have := congrArg Matrix.conjTranspose hexp
      rw [hH.eq, Matrix.conjTranspose_sum] at this
      simpa [Matrix.conjTranspose_kronecker, (hherm _).eq] using this
    have h2 := coeff_sum F i0 hF' (fun β => (A β)ᴴ) α
    rw [← h1] at h2
    rw [← h2, ← hAα]
    rfl
  -- `H_A` is a nonzero multiple of `A_0`
  have hne : Nonempty s := by
    rcases isEmpty_or_nonempty s with h | h
    · have := horth i0 i0
      simp [Matrix.trace] at this
    · exact h
  obtain ⟨r, hr⟩ : ∃ r : ℂ, r = (Real.sqrt (Fintype.card s) : ℂ) := ⟨_, rfl⟩
  have hr2 : r * r = (Fintype.card s : ℂ) := by
    rw [hr]
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hcard : (Fintype.card s : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hr0 : r ≠ 0 := fun h => hcard (by rw [← hr2, h, mul_zero])
  have hHA : HA H = r⁻¹ • A i0 := by
    have hA0 : A i0 = r⁻¹ • ptl H := by
      rw [← hAα]
      change ptl ((F i0 ⊗ₖ (1 : Matrix a a ℂ)) * H) = _
      rw [hF0, ← hr, Matrix.smul_kronecker, Matrix.one_kronecker_one, Matrix.smul_mul,
        Matrix.one_mul, map_smul]
    rw [hA0, smul_smul, ← mul_inv, hr2]
    rfl
  have hHAcomm : ∀ ρa : Matrix a a ℂ,
      HA H * ρa = ρa * HA H ↔ A i0 * ρa = ρa * A i0 := by
    intro ρa
    rw [hHA, Matrix.smul_mul, Matrix.mul_smul]
    exact (smul_right_injective _ (inv_ne_zero hr0)).eq_iff
  -- the two sides of the commutator with `X ⊗ ρ_a`
  have lhs : ∀ (X : Matrix s s ℂ) (ρa : Matrix a a ℂ),
      H * (X ⊗ₖ ρa) - (X ⊗ₖ ρa) * H =
        ∑ α, ((F α * X) ⊗ₖ (A α * ρa) - (X * F α) ⊗ₖ (ρa * A α)) := by
    intro X ρa
    conv_lhs => rw [hexp]
    simp only [Finset.sum_mul, Finset.mul_sum, ← Matrix.mul_kronecker_mul,
      ← Finset.sum_sub_distrib]
  have rhs : ∀ (g : κ → ℂ) (X : Matrix s s ℂ) (ρa : Matrix a a ℂ),
      ((∑ α, g α • F α) * X) ⊗ₖ ρa - (X * ∑ α, g α • F α) ⊗ₖ ρa =
        ∑ α, ((F α * X) ⊗ₖ (g α • ρa) - (X * F α) ⊗ₖ (g α • ρa)) := by
    intro g X ρa
    simp only [Finset.sum_mul, Finset.mul_sum, ← sum_kron, ← Finset.sum_sub_distrib,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_kronecker, Matrix.kronecker_smul]
  constructor
  · -- necessity
    intro hSC ρa hρa
    obtain ⟨Ha, hHa, hev⟩ := hSC ρa hρa
    have hd : ∀ ρ, WildeQIT.IsDensityOperator ρ →
        H * (ρ ⊗ₖ ρa) - (ρ ⊗ₖ ρa) * H = (Ha * ρ) ⊗ₖ ρa - (ρ * Ha) ⊗ₖ ρa :=
      fun ρ hρ => comm_of_conj_eq H hH Ha hHa ρ ρa (fun t => hev t ρ hρ)
    let L : Matrix s s ℂ →ₗ[ℂ] Matrix (s × a) (s × a) ℂ :=
      { toFun := fun X =>
          H * (X ⊗ₖ ρa) - (X ⊗ₖ ρa) * H - ((Ha * X) ⊗ₖ ρa - (X * Ha) ⊗ₖ ρa)
        map_add' := fun X Y => by
          simp only [Matrix.add_kronecker, Matrix.mul_add, Matrix.add_mul]
          abel
        map_smul' := fun c X => by
          simp only [Matrix.smul_kronecker, Matrix.mul_smul, Matrix.smul_mul, smul_sub,
            RingHom.id_apply] }
    have hall : ∀ X : Matrix s s ℂ,
        H * (X ⊗ₖ ρa) - (X ⊗ₖ ρa) * H = (Ha * X) ⊗ₖ ρa - (X * Ha) ⊗ₖ ρa := fun X =>
      sub_eq_zero.mp (linear_eq_zero_of_density L (fun ρ hρ => sub_eq_zero.mpr (hd ρ hρ)) X)
    -- `X = 1`: every `A_α` commutes with `ρ_a`
    have hAcomm : ∀ β, A β * ρa = ρa * A β := by
      intro β
      have e : ∑ α, F α ⊗ₖ (A α * ρa - ρa * A α) = 0 := by
        have h1 := hall 1
        rw [lhs, Matrix.mul_one, Matrix.one_mul, sub_self] at h1
        rw [← h1]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [Matrix.mul_one, Matrix.one_mul, kron_sub]
      have h2 := coeff_sum F i0 hF' (fun α => A α * ρa - ρa * A α) β
      rw [e, Matrix.mul_zero, map_zero] at h2
      exact sub_eq_zero.mp h2.symm
    refine ⟨fun β hβ => ?_, (hHAcomm ρa).mpr (hAcomm i0)⟩
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
      (show Ha ∈ Submodule.span ℂ (Set.range F) by rw [hspan]; trivial)
    refine ⟨g β, ?_⟩
    -- the defects `D_α = A_α ρ_a - g_α ρ_a`
    have e2 : ∀ X : Matrix s s ℂ,
        ∑ α, ((F α * X) ⊗ₖ (A α * ρa - g α • ρa) - (X * F α) ⊗ₖ (A α * ρa - g α • ρa)) = 0 := by
      intro X
      have h1 := hall X
      rw [lhs, ← hg, rhs, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [kron_sub, kron_sub, ← hAcomm α]
      abel
    ext k l
    -- the slice `G = Σ_α (D_α)_{kl} F_α` is central, hence scalar
    set G : Matrix s s ℂ := ∑ α, (A α * ρa - g α • ρa) k l • F α with hG
    have hGc : ∀ X : Matrix s s ℂ, G * X = X * G := by
      intro X
      have h1 := congrArg (slice k l) (e2 X)
      rw [map_sum, map_zero] at h1
      simp only [map_sub, slice_kronecker] at h1
      rw [← sub_eq_zero, ← h1, hG, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Matrix.smul_mul, Matrix.mul_smul]
    obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_iff_commute_single'.mpr
      (fun i j => (hGc (Matrix.single i j 1)).symm)
    have hcoef : (F β * G).trace = (A β * ρa - g β • ρa) k l := by
      rw [hG, Finset.mul_sum, Matrix.trace_sum]
      simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, ht]
      simp
    have hzero : (F β * G).trace = 0 := by
      rw [← hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
        Matrix.mul_one, Matrix.trace_smul, htr0 β hβ, smul_zero]
    have := hcoef.symm.trans hzero
    simpa [sub_eq_zero] using this
  · -- sufficiency
    intro h ρa hρa
    obtain ⟨hcs, hcomm⟩ := h ρa hρa
    have hcs' : ∀ α, ∃ c : ℂ, α ≠ i0 → A α * ρa = c • ρa := by
      intro α
      by_cases hα : α = i0
      · exact ⟨0, fun h => absurd hα h⟩
      · obtain ⟨c, hc⟩ := hcs α hα
        exact ⟨c, fun _ => hc⟩
    choose c hc using hcs'
    have hρH : ρaᴴ = ρa := (hM ρa hρa).1.isHermitian.eq
    have hρtr : ρa.trace = 1 := (hM ρa hρa).2
    have hA0 : A i0 * ρa = ρa * A i0 := (hHAcomm ρa).mp hcomm
    have hc' : ∀ α, α ≠ i0 → ρa * A α = star (c α) • ρa := by
      intro α hα
      have := congrArg Matrix.conjTranspose (hc α hα)
      rwa [Matrix.conjTranspose_mul, hAherm, hρH, Matrix.conjTranspose_smul, hρH] at this
    have hreal : ∀ α, α ≠ i0 → star (c α) = c α := by
      intro α hα
      have t1 := congrArg Matrix.trace (hc α hα)
      have t2 := congrArg Matrix.trace (hc' α hα)
      rw [Matrix.trace_smul, hρtr, smul_eq_mul, mul_one] at t1 t2
      rw [← t2, ← t1, Matrix.trace_mul_comm]
    set cc : κ → ℂ := fun α => if α = i0 then 0 else c α with hcc
    have hccstar : ∀ α, star (cc α) = cc α := by
      intro α
      by_cases hα : α = i0
      · simp [hcc, hα]
      · simp only [hcc, if_neg hα]
        exact hreal α hα
    set Ha : Matrix s s ℂ := ∑ α, cc α • F α with hHa
    have hHaH : Ha.IsHermitian := by
      unfold Matrix.IsHermitian
      rw [hHa, Matrix.conjTranspose_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Matrix.conjTranspose_smul, (hherm α).eq, hccstar]
    have key : ∀ X : Matrix s s ℂ,
        H * (X ⊗ₖ ρa) - (X ⊗ₖ ρa) * H = (Ha * X) ⊗ₖ ρa - (X * Ha) ⊗ₖ ρa := by
      intro X
      rw [lhs, hHa, rhs]
      refine Finset.sum_congr rfl fun α _ => ?_
      by_cases hα : α = i0
      · subst hα
        have hcomm0 : F α * X = X * F α := by
          rw [hF0, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
        simp [hcc, hA0, hcomm0]
      · rw [hc α hα, hc' α hα, hreal α hα]
        simp [hcc, hα]
    exact ⟨Ha, hHaH, fun t ρ _ => conj_eq_of_comm H hH Ha hHaH ρa key ρ t⟩

lemma vecMulVec_smul_self (u : a → ℂ) (k : ℂ) :
    Matrix.vecMulVec (k • u) (star (k • u)) = (k * star k) • Matrix.vecMulVec u (star u) := by
  rw [star_smul, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul, mul_comm]

lemma proj_mulVec_self (u : a → ℂ) (hu : star u ⬝ᵥ u = 1) :
    Matrix.vecMulVec u (star u) *ᵥ u = u := by
  rw [Matrix.vecMulVec_mulVec, hu]
  simp

end pure

end BaconThesis.Control.SolMpure

open BaconThesis.Control BaconThesis.Control.SolMpure in
theorem solution {s a κ : Type} [Fintype s] [DecidableEq s] [Fintype a]
    [DecidableEq a] [Fintype κ] [DecidableEq κ]
    (H : Matrix (s × a) (s × a) ℂ) (hH : H.IsHermitian)
    (F : κ → Matrix s s ℂ) (i0 : κ) (hF : IsFixedBasis F i0) (A : Set (a → ℂ)) :
    StationaryControlPure H A ↔
      ∀ v ∈ A, (∀ α, α ≠ i0 → ∃ c : ℂ, coeffOp H F α *ᵥ v = c • v) ∧
        ∃ lam : ℂ, HA H *ᵥ v = lam • v := by
  classical
  constructor
  · intro hSC v hv
    by_cases hv0 : v = 0
    · subst hv0
      exact ⟨fun _ _ => ⟨0, by simp⟩, ⟨0, by simp⟩⟩
    obtain ⟨k, hk, hku⟩ := exists_normalize v hv0
    set u := k • v with hu
    set P := Matrix.vecMulVec u (star u) with hP
    have hPv : P = (k * star k) • Matrix.vecMulVec v (star v) := vecMulVec_smul_self v k
    obtain ⟨Ha, hHa, hev⟩ := hSC v hv
    have hmix : StationaryControlMixed H {P} := by
      intro ρa hρa
      rw [Set.mem_singleton_iff] at hρa
      subst hρa
      refine ⟨Ha, hHa, fun t ρ hρ => ?_⟩
      rw [hPv, Matrix.kronecker_smul, Matrix.mul_smul, Matrix.smul_mul, hev t ρ hρ,
        Matrix.kronecker_smul]
    have hPd : WildeQIT.IsDensityOperator P :=
      ⟨Matrix.posSemidef_vecMulVec_self_star _, by
        rw [hP, Matrix.trace_vecMulVec, dotProduct_comm]; exact hku⟩
    obtain ⟨hcs, hcomm⟩ := (mixed_iff H hH F i0 hF {P}
      (fun ρa h => (Set.mem_singleton_iff.mp h) ▸ hPd)).mp hmix P rfl
    have hPu : P *ᵥ u = u := proj_mulVec_self u hku
    have descale : ∀ (M : Matrix a a ℂ) (μ : ℂ), M *ᵥ u = μ • u → M *ᵥ v = μ • v := by
      intro M μ h
      rw [hu, Matrix.mulVec_smul, smul_comm] at h
      exact smul_right_injective _ hk h
    refine ⟨fun α hα => ?_, ?_⟩
    · obtain ⟨c, hc⟩ := hcs α hα
      refine ⟨c, descale _ _ ?_⟩
      rw [← hPu, Matrix.mulVec_mulVec, hc, Matrix.smul_mulVec, hPu]
    · refine ⟨star u ⬝ᵥ HA H *ᵥ u, descale _ _ ?_⟩
      conv_lhs => rw [← hPu, Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hP,
        Matrix.vecMulVec_mulVec]
      simp
  · intro h v hv
    obtain ⟨hcs, lam, hl⟩ := h v hv
    by_cases hv0 : v = 0
    · subst hv0
      refine ⟨0, Matrix.isHermitian_zero, fun t ρ _ => ?_⟩
      simp
    obtain ⟨k, hk, hku⟩ := exists_normalize v hv0
    set u := k • v with hu
    have hPv : Matrix.vecMulVec u (star u) = (k * star k) • Matrix.vecMulVec v (star v) :=
      vecMulVec_smul_self v k
    have hkk : k * star k ≠ 0 := mul_ne_zero hk (star_ne_zero.mpr hk)
    have rescale : ∀ (M : Matrix a a ℂ) (μ : ℂ), M *ᵥ v = μ • v → M *ᵥ u = μ • u := by
      intro M μ h
      rw [hu, Matrix.mulVec_smul, h, smul_comm]
    have hcs' : ∀ α, ∃ c : ℂ, α ≠ i0 → coeffOp H F α *ᵥ u = c • u := by
      intro α
      by_cases hα : α = i0
      · exact ⟨0, fun h => absurd hα h⟩
      · obtain ⟨c, hc⟩ := hcs α hα
        exact ⟨c, fun _ => rescale _ _ hc⟩
    choose c hc using hcs'
    obtain ⟨hHaH, hev⟩ := suff H hH F i0 hF u hku c lam hc (rescale _ _ hl) _ rfl
    refine ⟨_, hHaH, fun t ρ _ => ?_⟩
    have e := hev t ρ
    rw [hPv, Matrix.kronecker_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.kronecker_smul] at e
    exact smul_right_injective _ hkk e
