-- Prove2me | solution 1 for BaconThesis.Control.eq_3_6
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T22:57:18.867282+00:00
-- url     : https://prove2.me/submissions/2b695874-4378-427d-9e25-d3512a1455a8

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_BaconThesis_Control_evol
import Definitions.Def_BaconThesis_Control_IsFixedBasis
import Definitions.Def_BaconThesis_Control_coeffOp
import Definitions.Def_BaconThesis_Control_HA

open scoped Matrix Kronecker ComplexOrder

set_option linter.unusedSectionVars false

namespace BaconThesis.Control.SolM3_6

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


end BaconThesis.Control.SolM3_6

open BaconThesis.Control BaconThesis.Control.SolM3_6 in
theorem solution {s a : Type} [Fintype s] [DecidableEq s] [Fintype a] [DecidableEq a]
    (H : Matrix (s × a) (s × a) ℂ) (hH : H.IsHermitian) (v : a → ℂ)
    (Ha : Matrix s s ℂ) (hHa : Ha.IsHermitian)
    (h32 : ∀ t : ℝ, ∀ ρ : Matrix s s ℂ, WildeQIT.IsDensityOperator ρ →
      evol H t * (ρ ⊗ₖ Matrix.vecMulVec v (star v)) * (evol H t)ᴴ =
        (evol Ha t * ρ * (evol Ha t)ᴴ) ⊗ₖ Matrix.vecMulVec v (star v)) :
    ∀ ρ : Matrix s s ℂ, WildeQIT.IsDensityOperator ρ →
      H * (ρ ⊗ₖ Matrix.vecMulVec v (star v)) - (ρ ⊗ₖ Matrix.vecMulVec v (star v)) * H =
        (Ha * ρ - ρ * Ha) ⊗ₖ Matrix.vecMulVec v (star v) := by
  intro ρ hρ
  rw [comm_of_conj_eq H hH Ha hHa ρ _ (fun t => h32 t ρ hρ), sub_kron]
