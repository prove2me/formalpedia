-- Prove2me | solution 1 for ConleyZehnder.hamiltonian_joinedIn_cube
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T20:25:57.988814+00:00
-- url     : https://prove2.me/submissions/ace4c840-1f37-4165-8510-eb2ab088240a

import Definitions.Def_ConleyZehnder_Setting
import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Complex.Polynomial.Basic



/-! The standard symplectic form and the Hamiltonian operators `Z_M(e, f)` built on frames. -/

namespace ConleyZehnder

open Matrix

variable {n : ℕ}

/-- Vectors of `ℝ²ⁿ`. -/
abbrev Vec (n : ℕ) := Fin n ⊕ Fin n → ℝ

/-- `Ω₀(u, v) = -uᵀ J₀ v`. -/
noncomputable def sformL (n : ℕ) : Vec n →ₗ[ℝ] Vec n →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => -(u ⬝ᵥ (J₀ n *ᵥ v)))
    (fun u u' v => by simp [add_dotProduct]; ring)
    (fun c u v => by simp [smul_dotProduct])
    (fun u v v' => by simp [Matrix.mulVec_add, dotProduct_add]; ring)
    (fun c u v => by simp [Matrix.mulVec_smul, dotProduct_smul])

lemma sformL_apply (u v : Vec n) : sformL n u v = -(u ⬝ᵥ (J₀ n *ᵥ v)) := rfl

/-- `(A u) ⬝ w = u ⬝ (Aᵀ w)`. -/
lemma mulVec_dotProduct' (A : Mat n) (u w : Vec n) : (A *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (Aᵀ *ᵥ w) := by
  rw [Matrix.mulVec_transpose, dotProduct_comm u, ← Matrix.dotProduct_mulVec, dotProduct_comm]

lemma J_mulVec_J_mulVec (v : Vec n) : J₀ n *ᵥ (J₀ n *ᵥ v) = -v := by
  rw [Matrix.mulVec_mulVec, Matrix.J_squared, Matrix.neg_mulVec, Matrix.one_mulVec]

lemma vecMul_J (u : Vec n) : u ᵥ* J₀ n = -(J₀ n *ᵥ u) := by
  rw [← Matrix.mulVec_transpose, Matrix.J_transpose, Matrix.neg_mulVec]

lemma sformL_skew (u v : Vec n) : sformL n u v = -sformL n v u := by
  rw [sformL_apply, sformL_apply, Matrix.dotProduct_mulVec, vecMul_J, neg_dotProduct,
    dotProduct_comm]

lemma sformL_self (u : Vec n) : sformL n u u = 0 := by
  have := sformL_skew u u; linarith

lemma sformL_J (u : Vec n) : sformL n u (J₀ n *ᵥ u) = u ⬝ᵥ u := by
  rw [sformL_apply, J_mulVec_J_mulVec, dotProduct_neg, neg_neg]

lemma sformL_nondeg {u : Vec n} (h : ∀ v, sformL n u v = 0) : u = 0 :=
  dotProduct_self_eq_zero.1 (by rw [← sformL_J]; exact h _)

/-- Hamiltonian matrices. -/
def IsHam (Y : Mat n) : Prop := Y * J₀ n + J₀ n * Yᵀ = 0

lemma isHam_iff' (Y : Mat n) : IsHam Y ↔ Yᵀ * J₀ n + J₀ n * Y = 0 := by
  have hJJ : J₀ n * J₀ n = -1 := Matrix.J_squared _ _
  have e1 : ∀ Y : Mat n, J₀ n * (Y * J₀ n + J₀ n * Yᵀ) * J₀ n = -(Yᵀ * J₀ n + J₀ n * Y) := by
    intro Y
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hJJ]
    rw [← Matrix.mul_assoc (J₀ n) (J₀ n), hJJ]
    simp [add_comm]
  have e2 : ∀ Y : Mat n, J₀ n * (Yᵀ * J₀ n + J₀ n * Y) * J₀ n = -(Y * J₀ n + J₀ n * Yᵀ) := by
    intro Y
    have := e1 Yᵀ
    rwa [Matrix.transpose_transpose] at this
  unfold IsHam
  constructor
  · intro h
    have := e1 Y
    rw [h, Matrix.mul_zero, Matrix.zero_mul] at this
    exact neg_eq_zero.1 this.symm
  · intro h
    have := e2 Y
    rw [h, Matrix.mul_zero, Matrix.zero_mul] at this
    exact neg_eq_zero.1 this.symm

lemma sform_ham_expr (Y : Mat n) (u v : Vec n) :
    sformL n (Y *ᵥ u) v + sformL n u (Y *ᵥ v) = -(u ⬝ᵥ ((Yᵀ * J₀ n + J₀ n * Y) *ᵥ v)) := by
  rw [sformL_apply, sformL_apply, mulVec_dotProduct', Matrix.add_mulVec, dotProduct_add,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  ring

lemma IsHam.sform {Y : Mat n} (hY : IsHam Y) (u v : Vec n) :
    sformL n (Y *ᵥ u) v + sformL n u (Y *ᵥ v) = 0 := by
  rw [sform_ham_expr, (isHam_iff' Y).1 hY]; simp

lemma isHam_of_sform {Y : Mat n} (h : ∀ u v, sformL n (Y *ᵥ u) v + sformL n u (Y *ᵥ v) = 0) :
    IsHam Y := by
  rw [isHam_iff']
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [sform_ham_expr, Matrix.mulVec_single_one, single_one_dotProduct] at this
  simp only [Matrix.col_apply, Matrix.add_apply, Matrix.zero_apply] at this ⊢
  linarith

lemma IsHam.add {X Y : Mat n} (hX : IsHam X) (hY : IsHam Y) : IsHam (X + Y) := by
  unfold IsHam at *
  rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]
  rw [show X * J₀ n + Y * J₀ n + (J₀ n * Xᵀ + J₀ n * Yᵀ)
    = (X * J₀ n + J₀ n * Xᵀ) + (Y * J₀ n + J₀ n * Yᵀ) by abel, hX, hY, add_zero]

lemma IsHam.smul {X : Mat n} (c : ℝ) (hX : IsHam X) : IsHam (c • X) := by
  unfold IsHam at *
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

lemma isHam_zero : IsHam (0 : Mat n) := by simp [IsHam]

lemma isHam_sum {ι : Type*} (s : Finset ι) (g : ι → Mat n) (h : ∀ i ∈ s, IsHam (g i)) :
    IsHam (∑ i ∈ s, g i) :=
  Finset.sum_induction _ IsHam (fun _ _ => IsHam.add) isHam_zero h

/-- `B(e, f) v = Ω₀(v, f) e + Ω₀(v, e) f`. -/
noncomputable def Bop (e f : Vec n) : Mat n :=
  vecMulVec e (-(J₀ n *ᵥ f)) + vecMulVec f (-(J₀ n *ᵥ e))

lemma Bop_mulVec (e f v : Vec n) : Bop e f *ᵥ v = sformL n v f • e + sformL n v e • f := by
  rw [Bop, Matrix.add_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul,
    op_smul_eq_smul, sformL_apply, sformL_apply, neg_dotProduct, neg_dotProduct,
    dotProduct_comm (J₀ n *ᵥ f), dotProduct_comm (J₀ n *ᵥ e)]

lemma Bop_isHam (e f : Vec n) : IsHam (Bop e f) := by
  apply isHam_of_sform
  intro u v
  simp only [Bop_mulVec, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [sformL_skew e v, sformL_skew f v]
  ring

lemma continuous_Bop : Continuous fun p : Vec n × Vec n => Bop p.1 p.2 := by
  unfold Bop
  have hJ : ∀ g : Vec n × Vec n → Vec n, Continuous g → Continuous fun p => -(J₀ n *ᵥ g p) :=
    fun g hg => (continuous_const.matrix_mulVec hg).neg
  exact (continuous_fst.matrix_vecMulVec (hJ _ continuous_snd)).add
    (continuous_snd.matrix_vecMulVec (hJ _ continuous_fst))

/-- `Z_M(e, f) = Σᵢⱼ Mᵢⱼ B(eᵢ, fⱼ)`. -/
noncomputable def Zmat {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (e f : ι → Vec n) : Mat n :=
  ∑ i, ∑ j, M i j • Bop (e i) (f j)

lemma Zmat_mulVec {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (e f : ι → Vec n) (v : Vec n) :
    Zmat M e f *ᵥ v = ∑ i, ∑ j, M i j • (sformL n v (f j) • e i + sformL n v (e i) • f j) := by
  simp only [Zmat, Matrix.sum_mulVec, Matrix.smul_mulVec, Bop_mulVec]

lemma Zmat_isHam {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (e f : ι → Vec n) :
    IsHam (Zmat M e f) :=
  isHam_sum _ _ fun i _ => isHam_sum _ _ fun j _ => (Bop_isHam _ _).smul _

lemma continuous_Zmat {ι : Type*} [Fintype ι] (e f : ι → Vec n) :
    Continuous fun M : Matrix ι ι ℝ => Zmat M e f := by
  unfold Zmat
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact (continuous_id.matrix_elem i j).smul continuous_const

/-- A symplectic frame: `Ω₀(eᵢ, fⱼ) = δᵢⱼ`, `Ω₀(eᵢ, eⱼ) = Ω₀(fᵢ, fⱼ) = 0`. -/
structure IsFrame {ι : Type*} [DecidableEq ι] (e f : ι → Vec n) : Prop where
  ef : ∀ i j, sformL n (e i) (f j) = if i = j then 1 else 0
  ee : ∀ i j, sformL n (e i) (e j) = 0
  ff : ∀ i j, sformL n (f i) (f j) = 0

lemma IsFrame.det_one_sub_Zmat {ι : Type*} [Fintype ι] [DecidableEq ι] {e f : ι → Vec n}
    (hF : IsFrame e f) {M : Matrix ι ι ℝ} (h1 : (1 - M).det ≠ 0) (h2 : (1 + M).det ≠ 0) :
    (1 - Zmat M e f).det ≠ 0 := by
  intro hd
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
  -- `hv : v = Z v`
  set a : ι → ℝ := fun j => sformL n v (f j) with ha_def
  set b : ι → ℝ := fun i => sformL n v (e i) with hb_def
  have hfe : ∀ i j, sformL n (f j) (e i) = -(if i = j then 1 else 0) := by
    intro i j; rw [sformL_skew, hF.ef]
  have hZ : ∀ w : Vec n, sformL n (Zmat M e f *ᵥ v) w
      = ∑ i, ∑ j, M i j * (a j * sformL n (e i) w + b i * sformL n (f j) w) := by
    intro w
    rw [Zmat_mulVec]
    simp only [map_sum, map_add, map_smul, LinearMap.sum_apply,
      LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, ha_def, hb_def]
  have ha : ∀ l, a l = ∑ j, M l j * a j := by
    intro l
    have h1 : a l = sformL n (Zmat M e f *ᵥ v) (f l) := by
      show sformL n v (f l) = _; rw [← hv]
    rw [h1, hZ]
    simp only [hF.ef, hF.ff, mul_zero, add_zero, mul_ite, mul_one]
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq', mul_comm]
  have hb : ∀ l, b l = -∑ i, b i * M i l := by
    intro l
    have h1 : b l = sformL n (Zmat M e f *ᵥ v) (e l) := by
      show sformL n v (e l) = _; rw [← hv]
    rw [h1, hZ]
    simp only [hF.ee, hfe, mul_zero, zero_add, mul_neg, mul_ite, mul_one, Finset.sum_neg_distrib]
    simp [Finset.sum_ite_eq, mul_comm]
  have ha0 : a = 0 := by
    by_contra hne
    apply h1
    refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨a, hne, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
    funext l
    rw [ha l]; rfl
  have hb0 : b = 0 := by
    by_contra hne
    apply h2
    refine Matrix.exists_vecMul_eq_zero_iff.1 ⟨b, hne, ?_⟩
    rw [Matrix.vecMul_add, Matrix.vecMul_one]
    funext l
    simp only [Pi.add_apply, Pi.zero_apply]
    rw [hb l]
    simp [Matrix.vecMul, dotProduct]
  apply hv0
  rw [hv, Zmat_mulVec]
  have ha' : ∀ j, sformL n v (f j) = 0 := fun j => congrFun ha0 j
  have hb' : ∀ i, sformL n v (e i) = 0 := fun i => congrFun hb0 i
  simp [ha', hb']

end ConleyZehnder

/-! Cayley transform between `Sp*` and Hamiltonian matrices without eigenvalue `1`. -/

namespace ConleyZehnder

open Matrix

variable {n : ℕ}

/-- Hamiltonian matrices without eigenvalue `1`. -/
def HamStar (n : ℕ) : Set (Mat n) := {X | X * J₀ n + J₀ n * Xᵀ = 0 ∧ (1 - X).det ≠ 0}

/-- The Cayley transform `(X + 1)(X - 1)⁻¹`. -/
noncomputable def cay (X : Mat n) : Mat n := (X + 1) * (X - 1)⁻¹

lemma det_sub_one_ne_zero {X : Mat n} (h : (1 - X).det ≠ 0) : (X - 1).det ≠ 0 := by
  have : X - 1 = -(1 - X) := by abel
  rw [this, Matrix.det_neg]
  simp [Fintype.card_sum, h]

lemma isUnit_det_sub_one {X : Mat n} (h : (1 - X).det ≠ 0) : IsUnit (X - 1).det :=
  isUnit_iff_ne_zero.2 (det_sub_one_ne_zero h)

lemma one_sub_cay {X : Mat n} (h : (1 - X).det ≠ 0) : 1 - cay X = (-2 : ℝ) • (X - 1)⁻¹ := by
  have hu := isUnit_det_sub_one h
  calc 1 - cay X = (X - 1) * (X - 1)⁻¹ - (X + 1) * (X - 1)⁻¹ := by
        rw [Matrix.mul_nonsing_inv _ hu]; rfl
    _ = (X - 1 - (X + 1)) * (X - 1)⁻¹ := by rw [← Matrix.sub_mul]
    _ = ((-2 : ℝ) • (1 : Mat n)) * (X - 1)⁻¹ := by
        congr 1; rw [show X - 1 - (X + 1) = -((1 : Mat n) + 1) by abel]
        rw [neg_smul, two_smul]
    _ = (-2 : ℝ) • (X - 1)⁻¹ := by rw [Matrix.smul_mul, Matrix.one_mul]

lemma det_one_sub_cay_ne_zero {X : Mat n} (h : (1 - X).det ≠ 0) : (1 - cay X).det ≠ 0 := by
  rw [one_sub_cay h, Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (inv_ne_zero (det_sub_one_ne_zero h))

/-- `(X - 1) cay X = X + 1`. -/
lemma sub_one_mul_cay {X : Mat n} (h : (1 - X).det ≠ 0) : (X - 1) * cay X = X + 1 := by
  have hu := isUnit_det_sub_one h
  have hc : (X - 1) * (X + 1) = (X + 1) * (X - 1) := by noncomm_ring
  unfold cay
  rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

lemma cay_eq_of {X W : Mat n} (h : (1 - X).det ≠ 0) (hW : (X - 1) * W = X + 1) : cay X = W := by
  have hu := isUnit_det_sub_one h
  have e : (X - 1) * cay X = (X - 1) * W := by rw [sub_one_mul_cay h, hW]
  have := congrArg (fun M => (X - 1)⁻¹ * M) e
  simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul] using this

lemma cay_mem_symplectic {X : Mat n} (hH : X * J₀ n + J₀ n * Xᵀ = 0) (h : (1 - X).det ≠ 0) :
    cay X ∈ symplecticGroup (Fin n) ℝ := by
  rw [SymplecticGroup.mem_iff]
  set Q := X - 1 with hQdef
  have hu : IsUnit Q.det := isUnit_det_sub_one h
  have hut : IsUnit Qᵀ.det := by rwa [Matrix.det_transpose]
  have hQ : Q * cay X = X + 1 := sub_one_mul_cay h
  have key : Q * (cay X * J₀ n * (cay X)ᵀ) * Qᵀ = Q * J₀ n * Qᵀ := by
    have e1 : Q * (cay X * J₀ n * (cay X)ᵀ) * Qᵀ = (Q * cay X) * J₀ n * (Q * cay X)ᵀ := by
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e1, hQ, hQdef]
    simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one]
    have : (X + 1) * J₀ n * (Xᵀ + 1) - (X - 1) * J₀ n * (Xᵀ - 1)
        = (2 : ℝ) • (X * J₀ n + J₀ n * Xᵀ) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
        Matrix.one_mul, two_smul]
      abel
    rw [hH, smul_zero] at this
    exact sub_eq_zero.1 this
  have := congrArg (fun M => Q⁻¹ * M * Qᵀ⁻¹) key
  simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul] at this
  simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hut] using this

lemma cay_mem_spStar {X : Mat n} (hX : X ∈ HamStar n) : cay X ∈ SpStar n :=
  ⟨cay_mem_symplectic hX.1 hX.2, det_one_sub_cay_ne_zero hX.2⟩

lemma cay_mem_hamStar {A : Mat n} (hA : A ∈ SpStar n) : cay A ∈ HamStar n := by
  refine ⟨?_, det_one_sub_cay_ne_zero hA.2⟩
  have hS : A * J₀ n * Aᵀ = J₀ n := (SymplecticGroup.mem_iff).1 hA.1
  set Q := A - 1 with hQdef
  have hu : IsUnit Q.det := isUnit_det_sub_one hA.2
  have hut : IsUnit Qᵀ.det := by rwa [Matrix.det_transpose]
  have hQ : Q * cay A = A + 1 := sub_one_mul_cay hA.2
  have key : Q * (cay A * J₀ n + J₀ n * (cay A)ᵀ) * Qᵀ = 0 := by
    have e1 : Q * (cay A * J₀ n + J₀ n * (cay A)ᵀ) * Qᵀ
        = (Q * cay A) * J₀ n * Qᵀ + Q * J₀ n * (Q * cay A)ᵀ := by
      simp [Matrix.transpose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    rw [e1, hQ, hQdef]
    simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one]
    have : (A + 1) * J₀ n * (Aᵀ - 1) + (A - 1) * J₀ n * (Aᵀ + 1)
        = (2 : ℝ) • (A * J₀ n * Aᵀ - J₀ n) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
        Matrix.one_mul, two_smul]
      abel
    rw [this, hS, sub_self, smul_zero]
  have := congrArg (fun M => Q⁻¹ * M * Qᵀ⁻¹) key
  simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul,
    Matrix.zero_mul, Matrix.mul_zero] at this
  simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hut] using this

lemma cay_cay {A : Mat n} (h : (1 - A).det ≠ 0) : cay (cay A) = A := by
  have hu : IsUnit (A - 1).det := isUnit_det_sub_one h
  have h2 : (1 - cay A).det ≠ 0 := det_one_sub_cay_ne_zero h
  apply cay_eq_of h2
  have hm : cay A - 1 = (2 : ℝ) • (A - 1)⁻¹ := by
    rw [show cay A - 1 = -(1 - cay A) by abel, one_sub_cay h, neg_smul, neg_neg]
  have hL : (A - 1)⁻¹ * A = 1 + (A - 1)⁻¹ := by
    rw [show (A - 1)⁻¹ * A = (A - 1)⁻¹ * ((A - 1) + 1) by rw [sub_add_cancel]]
    rw [Matrix.mul_add, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
  rw [hm, Matrix.smul_mul, hL, show cay A + 1 = (cay A - 1) + (1 + 1) by abel, hm,
    smul_add, two_smul ℝ (1 : Mat n)]
  abel

lemma continuousOn_cay : ContinuousOn (cay (n := n)) {X | (1 - X).det ≠ 0} := by
  have hs : Continuous fun X : Mat n => X - 1 := continuous_id.sub continuous_const
  have hp : Continuous fun X : Mat n => X + 1 := continuous_id.add continuous_const
  have hd : Continuous fun X : Mat n => (X - 1).det := hs.matrix_det
  have hinv : ContinuousOn (fun X : Mat n => ((X - 1).det)⁻¹) {X | (1 - X).det ≠ 0} :=
    hd.continuousOn.inv₀ fun X hX => det_sub_one_ne_zero hX
  have hadj : Continuous fun X : Mat n => (X - 1).adjugate := hs.matrix_adjugate
  refine (hp.continuousOn.mul (hinv.smul hadj.continuousOn)).congr ?_
  intro X _
  simp [cay, Matrix.inv_def, Ring.inverse_eq_inv']

lemma cay_zero : cay (0 : Mat n) = Wplus n := by
  apply cay_eq_of (by simp)
  simp [Wplus]

/-- The Hamiltonian counterpart of `W⁻`. -/
noncomputable def Yminus (n : ℕ) : Mat n :=
  Matrix.diagonal (Sum.elim (fun j : Fin n => if j.val = 0 then (3 : ℝ) else 0)
    (fun j : Fin n => if j.val = 0 then (-3 : ℝ) else 0))

lemma det_one_sub_Yminus : (1 - Yminus n).det ≠ 0 := by
  unfold Yminus
  rw [show (1 : Mat n) = Matrix.diagonal 1 from rfl, Matrix.diagonal_sub, Matrix.det_diagonal]
  rw [Finset.prod_ne_zero_iff]
  intro i _
  rcases i with j | j <;> by_cases hj : j.val = 0 <;> simp [hj] <;> norm_num

lemma cay_Yminus : cay (Yminus n) = Wminus n := by
  apply cay_eq_of det_one_sub_Yminus
  unfold Yminus Wminus
  rw [show (1 : Mat n) = Matrix.diagonal 1 from rfl, Matrix.diagonal_sub, Matrix.diagonal_add,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rcases i with j | j <;> by_cases hj : j.val = 0 <;> simp [hj] <;> norm_num

lemma Yminus_ham : Yminus n * J₀ n + J₀ n * (Yminus n)ᵀ = 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Yminus, Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.diagonal_apply,
      Matrix.one_apply] <;>
    (rcases eq_or_ne i j with rfl | h <;> simp [*] <;> split_ifs <;> norm_num)

lemma Yminus_mem : Yminus n ∈ HamStar n := ⟨Yminus_ham, det_one_sub_Yminus⟩

lemma zero_mem_hamStar : (0 : Mat n) ∈ HamStar n := ⟨by simp, by simp⟩

/-- Transport: a path in `HamStar` from `cay A` to `0` or `Yminus` gives the target. -/
theorem spStar_path_of_hamStar {A : Mat n} (hA : A ∈ SpStar n)
    (h : JoinedIn (HamStar n) (cay A) 0 ∨ JoinedIn (HamStar n) (cay A) (Yminus n)) :
    ∃ χ : C(unitInterval, Mat n), χ 0 = A ∧ (∀ t, χ t ∈ SpStar n) ∧
      (χ 1 = Wplus n ∨ χ 1 = Wminus n) := by
  have hmap : ∀ {Y : Mat n}, JoinedIn (HamStar n) (cay A) Y →
      JoinedIn (SpStar n) A (cay Y) := by
    intro Y hY
    have := hY.map_continuousOn (f := cay) (continuousOn_cay.mono fun X hX => hX.2)
    rw [cay_cay hA.2] at this
    exact this.mono (Set.image_subset_iff.2 fun X hX => cay_mem_spStar hX)
  rcases h with h | h
  · have hj := hmap h
    rw [cay_zero] at hj
    exact ⟨hj.somePath, by simp, hj.somePath_mem, Or.inl (by simp)⟩
  · have hj := hmap h
    rw [cay_Yminus] at hj
    exact ⟨hj.somePath, by simp, hj.somePath_mem, Or.inr (by simp)⟩

end ConleyZehnder

/-! The semisimple part of a Hamiltonian matrix without eigenvalue `1`. -/

namespace ConleyZehnder

open Matrix Polynomial

variable {n : ℕ}

/-- `τ(A) = J₀ Aᵀ J₀⁻¹ = -J₀ Aᵀ J₀`; `A` is Hamiltonian iff `τ(A) = -A`. -/
noncomputable def tau (A : Mat n) : Mat n := -(J₀ n * Aᵀ * J₀ n)

lemma JJ : J₀ n * J₀ n = -1 := Matrix.J_squared _ _

lemma tau_mul (A B : Mat n) : tau (A * B) = tau B * tau A := by
  unfold tau
  rw [Matrix.transpose_mul]
  have : J₀ n * Bᵀ * J₀ n * (J₀ n * Aᵀ * J₀ n) = -(J₀ n * Bᵀ * Aᵀ * J₀ n) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (J₀ n) (J₀ n), JJ]
    simp
  rw [neg_mul_neg, this, Matrix.mul_assoc (J₀ n) Bᵀ Aᵀ]

lemma tau_one : tau (1 : Mat n) = 1 := by simp [tau, JJ]

lemma tau_add (A B : Mat n) : tau (A + B) = tau A + tau B := by
  simp only [tau, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, neg_add]

lemma tau_smul (c : ℝ) (A : Mat n) : tau (c • A) = c • tau A := by
  simp [tau, Matrix.mul_smul, Matrix.smul_mul]

lemma tau_neg (A : Mat n) : tau (-A) = -tau A := by
  simpa using tau_smul (-1) A

lemma tau_pow (A : Mat n) (k : ℕ) : tau (A ^ k) = tau A ^ k := by
  induction k with
  | zero => simp [tau_one]
  | succ k ih => rw [pow_succ, tau_mul, ih, ← pow_succ']

lemma tau_aeval (A : Mat n) (p : ℝ[X]) : tau (aeval A p) = aeval (tau A) p := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range]
  have : ∀ s : Finset ℕ, tau (∑ i ∈ s, p.coeff i • A ^ i) = ∑ i ∈ s, p.coeff i • tau A ^ i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [tau]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, tau_add, ih, tau_smul, tau_pow]
  exact this _

lemma isHam_iff_tau (A : Mat n) : IsHam A ↔ tau A = -A := by
  unfold IsHam tau
  constructor
  · intro h
    have h' : J₀ n * Aᵀ = -(A * J₀ n) := eq_neg_of_add_eq_zero_right h
    rw [h', Matrix.neg_mul, neg_neg, Matrix.mul_assoc, JJ, Matrix.mul_neg, Matrix.mul_one]
  · intro h
    have h' : J₀ n * Aᵀ * J₀ n = A := by rw [← neg_neg (J₀ n * Aᵀ * J₀ n), h, neg_neg]
    have h2 : J₀ n * Aᵀ * J₀ n * J₀ n = A * J₀ n := by rw [h']
    rw [Matrix.mul_assoc _ (J₀ n) (J₀ n), JJ, Matrix.mul_neg, Matrix.mul_one] at h2
    rw [← h2, neg_add_cancel]


lemma tau_zero : tau (0 : Mat n) = 0 := by simp [tau]

lemma isHam_aeval_odd {A : Mat n} (hA : IsHam A) {p : ℝ[X]} (hp : p.comp (-X) = -p) :
    IsHam (aeval A p) := by
  rw [isHam_iff_tau, tau_aeval, (isHam_iff_tau A).1 hA]
  have : aeval (-A) p = aeval A (p.comp (-X)) := by rw [aeval_comp]; simp
  rw [this, hp, map_neg]

lemma isHam_sub {A B : Mat n} (hA : IsHam A) (hB : IsHam B) : IsHam (A - B) := by
  rw [sub_eq_add_neg]; exact hA.add (by simpa using hB.smul (-1))

/-- Jordan–Chevalley: a Hamiltonian `X` without eigenvalue `1` is joined inside `HamStar` to a
semisimple Hamiltonian `S` (its semisimple part). -/
theorem exists_semisimple_part (X : Mat n) (hX : X ∈ HamStar n) :
    ∃ S : Mat n, Module.End.IsSemisimple (Matrix.toLinAlgEquiv' S) ∧ S ∈ HamStar n ∧
      JoinedIn (HamStar n) X S := by
  set φ := (Matrix.toLinAlgEquiv' : Mat n ≃ₐ[ℝ] Module.End ℝ (Vec n)) with hφ
  obtain ⟨nE, hnE, sE, hsE, hnil, hss, hf⟩ := Module.End.exists_isNilpotent_isSemisimple (f := φ X)
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hnE hsE
  obtain ⟨q, rfl⟩ := hnE
  obtain ⟨p, rfl⟩ := hsE
  set S := aeval X p with hSdef
  set N := aeval X q with hNdef
  have hφS : φ S = aeval (φ X) p := (aeval_algHom_apply φ X p).symm
  have hφN : φ N = aeval (φ X) q := (aeval_algHom_apply φ X q).symm
  replace hss : Module.End.IsSemisimple (φ S) := by rw [hφS]; convert hss using 1 <;> rfl
  replace hnil : IsNilpotent (φ N) := by rw [hφN]; convert hnil using 1 <;> rfl
  have hXNS : X = N + S := φ.injective (by rw [map_add, hφN, hφS]; convert hf using 2 <;> rfl)
  have comm : ∀ a b : ℝ[X], Commute (aeval X a) (aeval X b) := fun a b => by
    show aeval X a * aeval X b = aeval X b * aeval X a
    rw [← map_mul, mul_comm, map_mul]
  have htX : tau X = -X := (isHam_iff_tau X).1 hX.1
  have hcomp : ∀ r : ℝ[X], -tau (aeval X r) = aeval X (-(r.comp (-Polynomial.X))) := by
    intro r
    rw [tau_aeval, htX, map_neg, aeval_comp]; simp
  -- the second decomposition `X = (-τ N) + (-τ S)`
  have hX2 : X = -tau N + -tau S := by rw [← neg_add, ← tau_add, ← hXNS, htX, neg_neg]
  have hNnil : IsNilpotent N := by
    obtain ⟨k, hk⟩ := hnil
    exact ⟨k, φ.injective (by rw [map_pow, hk, map_zero])⟩
  have hN2nil : IsNilpotent (φ (-tau N)) := by
    obtain ⟨k, hk⟩ := hNnil
    refine ⟨k, ?_⟩
    rw [← map_pow, neg_pow, ← tau_pow, hk, tau_zero, mul_zero, map_zero]
  have hS2ss : Module.End.IsSemisimple (φ (-tau S)) := by
    have hm : aeval (φ (tau S)) (minpoly ℝ (φ S)) = 0 := by
      rw [aeval_algHom_apply, ← tau_aeval]
      have : aeval S (minpoly ℝ (φ S)) = 0 :=
        φ.injective (by rw [← aeval_algHom_apply, minpoly.aeval, map_zero])
      rw [this, tau_zero, map_zero]
    have h1 := Module.End.isSemisimple_of_squarefree_aeval_eq_zero hss.minpoly_squarefree hm
    rw [map_neg]
    have h2 := Module.End.IsSemisimple_smul (-1) h1
    have h3 : -φ (tau S) = (-1 : ℝ) • φ (tau S) := (neg_one_smul ℝ _).symm
    rw [h3]; exact h2
  have hc1 : Commute (φ N) (φ S) := (comm q p).map φ
  have hc2 : Commute (φ (-tau N)) (φ (-tau S)) := by
    rw [hcomp, hcomp]; exact (comm _ _).map φ
  obtain ⟨-, hSS⟩ := Module.End.isNilpotent_isSemisimple_unique hnil hss hN2nil hS2ss hc1 hc2
    (by
      have := congrArg φ (hXNS.symm.trans hX2)
      rw [map_add, map_add] at this
      exact this)
  have hSham : IsHam S := by
    rw [isHam_iff_tau]
    have h := φ.injective hSS
    rw [eq_neg_iff_add_eq_zero] at h ⊢
    rw [add_comm]; exact h
  have hNham : IsHam N := by
    have : N = X - S := by rw [hXNS]; abel
    rw [this]; exact isHam_sub hX.1 hSham
  have hu : IsUnit (1 - X) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hX.2)
  have hcommNX : Commute N (1 - X) := by
    rw [hXNS]; exact (Commute.one_right N).sub_right ((Commute.refl N).add_right (comm q p))
  have hmem : ∀ c ∈ Set.Icc (0 : ℝ) 1, S + c • N ∈ HamStar n := by
    intro c _
    refine ⟨hSham.add (hNham.smul c), ?_⟩
    have : 1 - (S + c • N) = (1 - X) + (1 - c) • N := by rw [hXNS]; module
    rw [this]
    have hn : IsNilpotent ((1 - c) • N) := by
      obtain ⟨k, hk⟩ := hNnil
      exact ⟨k, by rw [smul_pow, hk, smul_zero]⟩
    have hu2 := hn.isUnit_add_left_of_commute hu (hcommNX.smul_left (1 - c))
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hu2).ne_zero
  have hS : S ∈ HamStar n := by simpa using hmem 0 (by simp)
  refine ⟨S, hss, hS, ?_⟩
  have hJ := ((convex_Icc (0 : ℝ) 1).isPathConnected (by simp)).joinedIn 1 (by simp) 0 (by simp)
  have := (hJ.map (f := fun c : ℝ => S + c • N) (by fun_prop)).mono
    (by rintro _ ⟨c, hc, rfl⟩; exact hmem c hc)
  simpa [hXNS, add_comm] using this

end ConleyZehnder

/-! Squashing the spectrum of a semisimple Hamiltonian matrix onto `{0, ±3}`. -/

namespace ConleyZehnder

open Matrix Polynomial ComplexConjugate

variable {n : ℕ}

/-! ### Complex spectrum of real matrices -/

/-- Complexification of real matrices. -/
noncomputable abbrev cx : Mat n →ₐ[ℝ] Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  (Algebra.ofId ℝ ℂ).mapMatrix

lemma cx_injective : Function.Injective (cx (n := n)) := fun A B h => by
  ext i j
  have := congrFun (congrFun h i) j
  simpa [AlgHom.mapMatrix_apply] using this

lemma det_cx (A : Mat n) : (cx A).det = (A.det : ℂ) :=
  (RingHom.map_det Complex.ofRealHom A).symm

lemma det_ne_of_spec {A : Mat n} (h : (1 : ℂ) ∉ spectrum ℂ (cx A)) : (1 - A).det ≠ 0 := by
  rw [spectrum.mem_iff, not_not, map_one, Matrix.isUnit_iff_isUnit_det, ← map_one cx, ← map_sub,
    det_cx] at h
  intro h0
  rw [h0] at h
  simp at h

lemma one_not_mem_spec {A : Mat n} (h : (1 - A).det ≠ 0) : (1 : ℂ) ∉ spectrum ℂ (cx A) := by
  rw [spectrum.mem_iff, not_not, map_one, Matrix.isUnit_iff_isUnit_det, ← map_one cx, ← map_sub,
    det_cx]
  exact isUnit_iff_ne_zero.2 (by exact_mod_cast h)

lemma spec_aeval (hn : 0 < n) (A : Mat n) (P : ℝ[X]) :
    spectrum ℂ (cx (aeval A P)) = (fun z => aeval z P) '' spectrum ℂ (cx A) := by
  haveI : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, hn⟩⟩
  have hne : (spectrum ℂ (cx A)).Nonempty :=
    spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ (cx A)
  rw [← aeval_algHom_apply, ← aeval_map_algebraMap ℂ,
    spectrum.map_polynomial_aeval_of_nonempty _ _ hne]
  congr 1
  funext z
  rw [eval_map_algebraMap]

lemma isNilpotent_of_spec {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ)
    (h : spectrum ℂ B ⊆ {0}) : IsNilpotent B := by
  have hroots : ∀ z ∈ B.charpoly.roots, z = 0 := fun z hz =>
    h (Matrix.mem_spectrum_iff_isRoot_charpoly.2 ((mem_roots (charpoly_monic B).ne_zero).1 hz))
  have hrep := Multiset.eq_replicate_of_mem hroots
  have hcard : B.charpoly.roots.card = Fintype.card ι := by
    rw [IsAlgClosed.card_roots_eq_natDegree, charpoly_natDegree_eq_dim]
  have hcp : B.charpoly = X ^ Fintype.card ι := by
    rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq (charpoly_monic B)
      IsAlgClosed.card_roots_eq_natDegree, hrep, hcard]
    simp
  refine ⟨Fintype.card ι, ?_⟩
  have := aeval_self_charpoly B
  rwa [hcp, map_pow, aeval_X] at this

/-! ### The target values -/

/-- `3` on real numbers `> 1`, `-3` on real numbers `< -1`, `0` elsewhere. -/
noncomputable def targ (z : ℂ) : ℂ :=
  if z.im = 0 ∧ 1 < z.re then 3 else if z.im = 0 ∧ z.re < -1 then -3 else 0

lemma targ_neg (z : ℂ) : targ (-z) = -targ z := by
  unfold targ
  simp only [Complex.neg_im, Complex.neg_re, neg_eq_zero]
  by_cases h0 : z.im = 0
  · simp only [h0, true_and]
    by_cases h1 : 1 < z.re
    · rw [if_neg (by linarith), if_pos (by linarith), if_pos h1]
    · by_cases h2 : z.re < -1
      · rw [if_pos (by linarith), if_neg h1, if_pos h2, neg_neg]
      · rw [if_neg (by linarith), if_neg (by linarith), if_neg h1, if_neg h2, neg_zero]
  · simp [h0]

lemma targ_conj (z : ℂ) : targ (conj z) = targ z := by
  simp [targ, Complex.conj_re, Complex.conj_im]

lemma conj_targ (z : ℂ) : conj (targ z) = targ z := by
  unfold targ; split_ifs <;> first | exact map_ofNat _ 3 | (rw [map_neg, map_ofNat]) | simp

lemma targ_cube (z : ℂ) : targ z ^ 3 - 9 * targ z = 0 := by
  unfold targ; split_ifs <;> norm_num

lemma key_ne {z : ℂ} (hz : z ≠ 1) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (1 - (c : ℂ)) * z + c * targ z ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  unfold targ at hre him
  split_ifs at hre him with h1 h2
  · simp [Complex.mul_re, h1.1] at hre
    nlinarith [mul_nonneg (sub_nonneg.2 hc1) (sub_nonneg.2 h1.2.le)]
  · simp [Complex.mul_re, h2.1] at hre
    nlinarith [mul_nonneg (sub_nonneg.2 hc1) (by linarith [h2.2] : (0 : ℝ) ≤ -z.re)]
  · simp [Complex.mul_re, Complex.mul_im] at hre him
    by_cases h0 : z.im = 0
    · simp only [h0, true_and, not_lt] at h1 h2
      have hne : z.re ≠ 1 := fun h' => hz (Complex.ext (by simpa using h') (by simpa using h0))
      have hlt : z.re < 1 := lt_of_le_of_ne h1 hne
      nlinarith [mul_nonneg hc0 (by linarith : (0 : ℝ) ≤ 1 - z.re)]
    · have hc : 1 - c = 0 := by
        rcases him with h' | h'
        · exact h'
        · exact absurd h' h0
      rw [hc] at hre
      simp at hre

/-! ### An odd real interpolating polynomial -/

lemma exists_odd_interp (s₀ : Finset ℂ) :
    ∃ g : ℝ[X], g.comp (-X) = -g ∧ ∀ z ∈ s₀, aeval z g = targ z := by
  set s : Finset ℂ := s₀ ∪ s₀.image conj ∪ s₀.image (fun z => -z) ∪
    s₀.image (fun z => -conj z) with hs
  set G : ℂ[X] := Lagrange.interpolate s id targ with hG
  have hGv : ∀ z ∈ s, eval z G = targ z := fun z hz =>
    Lagrange.eval_interpolate_at_node targ (Set.injOn_id _) hz
  set gr : ℝ[X] := ∑ i ∈ Finset.range (G.natDegree + 1), C (G.coeff i).re * X ^ i with hgr
  have hgr_eval : ∀ w : ℂ, aeval w gr = (eval w G + conj (eval (conj w) G)) / 2 := by
    intro w
    rw [hgr, eval_eq_sum_range, eval_eq_sum_range, map_sum, map_sum, ← Finset.sum_add_distrib,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, aeval_C, map_pow, aeval_X, map_mul, map_pow, Complex.conj_conj,
      Complex.coe_algebraMap, Complex.re_eq_add_conj]
    ring
  set g : ℝ[X] := C (1 / 2 : ℝ) * (gr - gr.comp (-X)) with hg
  refine ⟨g, ?_, ?_⟩
  · rw [hg, mul_comp, C_comp, sub_comp, comp_assoc, neg_comp, X_comp, neg_neg, comp_X]
    ring
  · intro z hz
    have hz1 : z ∈ s := by simp [hs, hz]
    have hz2 : conj z ∈ s := by
      simp only [hs, Finset.mem_union, Finset.mem_image]; left; left; right; exact ⟨z, hz, rfl⟩
    have hz3 : -z ∈ s := by
      simp only [hs, Finset.mem_union, Finset.mem_image]; left; right; exact ⟨z, hz, rfl⟩
    have hz4 : conj (-z) ∈ s := by
      simp only [hs, Finset.mem_union, Finset.mem_image, map_neg]; right; exact ⟨z, hz, rfl⟩
    have e1 : aeval z gr = targ z := by
      rw [hgr_eval, hGv z hz1, hGv _ hz2, targ_conj, conj_targ]; ring
    have e2 : aeval (-z) gr = -targ z := by
      rw [hgr_eval, hGv _ hz3, hGv _ hz4, targ_conj, conj_targ, targ_neg]; ring
    rw [hg, map_mul, aeval_C, map_sub, aeval_comp, map_neg, aeval_X, e1, e2]
    simp
    ring

/-! ### The squash -/

theorem squash (hn : 0 < n) (S : Mat n)
    (hss : Module.End.IsSemisimple (Matrix.toLinAlgEquiv' S)) (hS : S ∈ HamStar n) :
    ∃ Y : Mat n, IsHam Y ∧ Y * Y * Y = (9 : ℝ) • Y ∧ JoinedIn (HamStar n) S Y := by
  set s₀ : Finset ℂ := (cx S).charpoly.roots.toFinset
  have hmem : ∀ z ∈ spectrum ℂ (cx S), z ∈ s₀ := fun z hz => by
    rw [Multiset.mem_toFinset, mem_roots (charpoly_monic _).ne_zero]
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.1 hz
  obtain ⟨g, hodd, hval⟩ := exists_odd_interp s₀
  set Y := aeval S g with hYdef
  have hYham : IsHam Y := isHam_aeval_odd hS.1 hodd
  have h1S := one_not_mem_spec hS.2
  refine ⟨Y, hYham, ?_, ?_⟩
  · -- `W = Y³ - 9Y` is semisimple and nilpotent
    set P : ℝ[X] := g ^ 3 - C 9 * g
    have hW : aeval S P = Y * Y * Y - (9 : ℝ) • Y := by
      simp only [P, map_sub, map_mul, map_pow, aeval_C, pow_three, Algebra.smul_def,
        Matrix.mul_assoc]
      rfl
    have hnil : IsNilpotent (aeval S P) := by
      have hc : IsNilpotent (cx (aeval S P)) := by
        apply isNilpotent_of_spec
        rw [spec_aeval hn]
        rintro _ ⟨z, hz, rfl⟩
        simp only [Set.mem_singleton_iff, P, map_sub, map_mul, map_pow, aeval_C,
          hval z (hmem z hz)]
        simpa using targ_cube z
      obtain ⟨k, hk⟩ := hc
      exact ⟨k, cx_injective (by rw [map_pow, hk, map_zero])⟩
    have hsP : Module.End.IsSemisimple (Matrix.toLinAlgEquiv' (aeval S P)) := by
      rw [← aeval_algHom_apply]; exact hss.aeval P
    have h0 := Module.End.eq_zero_of_isNilpotent_isSemisimple (hnil.map Matrix.toLinAlgEquiv') hsP
    have : aeval S P = 0 := Matrix.toLinAlgEquiv'.injective (by rw [h0, map_zero])
    rw [hW] at this
    exact sub_eq_zero.1 this
  · have hmemc : ∀ c ∈ Set.Icc (0 : ℝ) 1, (1 - c) • S + c • Y ∈ HamStar n := by
      intro c hc
      refine ⟨((show IsHam S from hS.1).smul _).add (hYham.smul _), ?_⟩
      apply det_ne_of_spec
      have e : (1 - c) • S + c • Y = aeval S (C (1 - c) * X + C c * g) := by
        simp [hYdef, Algebra.smul_def]
      rw [e, spec_aeval hn]
      rintro ⟨z, hz, hz1⟩
      have hz1' : z ≠ 1 := fun h => h1S (h ▸ hz)
      apply key_ne hz1' hc.1 hc.2
      convert hz1 using 1
      simp only [map_add, map_mul, aeval_C, aeval_X, hval z (hmem z hz), Complex.coe_algebraMap,
        Complex.ofReal_sub, Complex.ofReal_one]
    have hJ := ((convex_Icc (0 : ℝ) 1).isPathConnected (by simp)).joinedIn 0 (by simp) 1 (by simp)
    have := (hJ.map (f := fun c : ℝ => (1 - c) • S + c • Y) (by fun_prop)).mono
      (by rintro _ ⟨c, hc, rfl⟩; exact hmemc c hc)
    simpa using this

/-- Every Hamiltonian matrix without eigenvalue `1` is joined inside `HamStar` to a Hamiltonian
`Y` with `Y³ = 9Y`. -/
theorem hamStar_joined_cube (X : Mat n) (hX : X ∈ HamStar n) :
    ∃ Y : Mat n, IsHam Y ∧ Y * Y * Y = (9 : ℝ) • Y ∧ JoinedIn (HamStar n) X Y := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨X, hX.1, ?_, JoinedIn.refl hX⟩
    ext i; rcases i with i | i <;> exact i.elim0
  obtain ⟨S, hss, hS, hXS⟩ := exists_semisimple_part X hX
  obtain ⟨Y, h1, h2, hSY⟩ := squash hn S hss hS
  exact ⟨Y, h1, h2, hXS.trans hSY⟩

end ConleyZehnder

open ConleyZehnder

open Matrix

theorem solution {n : ℕ} (X : Mat n) (hX : X * J₀ n + J₀ n * Xᵀ = 0)
    (h1 : (1 - X).det ≠ 0) :
    ∃ Y : Mat n, Y * J₀ n + J₀ n * Yᵀ = 0 ∧ Y * Y * Y = (9 : ℝ) • Y ∧
      JoinedIn {Z : Mat n | Z * J₀ n + J₀ n * Zᵀ = 0 ∧ (1 - Z).det ≠ 0} X Y :=
  by obtain ⟨Y, a, b, c⟩ := hamStar_joined_cube X ⟨hX, h1⟩; exact ⟨Y, a, b, c⟩
