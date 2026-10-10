-- Prove2me | solution 1 for ConleyZehnder.hamiltonian_cube_joinedIn_normal
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T20:25:00.306522+00:00
-- url     : https://prove2.me/submissions/752df2d1-7e2f-4377-8d25-101c65fa16a5

import Definitions.Def_ConleyZehnder_Setting
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Connected



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

/-! A Hamiltonian `Y` with `Y³ = 9Y` is `Z_{3·1}(e, f)` for a symplectic frame `(e, f)`. -/

namespace ConleyZehnder

open Matrix Module

variable {n : ℕ}

section Frame

variable (Y : Mat n)

/-- `ker(Y - c)`. -/
noncomputable def eig (c : ℝ) : Submodule ℝ (Vec n) := LinearMap.ker (Matrix.toLin' (Y - c • 1))

variable {Y}

lemma mem_eig {c : ℝ} {v : Vec n} : v ∈ eig Y c ↔ Y *ᵥ v = c • v := by
  rw [eig, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, sub_eq_zero]

variable (hY : IsHam Y) (h3 : Y * Y * Y = (9 : ℝ) • Y)
include hY h3

lemma cube_mulVec (v : Vec n) : Y *ᵥ (Y *ᵥ (Y *ᵥ v)) = (9 : ℝ) • (Y *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h3, Matrix.smul_mulVec]

/-- The three spectral components of `v`. -/
lemma decomp (v : Vec n) : ∃ a ∈ eig Y 3, ∃ b ∈ eig Y (-3), ∃ c ∈ eig Y 0, v = a + b + c := by
  have hc := cube_mulVec hY h3 v
  set w1 := Y *ᵥ v
  set w2 := Y *ᵥ w1
  refine ⟨(1 / 18 : ℝ) • (w2 + (3 : ℝ) • w1), ?_, (1 / 18 : ℝ) • (w2 - (3 : ℝ) • w1), ?_,
    v - (1 / 9 : ℝ) • w2, ?_, by module⟩
  · rw [mem_eig]
    simp only [Matrix.mulVec_smul, Matrix.mulVec_add, hc]
    module
  · rw [mem_eig]
    simp only [Matrix.mulVec_smul, Matrix.mulVec_sub, hc]
    module
  · rw [mem_eig]
    simp only [Matrix.mulVec_smul, Matrix.mulVec_sub, hc]
    module

omit h3 in
lemma iso {c d : ℝ} (hcd : c + d ≠ 0) {u v : Vec n} (hu : u ∈ eig Y c) (hv : v ∈ eig Y d) :
    sformL n u v = 0 := by
  have h := hY.sform u v
  rw [mem_eig.1 hu, mem_eig.1 hv, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul,
    smul_eq_mul, ← add_mul] at h
  exact (mul_eq_zero.1 h).resolve_left hcd

/-- `E₃` pairs nondegenerately with `E₋₃`. -/
lemma nd3 {u : Vec n} (hu : u ∈ eig Y 3) (h : ∀ w ∈ eig Y (-3), sformL n u w = 0) : u = 0 := by
  apply sformL_nondeg
  intro v
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := decomp hY h3 v
  rw [map_add, map_add, iso hY (by norm_num) hu ha, h b hb, iso hY (by norm_num) hu hc]
  simp

lemma ndm {w : Vec n} (hw : w ∈ eig Y (-3)) (h : ∀ u ∈ eig Y 3, sformL n u w = 0) : w = 0 := by
  apply sformL_nondeg
  intro v
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := decomp hY h3 v
  rw [map_add, map_add, sformL_skew w a, h a ha, iso hY (by norm_num) hw hb,
    iso hY (by norm_num) hw hc]
  simp

lemma finrank_eig_eq : finrank ℝ (eig Y 3) = finrank ℝ (eig Y (-3)) := by
  apply le_antisymm
  · have hinj : Function.Injective ((sformL n).domRestrict₁₂ (eig Y 3) (eig Y (-3))) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro u hu
      ext1
      exact nd3 hY h3 u.2 fun w hw => by
        simpa [LinearMap.domRestrict₁₂_apply] using LinearMap.congr_fun hu ⟨w, hw⟩
    have := LinearMap.finrank_le_finrank_of_injective hinj
    rwa [Subspace.dual_finrank_eq] at this
  · have hinj : Function.Injective
        ((sformL n).flip.domRestrict₁₂ (eig Y (-3)) (eig Y 3)) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro w hw
      ext1
      exact ndm hY h3 w.2 fun u hu => by
        simpa [LinearMap.domRestrict₁₂_apply] using LinearMap.congr_fun hw ⟨u, hu⟩
    have := LinearMap.finrank_le_finrank_of_injective hinj
    rwa [Subspace.dual_finrank_eq] at this

/-- The normal form. -/
theorem exists_frame : ∃ m r : ℕ, r ≤ 1 ∧ ∃ e f : (Fin m ⊕ Fin m) ⊕ Fin r → Vec n,
    IsFrame e f ∧ Y = Zmat ((3 : ℝ) • (1 : Matrix _ _ ℝ)) e f := by
  set k := finrank ℝ (eig Y 3)
  refine ⟨k / 2, k % 2, Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num)), ?_⟩
  set κ := (Fin (k / 2) ⊕ Fin (k / 2)) ⊕ Fin (k % 2)
  have hcard : Fintype.card κ = k := by simp [κ]; omega
  let bE : Basis κ ℝ (eig Y 3) :=
    (Module.finBasis ℝ (eig Y 3)).reindex (Fintype.equivFinOfCardEq hcard).symm
  let e : κ → Vec n := fun i => (bE i : Vec n)
  have he : ∀ i, e i ∈ eig Y 3 := fun i => (bE i).2
  -- the pairing map `Em → ℝ^κ`
  let Φ : eig Y (-3) →ₗ[ℝ] κ → ℝ :=
    LinearMap.pi fun i => (sformL n (e i)).comp (eig Y (-3)).subtype
  have hΦ : ∀ w i, Φ w i = sformL n (e i) w := fun _ _ => rfl
  -- every `u ∈ E₃` is a combination of the `e i`
  have hspan : ∀ u (hu : u ∈ eig Y 3), u = ∑ i, bE.repr ⟨u, hu⟩ i • e i := by
    intro u hu
    have h2 := congrArg Subtype.val (bE.sum_repr ⟨u, hu⟩)
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul] at h2
    exact h2.symm
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    ext1
    refine ndm hY h3 w.2 fun u hu => ?_
    rw [hspan u hu, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, LinearMap.smul_apply, ← hΦ, hw]
    simp
  have hΦsurj : Function.Surjective Φ := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hΦinj
    rw [Module.finrank_fintype_fun_eq_card, hcard, ← finrank_eig_eq hY h3]
  let fE : κ → eig Y (-3) := fun j => Classical.choose (hΦsurj (Pi.single j 1))
  have hfE : ∀ j, Φ (fE j) = Pi.single j 1 := fun j => Classical.choose_spec (hΦsurj _)
  let f : κ → Vec n := fun j => (fE j : Vec n)
  have hf : ∀ j, f j ∈ eig Y (-3) := fun j => (fE j).2
  have hef : ∀ i j, sformL n (e i) (f j) = if i = j then 1 else 0 := by
    intro i j
    have := congrFun (hfE j) i
    rw [hΦ] at this
    rw [this, Pi.single_apply]
  refine ⟨e, f, ⟨hef, fun i j => iso hY (by norm_num) (he i) (he j),
    fun i j => iso hY (by norm_num) (hf i) (hf j)⟩, ?_⟩
  -- identify `Y` with `Z_{3·1}(e, f)` on each spectral component
  have hZ : ∀ v, Zmat ((3 : ℝ) • (1 : Matrix κ κ ℝ)) e f *ᵥ v
      = (3 : ℝ) • ((∑ i, sformL n v (f i) • e i) + ∑ i, sformL n v (e i) • f i) := by
    intro v
    rw [Zmat_mulVec, smul_add, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      ite_smul, zero_smul]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), smul_add]
  -- components
  have hA : ∀ a (ha : a ∈ eig Y 3), a = ∑ i, sformL n a (f i) • e i := by
    intro a ha
    have hc : ∀ i, sformL n a (f i) = bE.repr ⟨a, ha⟩ i := by
      intro i
      conv_lhs => rw [hspan a ha]
      rw [map_sum, LinearMap.sum_apply]
      simp only [map_smul, LinearMap.smul_apply, hef, smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    simp_rw [hc]
    exact hspan a ha
  have hB : ∀ b ∈ eig Y (-3), b = -∑ i, sformL n b (e i) • f i := by
    intro b hb
    have key : (⟨b, hb⟩ : eig Y (-3)) = ∑ j, sformL n (e j) b • fE j := by
      apply hΦinj
      rw [map_sum]
      funext i
      simp only [map_smul, Finset.sum_apply, Pi.smul_apply, hfE, Pi.single_apply, smul_eq_mul,
        mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
      rfl
    have := congrArg Subtype.val key
    have hb' : b = ∑ j, sformL n (e j) b • f j := by simpa [f] using this
    simp only [sformL_skew b, neg_smul, Finset.sum_neg_distrib, neg_neg]
    exact hb'
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hZ]
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := decomp hY h3 v
  have hfa : ∀ i, sformL n (a + b + c) (f i) = sformL n a (f i) := by
    intro i
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      iso hY (by norm_num) hb (hf i), sformL_skew c, iso hY (by norm_num) (hf i) hc]
    simp
  have hea : ∀ i, sformL n (a + b + c) (e i) = sformL n b (e i) := by
    intro i
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      iso hY (by norm_num) ha (he i), sformL_skew c, iso hY (by norm_num) (he i) hc]
    simp
  simp only [hfa, hea]
  rw [← hA a ha, ← neg_neg (∑ i, sformL n b (e i) • f i), ← hB b hb]
  rw [Matrix.mulVec_add, Matrix.mulVec_add, mem_eig.1 ha, mem_eig.1 hb, mem_eig.1 hc]
  module

end Frame

end ConleyZehnder

/-! A Hamiltonian `Y` with `Y³ = 9Y` is joined inside `HamStar` to `0` or to `Yminus`. -/

namespace ConleyZehnder

open Matrix

variable {n : ℕ}

/-! ### Matrices `a + bJ` -/

lemma det_smul_one_add_smul_J_ne_zero (m : ℕ) {c d : ℝ} (h : c ^ 2 + d ^ 2 ≠ 0) :
    (c • (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) + d • J (Fin m) ℝ).det ≠ 0 := by
  have hJJ : J (Fin m) ℝ * J (Fin m) ℝ = -1 := J_squared _ _
  have hprod : (c • (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) + d • J (Fin m) ℝ) *
      (c • 1 - d • J (Fin m) ℝ) = (c ^ 2 + d ^ 2) • (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) := by
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, hJJ]
    module
  intro h0
  have := congrArg Matrix.det hprod
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ h this.symm

/-- `M(a, b) = (a + b J) ⊕ 3`. -/
noncomputable def Mab (m r : ℕ) (p : ℝ × ℝ) :
    Matrix ((Fin m ⊕ Fin m) ⊕ Fin r) ((Fin m ⊕ Fin m) ⊕ Fin r) ℝ :=
  fromBlocks (p.1 • 1 + p.2 • J (Fin m) ℝ) 0 0 ((3 : ℝ) • 1)

lemma continuous_Mab (m r : ℕ) : Continuous (Mab m r) := by
  unfold Mab
  exact ((continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)).matrix_fromBlocks
    continuous_const continuous_const continuous_const

/-- No eigenvalue `±1`. -/
def GoodM (ι : Type*) [Fintype ι] [DecidableEq ι] : Set (Matrix ι ι ℝ) :=
  {M | (1 - M).det ≠ 0 ∧ (1 + M).det ≠ 0}

/-- The parameters `(a, b)` with `a ± i b ≠ ±1`. -/
def goodR : Set (ℝ × ℝ) := {p | (1 - p.1) ^ 2 + p.2 ^ 2 ≠ 0 ∧ (1 + p.1) ^ 2 + p.2 ^ 2 ≠ 0}

lemma Mab_good (m r : ℕ) {p : ℝ × ℝ} (hp : p ∈ goodR) : Mab m r p ∈ GoodM _ := by
  have e1 : 1 - Mab m r p =
      fromBlocks ((1 - p.1) • 1 + (-p.2) • J (Fin m) ℝ) 0 0 ((-2 : ℝ) • 1) := by
    rw [Mab, ← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
    congr 1
    · module
    · simp
    · simp
    · module
  have e2 : 1 + Mab m r p =
      fromBlocks ((1 + p.1) • 1 + p.2 • J (Fin m) ℝ) 0 0 ((4 : ℝ) • 1) := by
    rw [Mab, ← fromBlocks_one, fromBlocks_add]
    congr 1
    · module
    · simp
    · simp
    · module
  refine ⟨?_, ?_⟩
  · rw [e1, det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_one, mul_one]
    refine mul_ne_zero (det_smul_one_add_smul_J_ne_zero m ?_) (pow_ne_zero _ (by norm_num))
    rw [neg_sq]; exact hp.1
  · rw [e2, det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_one, mul_one]
    exact mul_ne_zero (det_smul_one_add_smul_J_ne_zero m hp.2) (pow_ne_zero _ (by norm_num))

lemma joined_goodR : JoinedIn goodR ((3 : ℝ), (0 : ℝ)) (0, 0) := by
  have hC : ∀ C : Set (ℝ × ℝ), Convex ℝ C → C ⊆ goodR → ∀ x ∈ C, ∀ y ∈ C, JoinedIn goodR x y :=
    fun C hc hs x hx y hy => ((hc.isPathConnected ⟨x, hx⟩).joinedIn x hx y hy).mono hs
  have c1 : Convex ℝ (Prod.fst ⁻¹' Set.Ioi (2 : ℝ) : Set (ℝ × ℝ)) :=
    (convex_Ioi 2).linear_preimage (LinearMap.fst ℝ ℝ ℝ)
  have c2 : Convex ℝ (Prod.snd ⁻¹' Set.Ioi (0 : ℝ) : Set (ℝ × ℝ)) :=
    (convex_Ioi 0).linear_preimage (LinearMap.snd ℝ ℝ ℝ)
  have c3 : Convex ℝ (Prod.fst ⁻¹' Set.Ioo (-1 / 2 : ℝ) (1 / 2) : Set (ℝ × ℝ)) :=
    (convex_Ioo _ _).linear_preimage (LinearMap.fst ℝ ℝ ℝ)
  have s1 : (Prod.fst ⁻¹' Set.Ioi (2 : ℝ) : Set (ℝ × ℝ)) ⊆ goodR := by
    rintro ⟨a, b⟩ (h : 2 < a)
    exact ⟨ne_of_gt (by nlinarith [sq_nonneg b]), ne_of_gt (by nlinarith [sq_nonneg b])⟩
  have s2 : (Prod.snd ⁻¹' Set.Ioi (0 : ℝ) : Set (ℝ × ℝ)) ⊆ goodR := by
    rintro ⟨a, b⟩ (h : 0 < b)
    exact ⟨ne_of_gt (by positivity), ne_of_gt (by positivity)⟩
  have s3 : (Prod.fst ⁻¹' Set.Ioo (-1 / 2 : ℝ) (1 / 2) : Set (ℝ × ℝ)) ⊆ goodR := by
    rintro ⟨a, b⟩ ⟨h1, h2⟩
    exact ⟨ne_of_gt (by nlinarith [sq_nonneg b]), ne_of_gt (by nlinarith [sq_nonneg b])⟩
  refine (hC _ c1 s1 (3, 0) (by norm_num) (3, 3) (by norm_num)).trans
    ((hC _ c2 s2 (3, 3) (by norm_num) (0, 3) (by norm_num)).trans
      (hC _ c3 s3 (0, 3) (by norm_num) (0, 0) (by norm_num)))

lemma joined_Mab (m r : ℕ) :
    JoinedIn (GoodM _) ((3 : ℝ) • (1 : Matrix ((Fin m ⊕ Fin m) ⊕ Fin r) _ ℝ)) (Mab m r (0, 0)) := by
  have := (joined_goodR.map (continuous_Mab m r)).mono (by
    rintro _ ⟨p, hp, rfl⟩; exact Mab_good m r hp)
  have e : Mab m r (3, 0) = (3 : ℝ) • 1 := by
    rw [← fromBlocks_one, fromBlocks_smul]; simp [Mab]
  rwa [e] at this

lemma Zmat_Mab_r0 {m : ℕ} (e f : (Fin m ⊕ Fin m) ⊕ Fin 0 → Vec n) :
    Zmat (Mab m 0 (0, 0)) e f = 0 := by
  have : Mab m 0 (0, 0) = 0 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Mab]
      · exact j.elim0
    · exact i.elim0
  rw [this]; simp [Zmat]

lemma Zmat_Mab_r1 {m : ℕ} (e f : (Fin m ⊕ Fin m) ⊕ Fin 1 → Vec n) :
    Zmat (Mab m 1 (0, 0)) e f = (3 : ℝ) • Bop (e (Sum.inr 0)) (f (Sum.inr 0)) := by
  simp [Zmat, Mab, Fintype.sum_sum_type]

/-! ### The rank-one endpoint -/

lemma det_one_sub_three_Bop {e f : Vec n} (h : sformL n e f = 1) :
    (1 - (3 : ℝ) • Bop e f).det ≠ 0 := by
  have hF : IsFrame (fun _ : Fin 1 => e) (fun _ : Fin 1 => f) :=
    ⟨fun i j => by simp [h, Subsingleton.elim i j], fun _ _ => sformL_self e,
      fun _ _ => sformL_self f⟩
  have := hF.det_one_sub_Zmat (M := (3 : ℝ) • 1) (by simp [Matrix.det_unique]; norm_num)
    (by simp [Matrix.det_unique]; norm_num)
  have e1 : Zmat ((3 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) (fun _ => e) (fun _ => f)
      = (3 : ℝ) • Bop e f := by simp [Zmat]
  rwa [e1] at this

/-- `J₀ e / |e|²`, the dual partner of `e`. -/
noncomputable def gdual (e : Vec n) : Vec n := (e ⬝ᵥ e)⁻¹ • (J₀ n *ᵥ e)

lemma dot_self_ne_zero {e : Vec n} (he : e ≠ 0) : e ⬝ᵥ e ≠ 0 :=
  fun h => he (dotProduct_self_eq_zero.1 h)

lemma sform_gdual {e : Vec n} (he : e ≠ 0) : sformL n e (gdual e) = 1 := by
  rw [gdual, map_smul, sformL_J, smul_eq_mul, inv_mul_cancel₀ (dot_self_ne_zero he)]

lemma continuousOn_gdual : ContinuousOn (gdual (n := n)) {0}ᶜ := by
  have hd : Continuous fun e : Vec n => e ⬝ᵥ e := continuous_id.dotProduct continuous_id
  exact (hd.continuousOn.inv₀ fun e he => dot_self_ne_zero he).smul
    (continuous_const.matrix_mulVec continuous_id).continuousOn

/-- Pairs with `Ω₀(e, f) = 1`. -/
def pairSet (n : ℕ) : Set (Vec n × Vec n) := {p | sformL n p.1 p.2 = 1}

/-- The standard pair `(q₁, p₁)`. -/
noncomputable def qStd (hn : 0 < n) : Vec n := Pi.single (Sum.inl ⟨0, hn⟩) 1
noncomputable def pStd (hn : 0 < n) : Vec n := Pi.single (Sum.inr ⟨0, hn⟩) 1

lemma gdual_qStd (hn : 0 < n) : gdual (qStd hn) = pStd hn := by
  ext i
  rcases i with i | i <;>
    simp [gdual, qStd, pStd, Matrix.mulVec_single_one, Matrix.J, Pi.single_apply, Fin.ext_iff,
      Matrix.one_apply, eq_comm]

lemma qStd_ne_zero (hn : 0 < n) : qStd hn ≠ 0 := by
  intro h
  have := congrFun h (Sum.inl ⟨0, hn⟩)
  simp [qStd] at this

lemma joined_pairs (hn : 0 < n) {e f : Vec n} (h : sformL n e f = 1) :
    JoinedIn (pairSet n) (e, f) (qStd hn, pStd hn) := by
  have he : e ≠ 0 := by rintro rfl; simp at h
  have hA : JoinedIn (pairSet n) (e, f) (e, gdual e) := by
    have hc : Convex ℝ (sformL n e ⁻¹' {1}) := (convex_singleton 1).linear_preimage (sformL n e)
    have := (hc.isPathConnected ⟨f, h⟩).joinedIn f h (gdual e) (sform_gdual he)
    exact (this.map (f := fun g => (e, g)) (continuous_const.prodMk continuous_id)).mono
      (by rintro _ ⟨g, hg, rfl⟩; exact hg)
  have hrank : 1 < Module.rank ℝ (Vec n) := by
    rw [rank_fun']
    simp only [Fintype.card_sum, Fintype.card_fin]
    norm_cast
    omega
  have hB : JoinedIn (pairSet n) (e, gdual e) (qStd hn, gdual (qStd hn)) := by
    have := (isPathConnected_compl_singleton_of_one_lt_rank hrank 0).joinedIn e he (qStd hn)
      (qStd_ne_zero hn)
    exact (this.map_continuousOn (f := fun x => (x, gdual x))
      (continuousOn_id.prodMk continuousOn_gdual)).mono
      (by rintro _ ⟨x, hx, rfl⟩; exact sform_gdual hx)
  rw [gdual_qStd] at hB
  exact hA.trans hB

lemma Yminus_eq (hn : 0 < n) : Yminus n = (3 : ℝ) • Bop (qStd hn) (pStd hn) := by
  ext i k
  rcases i with i | i <;> rcases k with k | k <;>
    simp [Yminus, Bop, qStd, pStd, Matrix.J, vecMulVec, Pi.single_apply, Matrix.mulVec_single_one,
      Matrix.diagonal_apply, Fin.ext_iff, Matrix.one_apply] <;>
    split_ifs <;> simp_all

/-- Every Hamiltonian `Y` with `Y³ = 9Y` is joined inside `HamStar` to `0` or to `Yminus`. -/
theorem hamStar_joined_of_cube (Y : Mat n) (hY : IsHam Y) (h3 : Y * Y * Y = (9 : ℝ) • Y) :
    JoinedIn (HamStar n) Y 0 ∨ JoinedIn (HamStar n) Y (Yminus n) := by
  obtain ⟨m, r, hr, e, f, hF, rfl⟩ := exists_frame hY h3
  have hZ : JoinedIn (HamStar n) (Zmat ((3 : ℝ) • 1) e f) (Zmat (Mab m r (0, 0)) e f) :=
    ((joined_Mab m r).map (continuous_Zmat e f)).mono (by
      rintro _ ⟨M, hM, rfl⟩; exact ⟨Zmat_isHam M e f, hF.det_one_sub_Zmat hM.1 hM.2⟩)
  interval_cases r
  · left; rwa [Zmat_Mab_r0] at hZ
  · right
    rw [Zmat_Mab_r1] at hZ
    refine hZ.trans ?_
    have h1 : sformL n (e (Sum.inr 0)) (f (Sum.inr 0)) = 1 := by
      simpa using hF.ef (Sum.inr 0) (Sum.inr 0)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exfalso
      have : e (Sum.inr 0) = 0 := funext fun i => by rcases i with i | i <;> exact i.elim0
      rw [this] at h1; simp at h1
    rw [Yminus_eq hn]
    exact ((joined_pairs hn h1).map (f := fun p => (3 : ℝ) • Bop p.1 p.2)
      (continuous_Bop.const_smul (3 : ℝ))).mono (by
        rintro _ ⟨p, hp, rfl⟩; exact ⟨(Bop_isHam _ _).smul 3, det_one_sub_three_Bop hp⟩)

end ConleyZehnder

open ConleyZehnder

open Matrix

theorem solution {n : ℕ} (Y : Mat n) (hY : Y * J₀ n + J₀ n * Yᵀ = 0)
    (h3 : Y * Y * Y = (9 : ℝ) • Y) :
    JoinedIn {Z : Mat n | Z * J₀ n + J₀ n * Zᵀ = 0 ∧ (1 - Z).det ≠ 0} Y 0 ∨
      JoinedIn {Z : Mat n | Z * J₀ n + J₀ n * Zᵀ = 0 ∧ (1 - Z).det ≠ 0} Y
        (Matrix.diagonal (Sum.elim (fun j : Fin n => if j.val = 0 then (3 : ℝ) else 0)
          (fun j : Fin n => if j.val = 0 then (-3 : ℝ) else 0))) :=
  hamStar_joined_of_cube Y hY h3
