-- Prove2me | solution 1 for ConvexOptimization.single_constraint_quadratic_strong_duality
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-16T03:51:21.617426+00:00
-- url     : https://prove2.me/submissions/ab697b96-95ba-4aa7-8151-caf9158d2078

import Mathlib
import Definitions.Def_ConvexOptimization_quadraticForms
import Theorems.Thm_ConvexOptimization_field_of_values_psd_witness

open scoped RealInnerProductSpace ENNReal
open MeasureTheory
open Set

namespace ConvexOptimization

lemma trace_mul_smul_vecMulVec {n : Type*} [Fintype n]
    (M : Matrix n n ℝ) (r : ℝ) (x : n → ℝ) :
    (M * (r • Matrix.vecMulVec x x)).trace = r * (x ⬝ᵥ M.mulVec x) := by
  classical
  rw [Matrix.mul_smul, Matrix.trace_smul]
  simp only [smul_eq_mul]
  congr 1
  symm
  simp only [dotProduct, Matrix.mulVec, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.vecMulVec_apply]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma trace_mul_vecMulVec {n : Type*} [Fintype n]
    (M : Matrix n n ℝ) (x : n → ℝ) :
    (M * Matrix.vecMulVec x x).trace = x ⬝ᵥ M.mulVec x := by
  simpa using trace_mul_smul_vecMulVec M 1 x

lemma psd_nonneg_smul_vecMulVec {n : Type*} [Fintype n]
    (x : n → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (r • Matrix.vecMulVec x x).PosSemidef :=
  (Matrix.posSemidef_vecMulVec_self_star x).smul hr

lemma trace_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix κ κ ℝ) (e : ι ≃ κ) :
    (M.submatrix e e).trace = M.trace := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Equiv.sum_comp e (fun i => M i i)

lemma field_of_values_psd_witness_generic {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℝ) (hA : A.IsSymm) (hB : B.IsSymm)
    (X : Matrix ι ι ℝ) (hX : X.PosSemidef) :
    ∃ x : ι → ℝ,
      x ⬝ᵥ A.mulVec x = (A * X).trace ∧ x ⬝ᵥ B.mulVec x = (B * X).trace := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := Fintype.equivOfCardEq (by simp)
  have hAe : (A.submatrix e e).IsSymm := by
    ext i j
    simpa [Matrix.IsSymm, Matrix.transpose_apply] using
      congr_fun (congr_fun hA (e i)) (e j)
  have hBe : (B.submatrix e e).IsSymm := by
    ext i j
    simpa [Matrix.IsSymm, Matrix.transpose_apply] using
      congr_fun (congr_fun hB (e i)) (e j)
  have hXe : (X.submatrix e e).PosSemidef := hX.submatrix e
  obtain ⟨y, hyA, hyB⟩ := field_of_values_psd_witness
    (A.submatrix e e) (B.submatrix e e) hAe hBe (X.submatrix e e) hXe
  let x : ι → ℝ := y ∘ e.symm
  refine ⟨x, ?_, ?_⟩
  · rw [Matrix.submatrix_mul_equiv] at hyA
    rw [trace_submatrix_equiv] at hyA
    rw [Matrix.submatrix_mulVec_equiv] at hyA
    change (∑ i, y (e.symm i) * A.mulVec (y ∘ e.symm) i) = _
    rw [← Equiv.sum_comp e]
    simpa [dotProduct] using hyA
  · rw [Matrix.submatrix_mul_equiv] at hyB
    rw [trace_submatrix_equiv] at hyB
    rw [Matrix.submatrix_mulVec_equiv] at hyB
    change (∑ i, y (e.symm i) * B.mulVec (y ∘ e.symm) i) = _
    rw [← Equiv.sum_comp e]
    simpa [dotProduct] using hyB

lemma matrix_slemma {ι : Type*} [Fintype ι]
    (M₀ M₁ : Matrix ι ι ℝ) (hM₀ : M₀.IsSymm) (hM₁ : M₁.IsSymm)
    (xh : ι → ℝ) (hxh : xh ⬝ᵥ M₁.mulVec xh < 0)
    (himp : ∀ x : ι → ℝ, x ⬝ᵥ M₁.mulVec x ≤ 0 → 0 ≤ x ⬝ᵥ M₀.mulVec x) :
    ∃ lam : ℝ, 0 ≤ lam ∧ (M₀ + lam • M₁).PosSemidef := by
  let Q : (ι → ℝ) → EuclideanSpace ℝ (Fin 2) := fun x =>
    WithLp.toLp 2 ![x ⬝ᵥ M₁.mulVec x, x ⬝ᵥ M₀.mulVec x]
  let C : Set (EuclideanSpace ℝ (Fin 2)) := Set.range Q
  let D : Set (EuclideanSpace ℝ (Fin 2)) :=
    {p | p.ofLp 0 < 0 ∧ p.ofLp 1 < 0}
  have hCconv : Convex ℝ C := by
    intro p hp q hq a b ha hb hab
    rcases hp with ⟨x, rfl⟩
    rcases hq with ⟨y, rfl⟩
    let X := a • Matrix.vecMulVec x x + b • Matrix.vecMulVec y y
    have hX : X.PosSemidef :=
      (psd_nonneg_smul_vecMulVec x ha).add (psd_nonneg_smul_vecMulVec y hb)
    obtain ⟨z, hz1, hz0⟩ := field_of_values_psd_witness_generic M₁ M₀ hM₁ hM₀ X hX
    refine ⟨z, ?_⟩
    apply WithLp.ofLp_injective 2
    funext i
    fin_cases i
    · simp [Q, hz1, X, Matrix.mul_add, Matrix.trace_add,
        trace_mul_vecMulVec]
    · simp [Q, hz0, X, Matrix.mul_add, Matrix.trace_add,
        trace_mul_vecMulVec]
  have hDconv : Convex ℝ D := by
    intro p hp q hq a b ha hb hab
    constructor
    · change a * p.ofLp 0 + b * q.ofLp 0 < 0
      rcases ha.eq_or_lt with rfl | ha'
      · simpa using mul_neg_of_pos_of_neg (by linarith) hq.1
      · exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg ha' hp.1)
          (mul_nonpos_of_nonneg_of_nonpos hb hq.1.le)
    · change a * p.ofLp 1 + b * q.ofLp 1 < 0
      rcases ha.eq_or_lt with rfl | ha'
      · simpa using mul_neg_of_pos_of_neg (by linarith) hq.2
      · exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg ha' hp.2)
          (mul_nonpos_of_nonneg_of_nonpos hb hq.2.le)
  have hDopen : IsOpen D := by
    change IsOpen ({p : EuclideanSpace ℝ (Fin 2) | p.ofLp 0 < 0} ∩
      {p : EuclideanSpace ℝ (Fin 2) | p.ofLp 1 < 0})
    exact (isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0) continuous_const).inter
      (isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1) continuous_const)
  have hdisj : Disjoint D C := by
    rw [Set.disjoint_left]
    intro p hpD hpC
    rcases hpC with ⟨x, rfl⟩
    exact (not_lt_of_ge (himp x hpD.1.le)) hpD.2
  obtain ⟨f, u, hDu, hCu⟩ := geometric_hahn_banach_open hDconv hDopen hCconv hdisj
  have hu_le : u ≤ 0 := by
    have hzC : (0 : EuclideanSpace ℝ (Fin 2)) ∈ C := ⟨0, by simp [Q]⟩
    simpa using hCu 0 hzC
  have hu_ge : 0 ≤ u := by
    by_contra hu
    have hu' : u < 0 := lt_of_not_ge hu
    let d : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![-1, -1]
    have hdD : d ∈ D := by norm_num [D, d]
    have hfd : f d < u := hDu d hdD
    let r : ℝ := u / (2 * f d)
    have hfd0 : f d < 0 := hfd.trans hu'
    have hr : 0 < r := div_pos_of_neg_of_neg hu' (mul_neg_of_pos_of_neg (by norm_num) hfd0)
    have hrd : r • d ∈ D := by
      constructor <;> simp [D, d, hr]
    have hsep := hDu (r • d) hrd
    rw [map_smul, smul_eq_mul] at hsep
    dsimp [r] at hsep
    field_simp [hfd0.ne] at hsep
    linarith
  have hu0 : u = 0 := le_antisymm hu_le hu_ge
  let e0 : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 0]
  let e1 : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![0, 1]
  let alpha := f e0
  let beta := f e1
  have hfcoord (p : EuclideanSpace ℝ (Fin 2)) : f p = alpha * p.ofLp 0 + beta * p.ofLp 1 := by
    have hp : p = p.ofLp 0 • e0 + p.ofLp 1 • e1 := by
      apply WithLp.ofLp_injective 2
      funext i
      fin_cases i <;> simp [e0, e1]
    conv_lhs => rw [hp, map_add, map_smul, map_smul]
    simp [alpha, beta, e0, e1, smul_eq_mul]
    ring
  have ha : 0 ≤ alpha := by
    by_contra ha
    have ha' : alpha < 0 := lt_of_not_ge ha
    let r : ℝ := (|beta| + 1) / (-alpha)
    let d : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![-r, -1]
    have hr : 0 < r := div_pos (by positivity) (neg_pos.mpr ha')
    have hd : d ∈ D := by simp [D, d, hr]
    have h := hDu d hd
    rw [hu0, hfcoord] at h
    simp [d, r] at h
    field_simp [ha'.ne] at h
    have := le_abs_self beta
    linarith
  have hb : 0 ≤ beta := by
    by_contra hb
    have hb' : beta < 0 := lt_of_not_ge hb
    let r : ℝ := (|alpha| + 1) / (-beta)
    let d : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![-1, -r]
    have hr : 0 < r := div_pos (by positivity) (neg_pos.mpr hb')
    have hd : d ∈ D := by simp [D, d, hr]
    have h := hDu d hd
    rw [hu0, hfcoord] at h
    simp [d, r] at h
    field_simp [hb'.ne] at h
    have := le_abs_self alpha
    linarith
  have hbpos : 0 < beta := by
    rcases hb.eq_or_lt with hb0 | hbpos
    · have hbzero : beta = 0 := hb0.symm
      have hq : Q xh ∈ C := ⟨xh, rfl⟩
      have h := hCu (Q xh) hq
      rw [hu0, hfcoord] at h
      rw [hbzero] at h
      simp [Q] at h
      have hsum : 0 < alpha + beta := by
        let d : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![-1, -1]
        have hd : d ∈ D := by norm_num [D, d]
        have hd' := hDu d hd
        rw [hu0, hfcoord] at hd'
        simp [d] at hd'
        linarith
      have hap : 0 < alpha := by rw [hbzero] at hsum; simpa using hsum
      have hneg := mul_neg_of_pos_of_neg hap hxh
      linarith
    · exact hbpos
  refine ⟨alpha / beta, div_nonneg ha hb, ?_⟩
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · have h0 : M₀.IsHermitian := by simpa [Matrix.IsHermitian, Matrix.conjTranspose, hM₀]
    have h1 : M₁.IsHermitian := by simpa [Matrix.IsHermitian, Matrix.conjTranspose, hM₁]
    exact h0.add (h1.smul (star_trivial _))
  · intro x
    have hq : Q x ∈ C := ⟨x, rfl⟩
    have h := hCu (Q x) hq
    rw [hu0, hfcoord] at h
    simp [Q] at h
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul]
    simp only [star_trivial, smul_eq_mul]
    calc
      0 ≤ (alpha * (x ⬝ᵥ M₁.mulVec x) + beta * (x ⬝ᵥ M₀.mulVec x)) / beta := div_nonneg h hb
      _ = x ⬝ᵥ M₀.mulVec x + alpha / beta * (x ⬝ᵥ M₁.mulVec x) := by field_simp; ring


lemma symQuadBlock_isSymm {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ)
    (hF : F.IsSymm) (g : Fin n → ℝ) (h : ℝ) :
    (symQuadBlock F g h).IsSymm := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [symQuadBlock, Matrix.fromBlocks, Matrix.IsSymm, Matrix.transpose_apply]
  exact congr_fun (congr_fun hF i) j

lemma symQuadBlock_eval {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ)
    (g : Fin n → ℝ) (h : ℝ) (z : Fin n ⊕ Unit → ℝ) :
    z ⬝ᵥ (symQuadBlock F g h).mulVec z =
      (fun i => z (Sum.inl i)) ⬝ᵥ F.mulVec (fun i => z (Sum.inl i)) +
      2 * z (Sum.inr ()) * (g ⬝ᵥ fun i => z (Sum.inl i)) + h * z (Sum.inr ()) ^ 2 := by
  classical
  simp only [dotProduct, Matrix.mulVec, symQuadBlock]
  simp_rw [Fintype.sum_sum_type]
  simp only [Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
    Fintype.sum_unique, Finset.mul_sum]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  simp_rw [Finset.mul_sum]
  have hc : (∑ x, z (Sum.inl x) * (g x * z (Sum.inr ()))) =
      ∑ x, z (Sum.inr ()) * (g x * z (Sum.inl x)) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hc]
  ring_nf
  rw [Finset.sum_mul]

lemma symQuadBlock_lift_eval {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ)
    (g : Fin n → ℝ) (h : ℝ) (x : Fin n → ℝ) :
    (Sum.elim x (fun _ => 1)) ⬝ᵥ (symQuadBlock F g h).mulVec (Sum.elim x (fun _ => 1)) =
      quadForm F g h x := by
  rw [symQuadBlock_eval]
  simp [quadForm]


lemma quadForm_line {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    (g : Fin n → ℝ) (h : ℝ) (x₀ x : Fin n → ℝ) (s : ℝ) :
    quadForm F g h (x₀ + s • x) =
      s ^ 2 * (x ⬝ᵥ F.mulVec x) +
      2 * s * (x ⬝ᵥ F.mulVec x₀ + g ⬝ᵥ x) + quadForm F g h x₀ := by
  have hc : x₀ ⬝ᵥ F.mulVec x = x ⬝ᵥ F.mulVec x₀ := by
    calc
      x₀ ⬝ᵥ F.mulVec x = Matrix.vecMul x₀ F ⬝ᵥ x := Matrix.dotProduct_mulVec x₀ F x
      _ = F.transpose.mulVec x₀ ⬝ᵥ x := by
        rw [show Matrix.vecMul x₀ F = F.transpose.mulVec x₀ by
          simpa using Matrix.vecMul_transpose F.transpose x₀]
      _ = F.mulVec x₀ ⬝ᵥ x := by rw [hF]
      _ = x ⬝ᵥ F.mulVec x₀ := dotProduct_comm _ _
  simp only [quadForm, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
    dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [hc]
  ring

lemma symQuadBlock_eval_scale {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ)
    (g : Fin n → ℝ) (h : ℝ) (z : Fin n ⊕ Unit → ℝ)
    (ht : z (Sum.inr ()) ≠ 0) :
    z ⬝ᵥ (symQuadBlock F g h).mulVec z =
      z (Sum.inr ()) ^ 2 * quadForm F g h
        ((z (Sum.inr ()))⁻¹ • (fun i => z (Sum.inl i))) := by
  rw [symQuadBlock_eval]
  simp only [quadForm, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  field_simp


lemma affine_implication_homogeneous {n : ℕ}
    (A₀ A₁ : Matrix (Fin n) (Fin n) ℝ) (hA₀ : A₀.IsSymm) (hA₁ : A₁.IsSymm)
    (b₀ b₁ : Fin n → ℝ) (c₀ c₁ gamma : ℝ)
    (xh : Fin n → ℝ) (hxh : quadForm A₁ b₁ c₁ xh < 0)
    (himp : ∀ x, quadForm A₁ b₁ c₁ x ≤ 0 → gamma ≤ quadForm A₀ b₀ c₀ x) :
    ∀ z : Fin n ⊕ Unit → ℝ,
      z ⬝ᵥ (symQuadBlock A₁ b₁ c₁).mulVec z ≤ 0 →
      0 ≤ z ⬝ᵥ (symQuadBlock A₀ b₀ (c₀ - gamma)).mulVec z := by
  intro z hz1
  let x : Fin n → ℝ := fun i => z (Sum.inl i)
  let t : ℝ := z (Sum.inr ())
  by_cases ht : t = 0
  · have ha1 : x ⬝ᵥ A₁.mulVec x ≤ 0 := by
      rw [symQuadBlock_eval] at hz1
      simpa [x, t, ht] using hz1
    rw [symQuadBlock_eval]
    simp [t, ht]
    by_contra ha0
    have ha0' : x ⬝ᵥ A₀.mulVec x < 0 := lt_of_not_ge ha0
    let k1 : ℝ := x ⬝ᵥ A₁.mulVec xh + b₁ ⬝ᵥ x
    let sigma : ℝ := if k1 ≤ 0 then 1 else -1
    have hsigma : sigma = 1 ∨ sigma = -1 := by
      dsimp [sigma]
      by_cases hk : k1 ≤ 0
      · left; simp [hk]
      · right; simp [hk]
    have hsigma_sq : sigma ^ 2 = 1 := by
      rcases hsigma with hs | hs <;> rw [hs] <;> norm_num
    have hsigk1 : sigma * k1 ≤ 0 := by
      dsimp [sigma]
      split_ifs with hk
      · simpa using hk
      · have : 0 < k1 := lt_of_not_ge hk
        linarith
    let k0 : ℝ := x ⬝ᵥ A₀.mulVec xh + b₀ ⬝ᵥ x
    let d0 : ℝ := quadForm A₀ b₀ (c₀ - gamma) xh
    let P : ℝ := 2 * |k0| + |d0|
    let R : ℝ := 1 + P / (- (x ⬝ᵥ A₀.mulVec x))
    have hden : 0 < -(x ⬝ᵥ A₀.mulVec x) := neg_pos.mpr ha0'
    have hP : 0 ≤ P := by
      dsimp [P]
      nlinarith [abs_nonneg k0, abs_nonneg d0]
    have hR1 : 1 ≤ R := by
      dsimp [R]
      linarith [div_nonneg hP hden.le]
    have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR1
    have hRP : P < (-(x ⬝ᵥ A₀.mulVec x)) * R := by
      have heq : (-(x ⬝ᵥ A₀.mulVec x)) * R =
          (-(x ⬝ᵥ A₀.mulVec x)) + P := by
        dsimp [R]
        rw [mul_add, mul_one, mul_div_cancel₀ P (ne_of_gt hden)]
      rw [heq]
      linarith
    let s := sigma * R
    have hs2 : s ^ 2 = R ^ 2 := by dsimp [s]; rw [mul_pow, hsigma_sq, one_mul]
    have hq1 : quadForm A₁ b₁ c₁ (xh + s • x) < 0 := by
      rw [quadForm_line A₁ hA₁ b₁ c₁]
      change s ^ 2 * (x ⬝ᵥ A₁.mulVec x) + 2 * s * k1 + quadForm A₁ b₁ c₁ xh < 0
      have hs_nonneg : 0 ≤ s ^ 2 := sq_nonneg s
      have hlead : s ^ 2 * (x ⬝ᵥ A₁.mulVec x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs_nonneg ha1
      have hcross : s * k1 ≤ 0 := by
        dsimp [s]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hR.le hsigk1]
      nlinarith
    have hk0bound : sigma * k0 ≤ |k0| := by
      rcases hsigma with h | h <;> rw [h]
      · simpa using le_abs_self k0
      · simpa using neg_le_abs k0
    have hd0bound : d0 ≤ |d0| := le_abs_self d0
    have htail : 2 * s * k0 + d0 ≤ R * P := by
      have hcross0 : 2 * R * (sigma * k0) ≤ 2 * R * |k0| :=
        mul_le_mul_of_nonneg_left hk0bound (by positivity)
      have hd : d0 ≤ R * |d0| := by
        nlinarith [hd0bound, abs_nonneg d0,
          mul_le_mul_of_nonneg_right hR1 (abs_nonneg d0)]
      dsimp [s, P]
      nlinarith
    have hnegmain : (x ⬝ᵥ A₀.mulVec x) * R ^ 2 + R * P < 0 := by
      have := mul_lt_mul_of_pos_right hRP hR
      nlinarith
    have hq0 : quadForm A₀ b₀ (c₀ - gamma) (xh + s • x) < 0 := by
      rw [quadForm_line A₀ hA₀ b₀ (c₀ - gamma)]
      change s ^ 2 * (x ⬝ᵥ A₀.mulVec x) + 2 * s * k0 + d0 < 0
      rw [hs2]
      linarith
    have him := himp (xh + s • x) hq1.le
    have : 0 ≤ quadForm A₀ b₀ (c₀ - gamma) (xh + s • x) := by
      dsimp [quadForm] at him ⊢
      linarith
    exact (not_lt_of_ge this) hq0
  · have htpos : 0 < t ^ 2 := sq_pos_of_ne_zero ht
    rw [symQuadBlock_eval_scale A₁ b₁ c₁ z ht] at hz1
    have hq1 : quadForm A₁ b₁ c₁ (t⁻¹ • x) ≤ 0 := by
      dsimp [t, x] at hz1 ⊢
      nlinarith
    have hq0 := himp (t⁻¹ • x) hq1
    rw [symQuadBlock_eval_scale A₀ b₀ (c₀ - gamma) z ht]
    have : 0 ≤ quadForm A₀ b₀ (c₀ - gamma) (t⁻¹ • x) := by
      dsimp [quadForm] at hq0 ⊢
      linarith
    exact mul_nonneg (sq_nonneg _) this

end ConvexOptimization

open ConvexOptimization

theorem solution {nn : ℕ}
    (A₀ A₁ : Matrix (Fin nn) (Fin nn) ℝ) (hA₀ : A₀.IsSymm) (hA₁ : A₁.IsSymm)
    (b₀ b₁ : Fin nn → ℝ) (c₀ c₁ : ℝ)
    (xh : Fin nn → ℝ) (hxh : quadForm A₁ b₁ c₁ xh < 0) (gamma : ℝ) :
    (∀ x, quadForm A₁ b₁ c₁ x ≤ 0 → gamma ≤ quadForm A₀ b₀ c₀ x) ↔
      ∃ lam : ℝ, 0 ≤ lam ∧
        (symQuadBlock A₀ b₀ (c₀ - gamma) + lam • symQuadBlock A₁ b₁ c₁).PosSemidef := by
  constructor
  · intro himp
    apply matrix_slemma
        (symQuadBlock A₀ b₀ (c₀ - gamma)) (symQuadBlock A₁ b₁ c₁)
        (symQuadBlock_isSymm A₀ hA₀ b₀ (c₀ - gamma))
        (symQuadBlock_isSymm A₁ hA₁ b₁ c₁)
        (Sum.elim xh (fun _ => 1))
    · simpa [symQuadBlock_lift_eval] using hxh
    · exact affine_implication_homogeneous A₀ A₁ hA₀ hA₁ b₀ b₁ c₀ c₁ gamma xh hxh himp
  · rintro ⟨lam, hlam, hpsd⟩ x hx
    have hp := hpsd.dotProduct_mulVec_nonneg (Sum.elim x (fun _ => 1))
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
      smul_eq_mul] at hp
    change 0 ≤
      (Sum.elim x (fun _ => 1)) ⬝ᵥ
          (symQuadBlock A₀ b₀ (c₀ - gamma)).mulVec (Sum.elim x (fun _ => 1)) +
        lam * ((Sum.elim x (fun _ => 1)) ⬝ᵥ
          (symQuadBlock A₁ b₁ c₁).mulVec (Sum.elim x (fun _ => 1))) at hp
    rw [symQuadBlock_lift_eval, symQuadBlock_lift_eval] at hp
    dsimp [quadForm] at hp hx ⊢
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hlam hx]
