-- Prove2me | solution 1 for CaiCandesShen.GeneralConvex.optimality_conditions
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:11:37.638834+00:00
-- url     : https://prove2.me/submissions/d3e1556e-3cb6-448f-9039-5127b7e7a2b0

import Mathlib
import Definitions.Def_CaiCandesShen_GeneralConvex_Problem

namespace CaiCandesShen.GeneralConvex

open Set

theorem aux_occ_eps {A B c : ℝ} (hc : c < 0) (h : ∀ ε : ℝ, 0 < ε → A + ε * c < B) : A ≤ B := by
  by_contra hAB
  push Not at hAB
  have hε : 0 < (A - B) / (-c) := div_pos (by linarith) (by linarith)
  have := h _ hε
  have hc0 : c ≠ 0 := hc.ne
  have e : (A - B) / (-c) * c = B - A := by field_simp; ring
  linarith

theorem aux_occ_sum_rule {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ ψ : E → ℝ) (hφ : ConvexOn ℝ univ φ) (hψ : ConvexOn ℝ univ ψ) (hψc : Continuous ψ)
    (x0 : E) (hmin : ∀ x, φ x0 + ψ x0 ≤ φ x + ψ x) :
    ∃ g : E →L[ℝ] ℝ, (∀ x, g (x - x0) ≤ φ x - φ x0) ∧ ∀ x, - g (x - x0) ≤ ψ x - ψ x0 := by
  set K := φ x0 + ψ x0 with hK
  let s : Set (E × ℝ) := {p | p.1 ∈ univ ∧ ψ p.1 < p.2}
  let t : Set (E × ℝ) := {p | p.1 ∈ univ ∧ p.2 ≤ (fun x => K - φ x) p.1}
  have hs : Convex ℝ s := hψ.convex_strict_epigraph
  have hconc : ConcaveOn ℝ univ (fun x => K - φ x) := by
    have := (hφ.neg).add_const K
    refine this.congr ?_
    intro x _; simp [sub_eq_add_neg, add_comm]
  have ht : Convex ℝ t := hconc.convex_hypograph
  have hso : IsOpen s := by
    have : s = {p : E × ℝ | ψ p.1 < p.2} := by ext p; simp [s]
    rw [this]; exact isOpen_lt (hψc.comp continuous_fst) continuous_snd
  have hdisj : Disjoint s t := by
    rw [Set.disjoint_left]
    rintro ⟨x, r⟩ ⟨_, h1⟩ ⟨_, h2⟩
    have := hmin x
    simp only at h1 h2
    linarith
  obtain ⟨L, u, hLs, hLt⟩ := geometric_hahn_banach_open hs hso ht hdisj
  set c := L (0, 1) with hc
  have hL : ∀ x r, L (x, r) = L (x, 0) + r * c := by
    intro x r
    have : ((x, r) : E × ℝ) = (x, 0) + r • ((0 : E), (1 : ℝ)) := by ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  have mem_s : ∀ x (r : ℝ), ψ x < r → ((x, r) : E × ℝ) ∈ s := fun x r h => ⟨trivial, h⟩
  have mem_t : ∀ x (r : ℝ), r ≤ K - φ x → ((x, r) : E × ℝ) ∈ t := fun x r h => ⟨trivial, h⟩
  have hcneg : c < 0 := by
    have h1 := hLs _ (mem_s x0 (ψ x0 + 1) (by linarith))
    have h2 := hLt _ (mem_t x0 (ψ x0) (by linarith))
    rw [hL] at h1 h2
    nlinarith
  refine ⟨c⁻¹ • L.comp (ContinuousLinearMap.inl ℝ E ℝ), ?_, ?_⟩
  · intro x
    have key : L (x0, 0) + c * (φ x - φ x0) ≤ L (x, 0) := by
      apply aux_occ_eps hcneg
      intro ε hε
      have h1 := hLs _ (mem_s x0 (ψ x0 + ε) (by linarith))
      have h2 := hLt _ (mem_t x (K - φ x) le_rfl)
      rw [hL] at h1 h2
      rw [hK] at h2
      nlinarith
    have hx : (L.comp (ContinuousLinearMap.inl ℝ E ℝ)) (x - x0) = L (x, 0) - L (x0, 0) := by
      simp [← map_sub]
    rw [ContinuousLinearMap.smul_apply, hx, smul_eq_mul]
    have hci : c⁻¹ < 0 := inv_lt_zero.mpr hcneg
    have : c⁻¹ * (c * (φ x - φ x0)) = φ x - φ x0 := by
      rw [← mul_assoc, inv_mul_cancel₀ hcneg.ne, one_mul]
    nlinarith
  · intro x
    have key : L (x, 0) + ψ x * c ≤ L (x0, 0) + ψ x0 * c := by
      apply aux_occ_eps hcneg
      intro ε hε
      have h1 := hLs _ (mem_s x (ψ x + ε) (by linarith))
      have h2 := hLt _ (mem_t x0 (ψ x0) (by rw [hK]; linarith))
      rw [hL] at h1 h2
      nlinarith
    have hx : (L.comp (ContinuousLinearMap.inl ℝ E ℝ)) (x - x0) = L (x, 0) - L (x0, 0) := by
      simp [← map_sub]
    rw [ContinuousLinearMap.smul_apply, hx, smul_eq_mul]
    have hci : c⁻¹ < 0 := inv_lt_zero.mpr hcneg
    have : c⁻¹ * (c * (ψ x0 - ψ x)) = ψ x0 - ψ x := by
      rw [← mul_assoc, inv_mul_cancel₀ hcneg.ne, one_mul]
    nlinarith

theorem aux_occ_frob_eq {n₁ n₂ : ℕ} {ι : Type*} [Fintype ι] (X Y : Mat n₁ n₂)
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ (Fin n₂))) :
    frobInner Y X = ∑ i, inner ℝ (Matrix.toEuclideanLin Y (b i)) (Matrix.toEuclideanLin X (b i)) := by
  have h1 : ∀ (M : Mat n₁ n₂) (v : EuclideanSpace ℝ (Fin n₂)) (r : Fin n₁),
      (Matrix.toEuclideanLin M v) r = inner ℝ (WithLp.toLp 2 (M r)) v := by
    intro M v r
    simp [PiLp.inner_apply, Matrix.mulVec, dotProduct, mul_comm]
  have h2 : ∀ v : EuclideanSpace ℝ (Fin n₂), inner ℝ (Matrix.toEuclideanLin Y v)
      (Matrix.toEuclideanLin X v) = ∑ r, inner ℝ (WithLp.toLp 2 (Y r)) v *
        inner ℝ v (WithLp.toLp 2 (X r)) := by
    intro v
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [h1, h1, real_inner_comm v (WithLp.toLp 2 (X r))]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  simp_rw [h2]
  rw [Finset.sum_comm]
  simp_rw [OrthonormalBasis.sum_inner_mul_inner]
  simp [frobInner, PiLp.inner_apply, mul_comm]


section nuc
variable {n₁ n₂ : ℕ} (X : Mat n₁ n₂)

theorem aux_occ_nuc_eq :
    nuclearNorm X = ∑ i, √((Matrix.toEuclideanLin X).isSymmetric_adjoint_comp_self.eigenvalues
      rfl i) := by
  unfold nuclearNorm LinearMap.singularValues
  rw [Finsupp.sum_embDomain, Finsupp.sum_fintype _ _ (fun _ => rfl)]
  rfl

theorem aux_occ_inner_T (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n₂)))) :
    inner ℝ (Matrix.toEuclideanLin X
        ((Matrix.toEuclideanLin X).isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i))
      (Matrix.toEuclideanLin X
        ((Matrix.toEuclideanLin X).isSymmetric_adjoint_comp_self.eigenvectorBasis rfl j)) =
    if i = j then (Matrix.toEuclideanLin X).isSymmetric_adjoint_comp_self.eigenvalues rfl i
      else 0 := by
  set T := Matrix.toEuclideanLin X
  set hS := T.isSymmetric_adjoint_comp_self
  rw [← LinearMap.adjoint_inner_right]
  have : LinearMap.adjoint T (T (hS.eigenvectorBasis rfl j)) =
      (LinearMap.adjoint T ∘ₗ T) (hS.eigenvectorBasis rfl j) := rfl
  rw [this, hS.apply_eigenvectorBasis, real_inner_smul_right, OrthonormalBasis.inner_eq_ite]
  split_ifs with h
  · subst h; simp
  · simp


theorem aux_occ_norm_T (i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n₂)))) :
    ‖Matrix.toEuclideanLin X
        ((Matrix.toEuclideanLin X).isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i)‖ =
      √((Matrix.toEuclideanLin X).isSymmetric_adjoint_comp_self.eigenvalues rfl i) := by
  rw [norm_eq_sqrt_real_inner, aux_occ_inner_T, if_pos rfl]

theorem aux_occ_nuc_ub (Y : Mat n₁ n₂)
    (hY : ∀ w, ‖Matrix.toEuclideanLin Y w‖ ≤ ‖w‖) : frobInner Y X ≤ nuclearNorm X := by
  rw [aux_occ_frob_eq X Y ((Matrix.toEuclideanLin X).isSymmetric_adjoint_comp_self.eigenvectorBasis
    rfl), aux_occ_nuc_eq]
  apply Finset.sum_le_sum
  intro i _
  calc _ ≤ ‖Matrix.toEuclideanLin Y
          ((Matrix.toEuclideanLin X).isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i)‖ *
        ‖Matrix.toEuclideanLin X
          ((Matrix.toEuclideanLin X).isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i)‖ :=
        real_inner_le_norm _ _
    _ ≤ 1 * √((Matrix.toEuclideanLin X).isSymmetric_adjoint_comp_self.eigenvalues rfl i) := by
        rw [aux_occ_norm_T]
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        exact (hY _).trans_eq (OrthonormalBasis.norm_eq_one _ _)
    _ = _ := one_mul _

theorem aux_occ_nuc_att : ∃ Y : Mat n₁ n₂,
    (∀ w, ‖Matrix.toEuclideanLin Y w‖ ≤ ‖w‖) ∧ frobInner Y X = nuclearNorm X := by
  set T := Matrix.toEuclideanLin X with hT
  set hS := T.isSymmetric_adjoint_comp_self
  set v := hS.eigenvectorBasis rfl
  set lam := hS.eigenvalues rfl
  have hlam : ∀ i, 0 ≤ lam i := fun i => T.isPositive_adjoint_comp_self.nonneg_eigenvalues rfl i
  let cv : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n₂))) → EuclideanSpace ℝ (Fin n₁) :=
    fun i => (√(lam i))⁻¹ • T (v i)
  let T' : EuclideanSpace ℝ (Fin n₂) →ₗ[ℝ] EuclideanSpace ℝ (Fin n₁) :=
    { toFun := fun w => ∑ i, inner ℝ (v i) w • cv i
      map_add' := by
        intro a b
        simp [inner_add_right, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro r a
        simp [real_inner_smul_right, mul_smul, Finset.smul_sum] }
  have hT'v : ∀ j, T' (v j) = cv j := by
    intro j
    show ∑ i, inner ℝ (v i) (v j) • cv i = cv j
    simp [v, OrthonormalBasis.inner_eq_ite, ite_smul]
  have hcc : ∀ i j, inner ℝ (cv i) (cv j) =
      if i = j then (√(lam i))⁻¹ * (√(lam i))⁻¹ * lam i else 0 := by
    intro i j
    simp only [cv, real_inner_smul_left, real_inner_smul_right]
    rw [aux_occ_inner_T]
    split_ifs with h
    · subst h; ring
    · simp
  refine ⟨Matrix.toEuclideanLin.symm T', ?_, ?_⟩
  · intro w
    rw [LinearEquiv.apply_symm_apply, norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
    apply Real.sqrt_le_sqrt
    have e1 : inner ℝ (T' w) (T' w) =
        ∑ i, inner ℝ w (v i) * inner ℝ (v i) w * ((√(lam i))⁻¹ * (√(lam i))⁻¹ * lam i) := by
      show inner ℝ (∑ i, inner ℝ (v i) w • cv i) (∑ i, inner ℝ (v i) w • cv i) = _
      simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, hcc]
      simp [real_inner_comm w]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e1, ← v.sum_inner_mul_inner w w]
    apply Finset.sum_le_sum
    intro i _
    have h1 : (√(lam i))⁻¹ * (√(lam i))⁻¹ * lam i ≤ 1 := by
      rw [mul_assoc, inv_mul_eq_div (√(lam i)) (lam i), Real.div_sqrt, inv_mul_eq_div]
      exact div_self_le_one _
    have h2 : 0 ≤ inner ℝ w (v i) * inner ℝ (v i) w := by
      rw [real_inner_comm w]; exact mul_self_nonneg _
    nlinarith
  · rw [aux_occ_frob_eq X _ v, aux_occ_nuc_eq]
    simp only [LinearEquiv.apply_symm_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hT'v]
    simp only [cv, real_inner_smul_left]
    rw [aux_occ_inner_T, if_pos rfl, inv_mul_eq_div, Real.div_sqrt]

end nuc

theorem aux_occ_frob_lin {n₁ n₂ : ℕ} (Y A B : Mat n₁ n₂) (a b : ℝ) :
    frobInner Y (a • A + b • B) = a * frobInner Y A + b * frobInner Y B := by
  simp only [frobInner, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem aux_occ_nuc_convex {n₁ n₂ : ℕ} : ConvexOn ℝ univ (nuclearNorm : Mat n₁ n₂ → ℝ) := by
  refine ⟨convex_univ, ?_⟩
  intro A _ B _ a b ha hb _
  obtain ⟨Y, hY, hYe⟩ := aux_occ_nuc_att (a • A + b • B)
  rw [← hYe, aux_occ_frob_lin, smul_eq_mul, smul_eq_mul]
  have h1 := aux_occ_nuc_ub A Y hY
  have h2 := aux_occ_nuc_ub B Y hY
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

theorem aux_occ_frob_convex {n₁ n₂ : ℕ} :
    ConvexOn ℝ univ (fun X : Mat n₁ n₂ => frobInner X X) := by
  refine ⟨convex_univ, ?_⟩
  intro A _ B _ a b ha hb hab
  simp only [frobInner, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [sq_nonneg (A i j - B i j), mul_nonneg ha hb]

theorem aux_occ_fτ_convex {n₁ n₂ : ℕ} (τ : ℝ) (hτ : 0 ≤ τ) :
    ConvexOn ℝ univ (fτ τ : Mat n₁ n₂ → ℝ) := by
  have h := (aux_occ_nuc_convex (n₁ := n₁) (n₂ := n₂)).smul hτ |>.add
    ((aux_occ_frob_convex (n₁ := n₁) (n₂ := n₂)).smul (by norm_num : (0 : ℝ) ≤ 1 / 2))
  refine h.congr ?_
  intro X _
  simp only [fτ, frobNorm, Pi.add_apply, smul_eq_mul]
  rw [Real.sq_sqrt]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _


theorem aux_occ_psi_convex {n₁ n₂ m : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i)) (y : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i) :
    ConvexOn ℝ univ (fun X : Mat n₁ n₂ => dot y (constraintMap f X)) := by
  refine ⟨convex_univ, ?_⟩
  intro A _ B _ a b ha hb hab
  simp only [dot, constraintMap, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := (hconv i).2 (mem_univ A) (mem_univ B) ha hb hab
  simp only [smul_eq_mul] at h
  have := mul_le_mul_of_nonneg_left h (hy i)
  nlinarith

theorem aux_occ_core {n₁ n₂ m : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (f : Fin m → Mat n₁ n₂ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (X0 : Mat n₁ n₂) (y : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hmin : ∀ X' : Mat n₁ n₂, lagr τ f X0 y ≤ lagr τ f X' y) :
    ∃ Z : Mat n₁ n₂, IsSubgradient (fτ τ) X0 Z ∧
      ∀ X' : Mat n₁ n₂, 0 ≤ frobInner Z (X' - X0) +
        dot y (constraintMap f X' - constraintMap f X0) := by
  letI : NormedAddCommGroup (Mat n₁ n₂) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Mat n₁ n₂) := Matrix.normedSpace
  have hφ := aux_occ_fτ_convex (n₁ := n₁) (n₂ := n₂) τ hτ.le
  have hψ := aux_occ_psi_convex f hconv y hy
  have hψc : Continuous (fun X : Mat n₁ n₂ => dot y (constraintMap f X)) :=
    continuousOn_univ.mp (hψ.continuousOn isOpen_univ)
  obtain ⟨g, hg1, hg2⟩ := aux_occ_sum_rule (fτ τ) (fun X : Mat n₁ n₂ => dot y (constraintMap f X))
    hφ hψ hψc X0 (fun x => hmin x)
  let Z : Mat n₁ n₂ := Matrix.of fun i j => g (Matrix.single i j 1)
  have hZ : ∀ D : Mat n₁ n₂, frobInner Z D = g D := by
    intro D
    conv_rhs => rw [Matrix.matrix_eq_sum_single D]
    simp only [map_sum]
    unfold frobInner
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : Matrix.single i j (D i j) = D i j • Matrix.single i j (1 : ℝ) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul, smul_eq_mul]
    simp [Z, mul_comm]
  have hdot : ∀ X' : Mat n₁ n₂, dot y (constraintMap f X' - constraintMap f X0) =
      dot y (constraintMap f X') - dot y (constraintMap f X0) := by
    intro X'
    simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  refine ⟨Z, ?_, ?_⟩
  · intro X
    rw [hZ]
    have := hg1 X
    linarith
  · intro X'
    rw [hZ, hdot]
    have := hg2 X'
    linarith

theorem aux_occ_y_nonneg {n₁ n₂ m : ℕ} (τ : ℝ) (f : Fin m → Mat n₁ n₂ → ℝ)
    (δ : ℕ → ℝ) (X : ℕ → Mat n₁ n₂) (y : ℕ → Fin m → ℝ) (hseq : IsGeneralSVTSeq τ f δ X y) :
    ∀ k i, 0 ≤ y k i := by
  intro k i
  cases k with
  | zero => rw [hseq.1]; simp
  | succ k => rw [hseq.2.2 k i]; exact le_max_right _ _

end CaiCandesShen.GeneralConvex

open CaiCandesShen.GeneralConvex

theorem solution {n₁ n₂ m : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (f : Fin m → Mat n₁ n₂ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (δ : ℕ → ℝ) (X : ℕ → Mat n₁ n₂) (y : ℕ → Fin m → ℝ) (hseq : IsGeneralSVTSeq τ f δ X y)
    (Xs : Mat n₁ n₂) (ys : Fin m → ℝ) (hopt : IsPrimalDualOptimal τ f Xs ys) :
    (∀ k : ℕ, ∃ Z : Mat n₁ n₂, IsSubgradient (fτ τ) (X (k + 1)) Z ∧
        ∀ X' : Mat n₁ n₂, 0 ≤ frobInner Z (X' - X (k + 1)) +
          dot (y k) (constraintMap f X' - constraintMap f (X (k + 1)))) ∧
      ∃ Zs : Mat n₁ n₂, IsSubgradient (fτ τ) Xs Zs ∧
        ∀ X' : Mat n₁ n₂, 0 ≤ frobInner Zs (X' - Xs) +
          dot ys (constraintMap f X' - constraintMap f Xs) := by
  refine ⟨fun k => ?_, ?_⟩
  · exact aux_occ_core τ hτ f hconv (X (k + 1)) (y k)
      (aux_occ_y_nonneg τ f δ X y hseq k) (hseq.2.1 k)
  · exact aux_occ_core τ hτ f hconv Xs ys hopt.1 hopt.2.2
