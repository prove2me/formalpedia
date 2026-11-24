-- Prove2me | solution 1 for DepthOneQExp.theorem_2_11
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T06:51:43.758834+00:00
-- url     : https://prove2.me/submissions/54a06bc6-432e-47f6-aeeb-5d2634627093
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DepthOneQExp_sigma
import Definitions.Def_DepthOneQExp_kazhdan
import Theorems.Thm_DepthOneQExp_kassabov_uniform_bound
import Definitions.Def_ConstGapCircuits_spectralGap

namespace DepthOneQExp.SubrepAux

open Matrix
open scoped Matrix.Norms.L2Operator InnerProductSpace

section Subrep
variable {G : Type} [Group G] [TopologicalSpace G] (ρ : ConstGapCircuits.UnitaryRep G)

theorem rep_continuous : Continuous fun g => (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) :=
  continuous_subtype_val.comp ρ.continuous_hom

theorem rep_mul (g h : G) : (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) * ρ.hom h = ρ.hom (g * h) := by
  rw [map_mul]; rfl

theorem rep_star (g : G) : star (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) = ρ.hom g⁻¹ := by
  rw [map_inv]; rfl

/-- The operator `ρ(g)` on Euclidean space. -/
noncomputable def U (g : G) : EuclideanSpace ℂ (Fin ρ.dim) →L[ℂ] EuclideanSpace ℂ (Fin ρ.dim) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ)

theorem U_mul (g h : G) : U ρ (g * h) = U ρ g * U ρ h := by
  unfold U; rw [← map_mul, rep_mul]

theorem U_one : U ρ 1 = 1 := by
  unfold U; simp

theorem U_adjoint (g : G) : ContinuousLinearMap.adjoint (U ρ g) = U ρ g⁻¹ := by
  unfold U; rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, rep_star]

theorem U_inner_left (g : G) (x y : EuclideanSpace ℂ (Fin ρ.dim)) :
    ⟪U ρ g x, y⟫_ℂ = ⟪x, U ρ g⁻¹ y⟫_ℂ := by
  rw [← U_adjoint, ContinuousLinearMap.adjoint_inner_right]

theorem U_inner (g : G) (x y : EuclideanSpace ℂ (Fin ρ.dim)) :
    ⟪U ρ g x, U ρ g y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [U_inner_left]
  show ⟪x, (U ρ g⁻¹ * U ρ g) y⟫_ℂ = _
  rw [← U_mul, inv_mul_cancel, U_one]; rfl

theorem U_norm (g : G) (x : EuclideanSpace ℂ (Fin ρ.dim)) : ‖U ρ g x‖ = ‖x‖ := by
  have h := U_inner ρ g x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖U ρ g x‖ ^ 2 = ‖x‖ ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

theorem U_continuous (x : EuclideanSpace ℂ (Fin ρ.dim)) : Continuous fun g => U ρ g x := by
  have : (fun g => U ρ g x) = fun g => WithLp.toLp 2
      ((ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) *ᵥ WithLp.ofLp x) := rfl
  rw [this]
  exact (PiLp.continuous_toLp 2 _).comp ((rep_continuous ρ).matrix_mulVec continuous_const)

variable (W : Submodule ℂ (EuclideanSpace ℂ (Fin ρ.dim))) (hW : ∀ g, ∀ w ∈ W, U ρ g w ∈ W)

/-- `ρ(g)` restricted to an invariant subspace. -/
noncomputable def UW (g : G) : W →ₗ[ℂ] W := (U ρ g : _ →ₗ[ℂ] _).restrict (hW g)

theorem UW_apply (g : G) (w : W) : (UW ρ W hW g w : EuclideanSpace ℂ (Fin ρ.dim)) = U ρ g w := rfl

noncomputable def UWhom : G →* (W →ₗ[ℂ] W) where
  toFun := UW ρ W hW
  map_one' := by ext w; simp [UW_apply, U_one]
  map_mul' g h := by ext w; simp [UW_apply, U_mul]

theorem UW_adjoint (g : G) : LinearMap.adjoint (𝕜 := ℂ) (E := W) (F := W) (UW ρ W hW g) = UW ρ W hW g⁻¹ := by
  symm; refine (LinearMap.eq_adjoint_iff (𝕜 := ℂ) (E := W) (F := W) _ _).2 ?_; intro x y
  simp only [Submodule.coe_inner, UW_apply]
  rw [U_inner_left, inv_inv]

/-- The matrix representation on `W` in the orthonormal basis `stdOrthonormalBasis`. -/
noncomputable def subrepHom : G →* Matrix (Fin (Module.finrank ℂ W)) (Fin (Module.finrank ℂ W)) ℂ :=
  (MonoidHomClass.toMonoidHom (LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ W))).comp
    (UWhom ρ W hW)

theorem subrepHom_apply (g : G) : subrepHom ρ W hW g =
    LinearMap.toMatrix (stdOrthonormalBasis ℂ W).toBasis (stdOrthonormalBasis ℂ W).toBasis
      (UW ρ W hW g) := rfl

theorem subrepHom_mem (g : G) : subrepHom ρ W hW g ∈ Matrix.unitaryGroup _ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, subrepHom_apply, Matrix.star_eq_conjTranspose,
    ← LinearMap.toMatrix_adjoint, UW_adjoint, ← LinearMap.toMatrix_mul]
  have : UW ρ W hW g * UW ρ W hW g⁻¹ = 1 := by
    rw [← (UWhom ρ W hW).map_one, ← mul_inv_cancel g, (UWhom ρ W hW).map_mul]; rfl
  rw [this, LinearMap.toMatrix_one]

/-- The subrepresentation on an invariant subspace. -/
noncomputable def subrep : ConstGapCircuits.UnitaryRep G where
  dim := Module.finrank ℂ W
  hom := (subrepHom ρ W hW).codRestrict (Matrix.unitaryGroup _ ℂ) (subrepHom_mem ρ W hW)
  continuous_hom := by
    apply Continuous.subtype_mk
    apply continuous_matrix
    intro i j
    have : ∀ g, subrepHom ρ W hW g i j = ⟪((stdOrthonormalBasis ℂ W) i : EuclideanSpace ℂ (Fin ρ.dim)),
        U ρ g ((stdOrthonormalBasis ℂ W) j)⟫_ℂ := fun g =>
      LinearMap.toMatrixOrthonormal_apply_apply _ _ i j
    simp only [this]
    exact continuous_const.inner (U_continuous ρ _)

/-- The isometry between the invariant subspace and the representation space of `subrep`. -/
noncomputable def subrepEquiv : W ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (subrep ρ W hW).dim) :=
  (stdOrthonormalBasis ℂ W).repr

theorem subrep_apply (g : G) (w : W) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) ((subrep ρ W hW).hom g :
      Matrix (Fin (subrep ρ W hW).dim) (Fin (subrep ρ W hW).dim) ℂ)
      (subrepEquiv ρ W hW w) = subrepEquiv ρ W hW (UW ρ W hW g w) := by
  set b := stdOrthonormalBasis ℂ W
  change WithLp.toLp 2 (LinearMap.toMatrix b.toBasis b.toBasis (UW ρ W hW g) *ᵥ
    WithLp.ofLp (b.repr w)) = b.repr _
  have := LinearMap.toMatrix_mulVec_repr b.toBasis b.toBasis (UW ρ W hW g) w
  have h2 : ∀ x : W, (⇑(b.toBasis.repr x) : Fin _ → ℂ) = WithLp.ofLp (b.repr x) :=
    fun x => funext fun i => b.coe_toBasis_repr_apply x i
  rw [h2, h2] at this
  rw [this]

theorem subrep_free (hfree : ∀ w ∈ W, (∀ g, U ρ g w = w) → w = 0) :
    ∀ v : EuclideanSpace ℂ (Fin (subrep ρ W hW).dim),
      (∀ g, Matrix.toEuclideanCLM (𝕜 := ℂ) ((subrep ρ W hW).hom g :
        Matrix (Fin (subrep ρ W hW).dim) (Fin (subrep ρ W hW).dim) ℂ) v = v) → v = 0 := by
  intro v hv
  obtain ⟨w, rfl⟩ := (subrepEquiv ρ W hW).surjective v
  have h1 : ∀ g, UW ρ W hW g w = w := fun g =>
    (subrepEquiv ρ W hW).injective (by rw [← subrep_apply]; exact hv g)
  have hw0 := hfree w w.2 (fun g => congrArg Subtype.val (h1 g))
  have : w = 0 := Subtype.ext hw0
  subst this; exact map_zero _

end Subrep

section Regular
set_option linter.unusedSectionVars false
variable {G : Type} [Group G] [Fintype G] [DecidableEq G] [TopologicalSpace G] [DiscreteTopology G]

noncomputable def eG : G ≃ Fin (Fintype.card G) := Fintype.equivFin G

/-- Left translation, transported to `Fin (card G)`. -/
noncomputable def psiG : G →* Equiv.Perm (Fin (Fintype.card G)) where
  toFun g := (eG.symm.trans (Equiv.mulLeft g)).trans eG
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

theorem psiG_apply (g : G) (x : Fin (Fintype.card G)) : psiG g x = eG (g * eG.symm x) := rfl

/-- The left-regular representation. -/
noncomputable def regRep : ConstGapCircuits.UnitaryRep G where
  dim := Fintype.card G
  hom := ((Matrix.permMatrixHom (R := ℂ)).comp psiG).codRestrict (Matrix.unitaryGroup _ ℂ)
    (fun g => by
      rw [Matrix.mem_unitaryGroup_iff]
      simp [Matrix.star_eq_conjTranspose, ← permMatrix_mul])
  continuous_hom := continuous_of_discreteTopology

theorem regRep_U (g : G) (w : EuclideanSpace ℂ (Fin (regRep (G := G)).dim))
    (x : Fin (regRep (G := G)).dim) : U regRep g w x = w ((psiG g).symm x) := by
  show ((((psiG g)⁻¹).permMatrix ℂ) *ᵥ WithLp.ofLp w) x = _
  rw [permMatrix_mulVec]; rfl

/-- the constant vector -/
noncomputable def oneV : EuclideanSpace ℂ (Fin (regRep (G := G)).dim) := WithLp.toLp 2 (fun _ => 1)

theorem U_oneV (g : G) : U regRep g (oneV (G := G)) = oneV := by
  apply PiLp.ext; intro i
  rw [regRep_U]; rfl

noncomputable def Wc : Submodule ℂ (EuclideanSpace ℂ (Fin (regRep (G := G)).dim)) :=
  (ℂ ∙ oneV (G := G))ᗮ

theorem Wc_inv : ∀ g, ∀ w ∈ Wc (G := G), U regRep g w ∈ Wc (G := G) := by
  intro g w hw
  simp only [Wc, Submodule.mem_orthogonal_singleton_iff_inner_right] at hw ⊢
  have := U_inner_left (regRep (G := G)) g⁻¹ oneV w
  rw [inv_inv, U_oneV] at this
  rw [← this, hw]

theorem inner_oneV (w : EuclideanSpace ℂ (Fin (regRep (G := G)).dim)) :
    ⟪oneV (G := G), w⟫_ℂ = ∑ a, w a := by
  simp [oneV, PiLp.inner_apply]

theorem Wc_free : ∀ w ∈ Wc (G := G), (∀ g, U regRep g w = w) → w = 0 := by
  intro w hw hfix
  simp only [Wc, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_oneV] at hw
  have hconst : ∀ a b, w a = w b := by
    intro a b
    set g : G := eG.symm b * (eG.symm a)⁻¹
    have h1 := regRep_U g w (psiG g a)
    rw [hfix g] at h1
    erw [Equiv.symm_apply_apply] at h1
    have h2 : psiG g a = b := by
      show eG (g * eG.symm a) = b; simp only [g, inv_mul_cancel_right]; exact Equiv.apply_symm_apply _ _
    rw [← h1]
    exact congrArg (WithLp.ofLp w) h2
  have hpos : 0 < Fintype.card G := Fintype.card_pos
  set a0 : Fin (regRep (G := G)).dim := ⟨0, hpos⟩
  have hsum : ∑ a, w a = (Fintype.card G : ℂ) * w a0 := by
    rw [Finset.sum_congr rfl (fun a _ => hconst a a0), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Fintype.card_fin]
    rfl
  rw [hsum] at hw
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hw0 : w a0 = 0 := (mul_eq_zero.1 hw).resolve_left hc
  apply PiLp.ext; intro a
  rw [hconst a a0, hw0]; rfl

theorem exists_free_rep [Nontrivial G] : ∃ ρ : ConstGapCircuits.UnitaryRep G,
    (∀ v : EuclideanSpace ℂ (Fin ρ.dim),
      (∀ g, Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v = v) →
        v = 0) ∧ ∃ v : EuclideanSpace ℂ (Fin ρ.dim), ‖v‖ = 1 := by
  refine ⟨subrep regRep (Wc (G := G)) Wc_inv, subrep_free _ _ _ Wc_free, ?_⟩
  have h2 : 1 < Fintype.card G := Fintype.one_lt_card
  set a : Fin (regRep (G := G)).dim := ⟨0, by simp [regRep]; omega⟩
  set b : Fin (regRep (G := G)).dim := ⟨1, by simp [regRep]; omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  set v0 : EuclideanSpace ℂ (Fin (regRep (G := G)).dim) :=
    WithLp.toLp 2 (Pi.single a 1 - Pi.single b 1)
  have hv0 : v0 ∈ Wc (G := G) := by
    simp only [Wc, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_oneV]
    simp [v0, Finset.sum_sub_distrib]
  have hv0ne : v0 ≠ 0 := by
    intro h
    have := congrArg (fun x : EuclideanSpace ℂ (Fin (regRep (G := G)).dim) => x a) h
    simp [v0, hab] at this
  set u := subrepEquiv regRep (Wc (G := G)) Wc_inv ⟨v0, hv0⟩
  have hu : ‖u‖ ≠ 0 := by
    rw [LinearIsometryEquiv.norm_map, Submodule.coe_norm]
    exact norm_ne_zero_iff.2 hv0ne
  refine ⟨((‖u‖⁻¹ : ℝ) : ℂ) • u, ?_⟩
  rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hu]

end Regular
end DepthOneQExp.SubrepAux

theorem DepthOneQExp.SubrepAux.sl_nontrivial (k : ℕ) (hk : 2 ≤ k) :
    Nontrivial (Matrix.SpecialLinearGroup (Fin k) (ZMod 2)) := by
  let i : Fin k := ⟨0, by omega⟩
  let j : Fin k := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  refine ⟨⟨⟨Matrix.transvection i j 1, Matrix.det_transvection_of_ne i j hij 1⟩, 1, ?_⟩⟩
  intro h
  have := congrArg (fun M : Matrix.SpecialLinearGroup (Fin k) (ZMod 2) => (M : Matrix (Fin k) (Fin k) (ZMod 2)) i j) h
  simp [Matrix.transvection, hij] at this


open DepthOneQExp DepthOneQExp.SubrepAux in
theorem solution (s : ℕ) (hs : 1 ≤ s) :
    (1 / 400 : ℝ) < kazhdan (Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2)) (sigma s) := by
  haveI := sl_nontrivial (3 * s) (by omega)
  obtain ⟨ρ0, hfree, v0, hv0⟩ := exists_free_rep (G := Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2))
  have hlb : (1 / 250 : ℝ) ≤ kazhdan (Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2)) (sigma s) := by
    unfold kazhdan
    refine le_csInf ⟨_, ρ0, hfree, v0, hv0, rfl⟩ ?_
    rintro c ⟨ρ, hρ, v, hv, rfl⟩
    exact kassabov_uniform_bound s hs ρ hρ v hv
  linarith
