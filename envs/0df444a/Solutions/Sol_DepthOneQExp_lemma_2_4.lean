-- Prove2me | solution 1 for DepthOneQExp.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T06:49:15.072233+00:00
-- url     : https://prove2.me/submissions/26ca7791-1e82-41d5-a6d5-35043508e9fd

import Mathlib
import Definitions.Def_ConstGapCircuits_compactGroups
import Definitions.Def_ConstGapCircuits_spectralGap
import Definitions.Def_DepthOneQExp_kazhdan

namespace DepthOneQExp.L24Aux

open Matrix MeasureTheory
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

section Kazhdan
set_option linter.unusedSectionVars false
variable {G : Type} [Group G] [TopologicalSpace G] {ι : Type} [Fintype ι] (S : ι → G)

theorem kazhdan_bddBelow : BddBelow {c : ℝ | ∃ ρ : ConstGapCircuits.UnitaryRep G,
    (∀ v : EuclideanSpace ℂ (Fin ρ.dim),
      (∀ g : G, Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v = v) →
        v = 0) ∧
    ∃ v : EuclideanSpace ℂ (Fin ρ.dim), ‖v‖ = 1 ∧
      c = ⨆ i : ι, ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
        (ρ.hom (S i) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v - v‖} := by
  refine ⟨0, ?_⟩
  rintro c ⟨ρ, _, v, _, rfl⟩
  exact Real.iSup_nonneg fun i => norm_nonneg _

theorem kazhdan_nonneg : 0 ≤ kazhdan G S := by
  unfold kazhdan
  apply Real.sInf_nonneg
  rintro c ⟨ρ, _, v, _, rfl⟩
  exact Real.iSup_nonneg fun i => norm_nonneg _

theorem kazhdan_le_of_bound (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ ρ : ConstGapCircuits.UnitaryRep G, ∀ v : EuclideanSpace ℂ (Fin ρ.dim), ‖v‖ = 1 → ∀ i,
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.hom (S i) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v - v‖ ≤ B) :
    kazhdan G S ≤ B := by
  unfold kazhdan
  by_cases hne : {c : ℝ | ∃ ρ : ConstGapCircuits.UnitaryRep G,
    (∀ v : EuclideanSpace ℂ (Fin ρ.dim),
      (∀ g : G, Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v = v) →
        v = 0) ∧
    ∃ v : EuclideanSpace ℂ (Fin ρ.dim), ‖v‖ = 1 ∧
      c = ⨆ i : ι, ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
        (ρ.hom (S i) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v - v‖}.Nonempty
  · obtain ⟨c, hc⟩ := hne
    refine (csInf_le (kazhdan_bddBelow S) hc).trans ?_
    obtain ⟨ρ, _, v, hv, rfl⟩ := hc
    exact Real.iSup_le (fun i => h ρ v hv i) hB
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Real.sInf_empty]; exact hB

theorem kazhdan_le_two : kazhdan G S ≤ 2 := by
  apply kazhdan_le_of_bound S 2 (by norm_num)
  intro ρ v hv i
  calc _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.hom (S i) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v‖ + ‖v‖ :=
        norm_sub_le _ _
    _ = 2 := by
      have := U_norm ρ (S i) v
      unfold U at this
      rw [this, hv]; norm_num

variable (ρ : ConstGapCircuits.UnitaryRep G)
  (W : Submodule ℂ (EuclideanSpace ℂ (Fin ρ.dim))) (hW : ∀ g, ∀ w ∈ W, U ρ g w ∈ W)
include hW

theorem kazhdan_le_of_mem (hfree : ∀ w ∈ W, (∀ g, U ρ g w = w) → w = 0) (w : W) (hw : ‖w‖ = 1) :
    kazhdan G S ≤ ⨆ i, ‖U ρ (S i) w - w‖ := by
  apply csInf_le (kazhdan_bddBelow S)
  refine ⟨subrep ρ W hW, subrep_free ρ W hW hfree, subrepEquiv ρ W hW w,
    by rw [LinearIsometryEquiv.norm_map, hw], ?_⟩
  congr 1; funext i
  rw [subrep_apply, ← map_sub, LinearIsometryEquiv.norm_map]
  rfl

theorem kazhdan_sq_le [Nonempty ι] (hfree : ∀ w ∈ W, (∀ g, U ρ g w = w) → w = 0)
    (w : EuclideanSpace ℂ (Fin ρ.dim)) (hw : w ∈ W) :
    kazhdan G S ^ 2 * ‖w‖ ^ 2 ≤ ∑ i, ‖U ρ (S i) w - w‖ ^ 2 := by
  by_cases h0 : w = 0
  · subst h0; simp
  have hpos : 0 < ‖w‖ := norm_pos_iff.2 h0
  set u : W := ⟨((‖w‖⁻¹ : ℝ) : ℂ) • w, W.smul_mem _ hw⟩ with hu
  have hun : ‖u‖ = 1 := by
    rw [hu, Submodule.coe_norm]
    simp only [norm_smul, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hpos.ne'
  have hK := kazhdan_le_of_mem S ρ W hW hfree u hun
  obtain ⟨i0, hi0⟩ := exists_eq_ciSup_of_finite (f := fun i => ‖U ρ (S i) u - u‖)
  rw [← hi0] at hK
  have heq : ‖U ρ (S i0) (u : EuclideanSpace ℂ (Fin ρ.dim)) - u‖ = ‖w‖⁻¹ * ‖U ρ (S i0) w - w‖ := by
    rw [hu]
    simp only [map_smul, ← smul_sub, norm_smul, Complex.norm_real, norm_inv, norm_norm]
  rw [heq] at hK
  have hK2 : kazhdan G S * ‖w‖ ≤ ‖U ρ (S i0) w - w‖ := by
    rw [← le_div_iff₀ hpos]; rw [inv_mul_eq_div] at hK; exact hK
  have hK0 := kazhdan_nonneg S
  calc kazhdan G S ^ 2 * ‖w‖ ^ 2 = (kazhdan G S * ‖w‖) ^ 2 := by ring
    _ ≤ ‖U ρ (S i0) w - w‖ ^ 2 := pow_le_pow_left₀ (by positivity) hK2 2
    _ ≤ _ := Finset.single_le_sum (f := fun i => ‖U ρ (S i) w - w‖ ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ i0)

end Kazhdan

section Haar
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
variable (ρ : ConstGapCircuits.UnitaryRep G)
set_option linter.unusedSectionVars false

instance haar_leftInv : (ConstGapCircuits.haarProbability (G := G)).IsMulLeftInvariant := by
  unfold ConstGapCircuits.haarProbability; infer_instance

theorem rep_integrable : Integrable (fun g => (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ))
    (ConstGapCircuits.haarProbability (G := G)) :=
  (rep_continuous ρ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem mul_P (h : G) : (ρ.hom h : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) *
    ConstGapCircuits.invariantProjector ρ = ConstGapCircuits.invariantProjector ρ := by
  unfold ConstGapCircuits.invariantProjector ConstGapCircuits.moment
  have := (ContinuousLinearMap.mul ℂ (Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) (ρ.hom h)).integral_comp_comm
    (rep_integrable ρ)
  simp only [ContinuousLinearMap.mul_apply'] at this
  rw [← this]
  simp_rw [rep_mul]
  exact integral_mul_left_eq_self (fun g => (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ)) h

theorem P_mul_P : ConstGapCircuits.invariantProjector ρ * ConstGapCircuits.invariantProjector ρ =
    ConstGapCircuits.invariantProjector ρ := by
  nth_rewrite 1 [ConstGapCircuits.invariantProjector, ConstGapCircuits.moment]
  have := ((ContinuousLinearMap.mul ℂ (Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ)).flip
    (ConstGapCircuits.invariantProjector ρ)).integral_comp_comm (rep_integrable ρ)
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] at this
  rw [← this]
  simp_rw [mul_P]
  simp

theorem starP_mul (h : G) : star (ConstGapCircuits.invariantProjector ρ) *
    (ρ.hom h : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) = star (ConstGapCircuits.invariantProjector ρ) := by
  have := congrArg star (mul_P ρ h⁻¹)
  rwa [star_mul, rep_star, inv_inv] at this

theorem mul_P_eq (X : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) : X * ConstGapCircuits.invariantProjector ρ =
    ∫ g, X * (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) ∂(ConstGapCircuits.haarProbability (G := G)) := by
  have := (ContinuousLinearMap.mul ℂ (Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) X).integral_comp_comm
    (rep_integrable ρ)
  simp only [ContinuousLinearMap.mul_apply'] at this
  rw [this]; rfl

theorem star_P : star (ConstGapCircuits.invariantProjector ρ) = ConstGapCircuits.invariantProjector ρ := by
  have h1 : star (ConstGapCircuits.invariantProjector ρ) * ConstGapCircuits.invariantProjector ρ =
      star (ConstGapCircuits.invariantProjector ρ) := by
    rw [mul_P_eq]
    simp_rw [starP_mul]
    simp
  have h2 := congrArg star h1
  rw [star_mul, star_star] at h2
  exact h1.symm.trans h2

theorem P_mul (h : G) : ConstGapCircuits.invariantProjector ρ *
    (ρ.hom h : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) = ConstGapCircuits.invariantProjector ρ := by
  have := starP_mul ρ h
  rwa [star_P] at this

/-- evaluation of a matrix (as an operator) at a vector, as a continuous linear map -/
noncomputable def evalL (d : ℕ) (w : EuclideanSpace ℂ (Fin d)) :
    Matrix (Fin d) (Fin d) ℂ →L[ℂ] EuclideanSpace ℂ (Fin d) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => Matrix.toEuclideanCLM (𝕜 := ℂ) A w
      map_add' := fun A B => by simp [map_add]
      map_smul' := fun c A => by simp [map_smul] }

theorem P_fix (w : EuclideanSpace ℂ (Fin ρ.dim))
    (hw : ∀ g, Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) w = w) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (ConstGapCircuits.invariantProjector ρ) w = w := by
  have := (evalL ρ.dim w).integral_comp_comm (rep_integrable ρ)
  change _ = Matrix.toEuclideanCLM (𝕜 := ℂ) (ConstGapCircuits.invariantProjector ρ) w at this
  rw [← this]
  change ∫ g, Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) w ∂_ = w
  simp_rw [hw]
  simp

end Haar
section CLM
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem rayleigh_decomp (A P : E →L[ℂ] E) (hAP : A * P = P) (hPA : P * A = P) (hPP : P * P = P)
    (hP : ContinuousLinearMap.adjoint P = P) (v : E) :
    RCLike.re ⟪v, (A - P) v⟫_ℂ = RCLike.re ⟪v - P v, A (v - P v)⟫_ℂ ∧ ‖v - P v‖ ≤ ‖v‖ := by
  have hAPv : ∀ w, A (P w) = P w := fun w => by
    rw [← ContinuousLinearMap.mul_apply, hAP]
  have hPAv : ∀ w, P (A w) = P w := fun w => by
    rw [← ContinuousLinearMap.mul_apply, hPA]
  have hPPv : ∀ w, P (P w) = P w := fun w => by
    rw [← ContinuousLinearMap.mul_apply, hPP]
  have hadj : ∀ x y, ⟪P x, y⟫_ℂ = ⟪x, P y⟫_ℂ := fun x y => by
    rw [← ContinuousLinearMap.adjoint_inner_right, hP]
  constructor
  · congr 1
    rw [map_sub, hAPv, inner_sub_left, inner_sub_right, inner_sub_right, hadj, hadj, hPAv, hPPv,
      ContinuousLinearMap.sub_apply, inner_sub_right]
    ring
  · have horth : ⟪P v, v - P v⟫_ℂ = 0 := by
      rw [inner_sub_right, hadj v v, hadj v (P v), hPPv, sub_self]
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P v) (v - P v) horth
    rw [add_sub_cancel] at this
    have h2 : ‖v - P v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
      nlinarith [mul_self_nonneg ‖P v‖, sq_nonneg ‖v - P v‖, sq_nonneg ‖v‖]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

theorem norm_le_of_rayleigh (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ v, |RCLike.re ⟪v, T v⟫_ℂ| ≤ c * ‖v‖ ^ 2) : ‖T‖ ≤ c := by
  have hS : (T : E →ₗ[ℂ] E).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hT
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T hS]
  refine ciSup_le fun x => ?_
  by_cases hx : x = 0
  · simp [hx, hc]
  · have hpos : 0 < ‖x‖ ^ 2 := by positivity
    rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf, abs_div,
      abs_of_pos hpos, div_le_iff₀ hpos]
    have := h x
    rwa [← inner_conj_symm, RCLike.conj_re] at this
end CLM

section Main
set_option linter.unusedSectionVars false
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {ι : Type} [Fintype ι] (S : ι → G) (ρ : ConstGapCircuits.UnitaryRep G)

/-- The invariant projector as an operator. -/
noncomputable def Pc : EuclideanSpace ℂ (Fin ρ.dim) →L[ℂ] EuclideanSpace ℂ (Fin ρ.dim) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (ConstGapCircuits.invariantProjector ρ)

theorem Pc_U (g : G) : Pc ρ * U ρ g = Pc ρ := by
  unfold Pc U; rw [← map_mul, P_mul]

theorem U_Pc (g : G) : U ρ g * Pc ρ = Pc ρ := by
  unfold Pc U; rw [← map_mul, mul_P]

theorem Pc_Pc : Pc ρ * Pc ρ = Pc ρ := by
  unfold Pc; rw [← map_mul, P_mul_P]

theorem Pc_adj : ContinuousLinearMap.adjoint (Pc ρ) = Pc ρ := by
  unfold Pc; rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, star_P]

/-- The orthogonal complement of the invariant vectors, as the kernel of the projector. -/
noncomputable def Wk : Submodule ℂ (EuclideanSpace ℂ (Fin ρ.dim)) :=
  LinearMap.ker (Pc ρ : EuclideanSpace ℂ (Fin ρ.dim) →ₗ[ℂ] EuclideanSpace ℂ (Fin ρ.dim))

theorem Wk_inv : ∀ g, ∀ w ∈ Wk ρ, U ρ g w ∈ Wk ρ := by
  intro g w hw
  simp only [Wk, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hw ⊢
  rw [← ContinuousLinearMap.mul_apply, Pc_U, hw]

theorem Wk_free : ∀ w ∈ Wk ρ, (∀ g, U ρ g w = w) → w = 0 := by
  intro w hw hfix
  simp only [Wk, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hw
  have := P_fix ρ w hfix
  rw [← this]; exact hw

theorem Ac_eq : Matrix.toEuclideanCLM (𝕜 := ℂ) ((1 / (Fintype.card ι : ℂ)) •
    ∑ i, (ρ.hom (S i) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ)) =
      (1 / (Fintype.card ι : ℂ)) • ∑ i, U ρ (S i) := by
  rw [map_smul, map_sum]; rfl

theorem Ac_Pc (hn : Fintype.card ι ≠ 0) :
    ((1 / (Fintype.card ι : ℂ)) • ∑ i, U ρ (S i)) * Pc ρ = Pc ρ := by
  rw [smul_mul_assoc, Finset.sum_mul]
  simp_rw [U_Pc]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [one_div, inv_mul_cancel₀ this, one_smul]

theorem Pc_Ac (hn : Fintype.card ι ≠ 0) :
    Pc ρ * ((1 / (Fintype.card ι : ℂ)) • ∑ i, U ρ (S i)) = Pc ρ := by
  rw [mul_smul_comm, Finset.mul_sum]
  simp_rw [Pc_U]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [one_div, inv_mul_cancel₀ this, one_smul]

theorem re_inner_U (g : G) (x : EuclideanSpace ℂ (Fin ρ.dim)) :
    RCLike.re ⟪x, U ρ g x⟫_ℂ = ‖x‖ ^ 2 - ‖U ρ g x - x‖ ^ 2 / 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), U_norm, inner_re_symm (𝕜 := ℂ)]
  ring

theorem re_inner_avg (hn : Fintype.card ι ≠ 0) (x : EuclideanSpace ℂ (Fin ρ.dim)) :
    RCLike.re ⟪x, ((1 / (Fintype.card ι : ℂ)) • ∑ i, U ρ (S i)) x⟫_ℂ =
      ‖x‖ ^ 2 - (1 / (2 * Fintype.card ι)) * ∑ i, ‖U ρ (S i) x - x‖ ^ 2 := by
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, inner_smul_right, inner_sum]
  have hc : (1 / (Fintype.card ι : ℂ)) = (((1 / (Fintype.card ι : ℝ)) : ℝ) : ℂ) := by push_cast; rfl
  rw [hc, RCLike.re_to_complex, Complex.re_ofReal_mul, Complex.re_sum]
  have h' : ∀ i, (⟪x, U ρ (S i) x⟫_ℂ).re = ‖x‖ ^ 2 - ‖U ρ (S i) x - x‖ ^ 2 / 2 :=
    fun i => re_inner_U ρ (S i) x
  simp_rw [h']
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_div]
  have : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp

theorem sum_le_K (hn : Fintype.card ι ≠ 0) (v : EuclideanSpace ℂ (Fin ρ.dim)) :
    kazhdan G S ^ 2 * ‖v - Pc ρ v‖ ^ 2 ≤ ∑ i, ‖U ρ (S i) (v - Pc ρ v) - (v - Pc ρ v)‖ ^ 2 := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (Nat.pos_of_ne_zero hn)
  apply kazhdan_sq_le S ρ (Wk ρ) (Wk_inv ρ) (Wk_free ρ)
  simp only [Wk, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  rw [map_sub, ← ContinuousLinearMap.mul_apply, Pc_Pc, sub_self]

theorem lemma_2_4_main (hS : ∃ σ : ι ≃ ι, ∀ i, S (σ i) = (S i)⁻¹) :
    (2 ≤ Fintype.card ι → ∀ v : EuclideanSpace ℂ (Fin ρ.dim),
      RCLike.re ⟪v, Matrix.toEuclideanCLM (𝕜 := ℂ)
          ((1 / (Fintype.card ι : ℂ)) • ∑ i, (ρ.hom (S i) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) -
            ConstGapCircuits.invariantProjector ρ) v⟫_ℂ ≤
        (1 - kazhdan G S ^ 2 / (2 * Fintype.card ι)) * ‖v‖ ^ 2) ∧
    ((∃ i, S i = 1) →
      ConstGapCircuits.opNorm
          ((1 / (Fintype.card ι : ℂ)) • ∑ i, (ρ.hom (S i) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) -
            ConstGapCircuits.invariantProjector ρ) ≤
        1 - kazhdan G S ^ 2 / (2 * Fintype.card ι)) := by
  set n := Fintype.card ι with hn_def
  set K := kazhdan G S with hK_def
  have hK0 : 0 ≤ K := kazhdan_nonneg S
  have hK2 : K ≤ 2 := kazhdan_le_two S
  set Ac := (1 / (n : ℂ)) • ∑ i, U ρ (S i) with hAc
  have hT : Matrix.toEuclideanCLM (𝕜 := ℂ)
      ((1 / (n : ℂ)) • ∑ i, (ρ.hom (S i) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) -
        ConstGapCircuits.invariantProjector ρ) = Ac - Pc ρ := by
    rw [map_sub, Ac_eq]; rfl
  -- the key Rayleigh upper bound
  have upper : ∀ (hn : n ≠ 0) (v : EuclideanSpace ℂ (Fin ρ.dim)),
      RCLike.re ⟪v, (Ac - Pc ρ) v⟫_ℂ ≤ (1 - K ^ 2 / (2 * n)) * ‖v - Pc ρ v‖ ^ 2 := by
    intro hn v
    obtain ⟨h1, _⟩ := rayleigh_decomp Ac (Pc ρ) (Ac_Pc S ρ hn) (Pc_Ac S ρ hn) (Pc_Pc ρ) (Pc_adj ρ) v
    rw [h1, re_inner_avg S ρ hn]
    have hs := sum_le_K S ρ hn v
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have : (1 / (2 * (n : ℝ))) * (K ^ 2 * ‖v - Pc ρ v‖ ^ 2) ≤
        (1 / (2 * n)) * ∑ i, ‖U ρ (S i) (v - Pc ρ v) - (v - Pc ρ v)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    have e : (1 - K ^ 2 / (2 * n)) * ‖v - Pc ρ v‖ ^ 2 =
        ‖v - Pc ρ v‖ ^ 2 - (1 / (2 * (n : ℝ))) * (K ^ 2 * ‖v - Pc ρ v‖ ^ 2) := by ring
    rw [e]; linarith
  constructor
  · intro hn2 v
    have hn : n ≠ 0 := by omega
    rw [hT]
    refine (upper hn v).trans ?_
    obtain ⟨_, h2⟩ := rayleigh_decomp Ac (Pc ρ) (Ac_Pc S ρ hn) (Pc_Ac S ρ hn) (Pc_Pc ρ) (Pc_adj ρ) v
    have hc : 0 ≤ 1 - K ^ 2 / (2 * (n : ℝ)) := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      rw [sub_nonneg, div_le_one (by positivity)]
      nlinarith
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h2 2) hc
  · rintro ⟨i0, hi0⟩
    classical
    have hn : n ≠ 0 := (Fintype.card_pos_iff.2 ⟨i0⟩).ne'
    obtain ⟨σ, hσ⟩ := hS
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hKn : K ^ 2 ≤ 2 * n := by
      by_cases h1 : n = 1
      · have hall : ∀ i, S i = 1 := by
          intro i
          have : i = i0 := Fintype.card_le_one_iff.1 h1.le i i0
          rw [this, hi0]
        have hK0' : K ≤ 0 := kazhdan_le_of_bound S 0 le_rfl (fun ρ' v _ i => by rw [hall i]; simp)
        have : K = 0 := le_antisymm hK0' hK0
        rw [this]; nlinarith
      · have : (2 : ℝ) ≤ n := by
          have : 2 ≤ n := by omega
          exact_mod_cast this
        nlinarith
    have hc : 0 ≤ 1 - K ^ 2 / (2 * (n : ℝ)) := by
      rw [sub_nonneg, div_le_one (by positivity)]; exact hKn
    have hAsa : IsSelfAdjoint Ac := by
      rw [IsSelfAdjoint, hAc, star_smul]
      rw [show star (∑ i, U ρ (S i)) = ∑ i, star (U ρ (S i)) from
        map_sum (starAddEquiv (R := EuclideanSpace ℂ (Fin ρ.dim) →L[ℂ] EuclideanSpace ℂ (Fin ρ.dim))) _ _]
      simp_rw [ContinuousLinearMap.star_eq_adjoint, U_adjoint]
      congr 1
      · simp
      · rw [← Equiv.sum_comp σ]; simp_rw [hσ, inv_inv]
    have hPsa : IsSelfAdjoint (Pc ρ) := by
      rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, Pc_adj]
    unfold ConstGapCircuits.opNorm
    rw [hT]
    refine norm_le_of_rayleigh _ (hAsa.sub hPsa) _ hc fun v => ?_
    obtain ⟨h1, h2⟩ := rayleigh_decomp Ac (Pc ρ) (Ac_Pc S ρ hn) (Pc_Ac S ρ hn) (Pc_Pc ρ) (Pc_adj ρ) v
    have hup := upper hn v
    set v1 := v - Pc ρ v with hv1
    have hv : ‖v1‖ ^ 2 ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    have hfle : ∀ i, ‖U ρ (S i) v1 - v1‖ ^ 2 ≤ 4 * ‖v1‖ ^ 2 := by
      intro i
      have h3 := norm_sub_le (U ρ (S i) v1) v1
      rw [U_norm] at h3
      have h4 : ‖U ρ (S i) v1 - v1‖ ^ 2 ≤ (2 * ‖v1‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
      linarith
    have hsum : ∑ i, ‖U ρ (S i) v1 - v1‖ ^ 2 ≤ ((n : ℝ) - 1) * (4 * ‖v1‖ ^ 2) := by
      have e := Finset.add_sum_erase Finset.univ (fun i => ‖U ρ (S i) v1 - v1‖ ^ 2)
        (Finset.mem_univ i0)
      have h0 : ‖U ρ (S i0) v1 - v1‖ ^ 2 = 0 := by rw [hi0, U_one]; simp
      have hle := Finset.sum_le_card_nsmul (Finset.univ.erase i0)
        (fun i => ‖U ρ (S i) v1 - v1‖ ^ 2) (4 * ‖v1‖ ^ 2) (fun i _ => hfle i)
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, nsmul_eq_mul,
        Nat.cast_sub (Nat.pos_of_ne_zero hn), Nat.cast_one] at hle
      rw [← e, h0, zero_add]
      exact hle
    have hlow : -((1 - K ^ 2 / (2 * n)) * ‖v1‖ ^ 2) ≤ RCLike.re ⟪v, (Ac - Pc ρ) v⟫_ℂ := by
      rw [h1, re_inner_avg S ρ hn]
      set t : ℝ := 1 / (2 * n) with ht
      have htpos : 0 < t := by positivity
      have ht2 : t * (2 * n) = 1 := by rw [ht]; field_simp
      have hKt : K ^ 2 / (2 * n) = K ^ 2 * t := by rw [ht]; ring
      rw [hKt]
      have hK4 : K ^ 2 ≤ 4 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsum htpos.le,
        mul_nonneg (sub_nonneg.2 hK4) (mul_nonneg htpos.le (sq_nonneg ‖v1‖))]
    rw [abs_le]
    constructor
    · have := mul_le_mul_of_nonneg_left hv hc
      linarith
    · have := mul_le_mul_of_nonneg_left hv hc
      linarith

end Main
end DepthOneQExp.L24Aux

open scoped InnerProductSpace

open DepthOneQExp in
theorem solution {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {ι : Type} [Fintype ι] (S : ι → G) (hS : ∃ σ : ι ≃ ι, ∀ i, S (σ i) = (S i)⁻¹)
    (ρ : ConstGapCircuits.UnitaryRep G) :
    (2 ≤ Fintype.card ι → ∀ v : EuclideanSpace ℂ (Fin ρ.dim),
      RCLike.re ⟪v, Matrix.toEuclideanCLM (𝕜 := ℂ)
          ((1 / (Fintype.card ι : ℂ)) • ∑ i, (ρ.hom (S i) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) -
            ConstGapCircuits.invariantProjector ρ) v⟫_ℂ ≤
        (1 - kazhdan G S ^ 2 / (2 * Fintype.card ι)) * ‖v‖ ^ 2) ∧
    ((∃ i, S i = 1) →
      ConstGapCircuits.opNorm
          ((1 / (Fintype.card ι : ℂ)) • ∑ i, (ρ.hom (S i) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) -
            ConstGapCircuits.invariantProjector ρ) ≤
        1 - kazhdan G S ^ 2 / (2 * Fintype.card ι)) :=
  DepthOneQExp.L24Aux.lemma_2_4_main S ρ hS
