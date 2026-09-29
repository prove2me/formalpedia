-- Prove2me | solution 2 for BookProof.ChapterSirkGramCutoff.retainedVec_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:22:44.47384+00:00
-- url     : https://prove2.me/submissions/e7a72f7a-392e-4657-9455-06622927ba77

import Definitions.Def_ChapterSirkGramCutoff
-- Adapted from Leonardo Pedro, timepiece commit 61595bc (Apache-2.0).
-- https://github.com/leonardopedro/timepiece/tree/61595bc/BookProof
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
-- Adapted from Leonardo Pedro, timepiece commit 61595bc (Apache-2.0).
namespace SirkGramAux
open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening BookProof.ChapterSirkGramWhitening
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

private theorem norm_embedding {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] (V : F →L[ℂ] E)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F) (x : F) : ‖V x‖ = ‖x‖ := by
  have h := congrArg (fun T : F →L[ℂ] F => T x) hVV
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_id', id_eq] at h
  have hin : (inner ℂ (V x) (V x) : ℂ) = inner ℂ x x := by
    rw [← ContinuousLinearMap.adjoint_inner_left, h]
  have := congrArg Complex.re hin
  simp only [inner_self_eq_norm_sq_to_K] at this
  have hsq : ‖V x‖ ^ 2 = ‖x‖ ^ 2 := by
    simpa [← Complex.ofReal_pow] using this
  calc ‖V x‖ = Real.sqrt (‖V x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖x‖ ^ 2) := by rw [hsq]
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)

@[simp] private theorem synthesis_apply {m : ℕ} (w : Fin m → E) (c : EuclideanSpace ℂ (Fin m)) :
    synthesis w c = ∑ i, c i • w i := rfl

private theorem range_synthesis {m : ℕ} (w : Fin m → E) :
    LinearMap.range (synthesis w : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] E)
      = Submodule.span ℂ (Set.range w) := by
  ext x
  simp only [LinearMap.mem_range, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨fun i => c i, rfl⟩
  · rintro ⟨c, rfl⟩; exact ⟨WithLp.toLp 2 c, rfl⟩

private theorem synthesis_mem_span {m : ℕ} (w : Fin m → E) (c : EuclideanSpace ℂ (Fin m)) :
    synthesis w c ∈ Submodule.span ℂ (Set.range w) := by
  rw [← range_synthesis w]; exact ⟨c, rfl⟩

private theorem inner_synthesis_left {m : ℕ} (w : Fin m → E) (c : EuclideanSpace ℂ (Fin m)) (x : E) :
    ⟪synthesis w c, x⟫_ℂ = ∑ i, (starRingEnd ℂ) (c i) * ⟪w i, x⟫_ℂ := by
  simp [mul_comm]

private theorem synthesis_adjoint_eq {m : ℕ} (w : Fin m → E) (x : E) :
    (ContinuousLinearMap.adjoint (synthesis w)) x = (WithLp.toLp 2 fun i => ⟪w i, x⟫_ℂ) := by
  refine ext_inner_left ℂ fun c => ?_
  rw [ContinuousLinearMap.adjoint_inner_right, inner_synthesis_left]
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

private theorem synthesis_injective_of_linearIndependent {m : ℕ} {w : Fin m → E}
    (hw : LinearIndependent ℂ w) : Function.Injective (synthesis w) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  have hc' : ∑ i, (c i) • w i = 0 := hc
  have hzero := (Fintype.linearIndependent_iff.mp hw) (fun i => c i) hc'
  ext i
  simpa using hzero i

private theorem gramOp_apply {m : ℕ} (w : Fin m → E) (c : EuclideanSpace ℂ (Fin m)) (i : Fin m) :
    gramOp w c i = ∑ j, ⟪w i, w j⟫_ℂ * c j := by
  have h : gramOp w c = (WithLp.toLp 2 fun i => ⟪w i, synthesis w c⟫_ℂ) :=
    synthesis_adjoint_eq w (synthesis w c)
  rw [h]
  simp [mul_comm]

private theorem inner_gramOp {m : ℕ} (w : Fin m → E) (c d : EuclideanSpace ℂ (Fin m)) :
    ⟪c, gramOp w d⟫_ℂ = ⟪synthesis w c, synthesis w d⟫_ℂ := by
  exact ContinuousLinearMap.adjoint_inner_right (synthesis w) c (synthesis w d)

private theorem gramOp_isSelfAdjoint {m : ℕ} (w : Fin m → E) : IsSelfAdjoint (gramOp w) := by
  rw [gramOp, IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

private theorem gramOp_nonneg {m : ℕ} (w : Fin m → E) (c : EuclideanSpace ℂ (Fin m)) :
    0 ≤ (⟪c, gramOp w c⟫_ℂ).re := by
  rw [inner_gramOp]
  simpa using inner_self_nonneg (𝕜 := ℂ) (x := synthesis w c)

@[simp] private theorem whitened_apply {m : ℕ} (w : Fin m → E)
    (T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m))
    (c : EuclideanSpace ℂ (Fin m)) : whitened w T c = synthesis w (T c) := rfl

private theorem whitened_adjoint_comp_self {m : ℕ} (w : Fin m → E)
    {T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)} (hT : IsWhitening w T) :
    (ContinuousLinearMap.adjoint (whitened w T)).comp (whitened w T)
      = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin m)) := by
  rw [whitened, ContinuousLinearMap.adjoint_comp, ← hT, gramOp]
  ext c
  simp

private theorem norm_whitened_apply {m : ℕ} (w : Fin m → E)
    {T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)} (hT : IsWhitening w T)
    (c : EuclideanSpace ℂ (Fin m)) : ‖whitened w T c‖ = ‖c‖ :=
  norm_embedding _ (whitened_adjoint_comp_self w hT) c

private theorem range_whitened_le {m : ℕ} (w : Fin m → E)
    (T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)) :
    LinearMap.range (whitened w T : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] E)
      ≤ Submodule.span ℂ (Set.range w) := by
  rintro x ⟨c, rfl⟩
  exact synthesis_mem_span w (T c)

private theorem range_whitened {m : ℕ} (w : Fin m → E)
    {T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)}
    (hT : Function.Surjective T) :
    LinearMap.range (whitened w T : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] E)
      = Submodule.span ℂ (Set.range w) := by
  refine le_antisymm (range_whitened_le w T) ?_
  rw [← range_synthesis w]
  rintro x ⟨c, rfl⟩
  obtain ⟨d, rfl⟩ := hT c
  exact ⟨d, rfl⟩

private theorem adjoint_comp_self_of_inner {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (V : F →L[ℂ] E)
    (h : ∀ c d : F, ⟪V c, V d⟫_ℂ = ⟪c, d⟫_ℂ) :
    (ContinuousLinearMap.adjoint V).comp V = ContinuousLinearMap.id ℂ F := by
  ext d
  refine ext_inner_left ℂ fun c => ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.id_apply]
  exact h c d

private theorem onbEmbedding_apply {d : ℕ} (S : Submodule ℂ E) [CompleteSpace S]
    (b : OrthonormalBasis (Fin d) ℂ S) (c : EuclideanSpace ℂ (Fin d)) :
    onbEmbedding S b c = (b.repr.symm c : E) := rfl

private theorem onbEmbedding_isometry {d : ℕ} (S : Submodule ℂ E) [CompleteSpace S]
    (b : OrthonormalBasis (Fin d) ℂ S) :
    (ContinuousLinearMap.adjoint (onbEmbedding S b)).comp (onbEmbedding S b)
      = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin d)) := by
  refine adjoint_comp_self_of_inner _ fun c e => ?_
  have hcoe : ⟪(b.repr.symm c : E), (b.repr.symm e : E)⟫_ℂ
      = ⟪b.repr.symm c, b.repr.symm e⟫_ℂ := rfl
  rw [onbEmbedding_apply, onbEmbedding_apply, hcoe, LinearIsometryEquiv.inner_map_map]

private theorem range_onbEmbedding {d : ℕ} (S : Submodule ℂ E) [CompleteSpace S]
    (b : OrthonormalBasis (Fin d) ℂ S) :
    LinearMap.range (onbEmbedding S b : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] E) = S := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩; exact (b.repr.symm c).2
  · intro hx
    exact ⟨b.repr ⟨x, hx⟩, by simp [onbEmbedding_apply]⟩

private theorem exists_isometry_range_eq_span {m : ℕ} (w : Fin m → E) :
    ∃ (d : ℕ) (V : EuclideanSpace ℂ (Fin d) →L[ℂ] E),
      d = Module.finrank ℂ (Submodule.span ℂ (Set.range w)) ∧
      (ContinuousLinearMap.adjoint V).comp V = ContinuousLinearMap.id ℂ
        (EuclideanSpace ℂ (Fin d)) ∧
      LinearMap.range (V : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] E)
        = Submodule.span ℂ (Set.range w) := by
  set S := Submodule.span ℂ (Set.range w) with hS
  haveI : FiniteDimensional ℂ S :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range w)
  exact ⟨Module.finrank ℂ S, onbEmbedding S (stdOrthonormalBasis ℂ S), rfl,
    onbEmbedding_isometry S _, range_onbEmbedding S _⟩

private theorem exists_isometry_fin_range_eq_span {m : ℕ} {w : Fin m → E}
    (hw : LinearIndependent ℂ w) :
    ∃ V : EuclideanSpace ℂ (Fin m) →L[ℂ] E,
      (ContinuousLinearMap.adjoint V).comp V = ContinuousLinearMap.id ℂ
        (EuclideanSpace ℂ (Fin m)) ∧
      LinearMap.range (V : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] E)
        = Submodule.span ℂ (Set.range w) := by
  set S := Submodule.span ℂ (Set.range w) with hS
  haveI : FiniteDimensional ℂ S :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range w)
  have hd : Module.finrank ℂ S = m := by
    rw [hS, finrank_span_eq_card hw, Fintype.card_fin]
  let b : OrthonormalBasis (Fin m) ℂ S := (stdOrthonormalBasis ℂ S).reindex (finCongr hd)
  exact ⟨onbEmbedding S b, onbEmbedding_isometry S b, range_onbEmbedding S b⟩

private theorem exists_isWhitening {m : ℕ} {w : Fin m → E} (hw : LinearIndependent ℂ w) :
    ∃ T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m),
      Function.Bijective T ∧ IsWhitening w T := by
  obtain ⟨V, hV, hrange⟩ := exists_isometry_fin_range_eq_span hw
  have hinj : Function.Injective (synthesis w) := synthesis_injective_of_linearIndependent hw
  set A : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
    (ContinuousLinearMap.adjoint V).comp (synthesis w) with hA
  have hVadj : ∀ z, ContinuousLinearMap.adjoint V (V z) = z := fun z =>
    congrArg (fun f : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m) => f z) hV
  have hproj : ∀ c, V (ContinuousLinearMap.adjoint V (synthesis w c)) = synthesis w c := by
    intro c
    have hmem : synthesis w c ∈ LinearMap.range (V : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] E) := by
      rw [hrange]; exact synthesis_mem_span w c
    obtain ⟨z, hz⟩ := hmem
    simp only [ContinuousLinearMap.coe_coe] at hz
    rw [← hz, hVadj z]
  have hAA : (ContinuousLinearMap.adjoint A).comp A = gramOp w := by
    ext c
    simp only [hA, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.comp_apply, gramOp]
    rw [hproj c]
  have hAinj : Function.Injective A := by
    intro x y hxy
    have hx : ContinuousLinearMap.adjoint V (synthesis w x)
        = ContinuousLinearMap.adjoint V (synthesis w y) := hxy
    exact hinj (by rw [← hproj x, ← hproj y, hx])
  have hAbij : Function.Bijective
      (A : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) :=
    ⟨hAinj, (LinearMap.injective_iff_surjective (K := ℂ)).mp hAinj⟩
  let e := LinearEquiv.ofBijective
    (A : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) hAbij
  let T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
    LinearMap.toContinuousLinearMap
      (e.symm : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
  have hAT : ∀ c, A (T c) = c := fun c => e.apply_symm_apply c
  have hATcomp : A.comp T = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin m)) :=
    ContinuousLinearMap.ext fun c => hAT c
  refine ⟨T, ⟨?_, ?_⟩, ?_⟩
  · intro x y hxy
    have hx := congrArg (fun z => A z) hxy
    simpa [hAT] using hx
  · exact fun y => ⟨A y, e.symm_apply_apply y⟩
  · have hid : (ContinuousLinearMap.adjoint (A.comp T)).comp (A.comp T)
        = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin m)) := by
      rw [hATcomp, ContinuousLinearMap.adjoint_id]
      ext c
      rfl
    rw [IsWhitening, ← hAA]
    rw [ContinuousLinearMap.adjoint_comp] at hid
    rw [← hid]
    ext c
    simp

private theorem exists_whitened_isometry_onto_span {m : ℕ} {w : Fin m → E}
    (hw : LinearIndependent ℂ w) :
    ∃ T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m),
      IsWhitening w T ∧
      (ContinuousLinearMap.adjoint (whitened w T)).comp (whitened w T)
        = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin m)) ∧
      LinearMap.range (whitened w T : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] E)
        = Submodule.span ℂ (Set.range w) := by
  obtain ⟨T, hbij, hT⟩ := exists_isWhitening hw
  exact ⟨T, hT, whitened_adjoint_comp_self w hT, range_whitened w hbij.2⟩

private theorem gramMatrix_conjTranspose {m : ℕ} (w : Fin m → E) :
    (gramMatrix w)ᴴ = gramMatrix w := by
  ext i j
  simp [gramMatrix, Matrix.conjTranspose_apply]

private theorem gramOp_eq_toEuclideanCLM {m : ℕ} (w : Fin m → E) :
    gramOp w = Matrix.toEuclideanCLM (𝕜 := ℂ) (gramMatrix w) := by
  ext c i
  simpa [gramMatrix, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct]
    using gramOp_apply w c i

private theorem isWhitening_of_matrix {m : ℕ} (w : Fin m → E) {M : Matrix (Fin m) (Fin m) ℂ}
    (hM : IsWhiteningMatrix w M) :
    IsWhitening w (Matrix.toEuclideanCLM (𝕜 := ℂ) M) := by
  have hstar : ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (𝕜 := ℂ) M)
      = Matrix.toEuclideanCLM (𝕜 := ℂ) Mᴴ := by
    have : star (Matrix.toEuclideanCLM (𝕜 := ℂ) M)
        = Matrix.toEuclideanCLM (𝕜 := ℂ) (star M) := (map_star _ _).symm
    simpa [ContinuousLinearMap.star_eq_adjoint, Matrix.star_eq_conjTranspose] using this
  rw [IsWhitening, gramOp_eq_toEuclideanCLM, hstar]
  have hmul : ∀ P Q : Matrix (Fin m) (Fin m) ℂ,
      (Matrix.toEuclideanCLM (𝕜 := ℂ) P).comp (Matrix.toEuclideanCLM (𝕜 := ℂ) Q)
        = Matrix.toEuclideanCLM (𝕜 := ℂ) (P * Q) := by
    intro P Q
    exact (map_mul (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m)) P Q).symm
  rw [hmul, hmul, ← mul_assoc, hM]
  have hone : Matrix.toEuclideanCLM (𝕜 := ℂ) (1 : Matrix (Fin m) (Fin m) ℂ)
      = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin m)) := by
    exact map_one (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m))
  exact hone

private theorem isWhiteningMatrix_one_of_orthonormal {m : ℕ} {w : Fin m → E}
    (hw : Orthonormal ℂ w) : IsWhiteningMatrix w 1 := by
  have hG : gramMatrix w = 1 := by
    ext i j
    rw [gramMatrix, orthonormal_iff_ite.mp hw i j]
    simp [Matrix.one_apply]
  simp [IsWhiteningMatrix, hG]

private theorem isWhitening_one_of_orthonormal {m : ℕ} {w : Fin m → E} (hw : Orthonormal ℂ w) :
    IsWhitening w (Matrix.toEuclideanCLM (𝕜 := ℂ) (1 : Matrix (Fin m) (Fin m) ℂ)) :=
  isWhitening_of_matrix w (isWhiteningMatrix_one_of_orthonormal hw)

private theorem sum_norm_coord_le {m : ℕ} (c : EuclideanSpace ℂ (Fin m)) :
    ∑ i, ‖c i‖ ≤ Real.sqrt m * ‖c‖ := by
  have h1 : (∑ i, ‖c i‖) ^ 2 ≤ (m : ℝ) * ∑ i, ‖c i‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m)))
      (f := fun i => ‖c i‖)
  have h2 : ‖c‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  have h3 : (0 : ℝ) ≤ ∑ i, ‖c i‖ := by positivity
  have h4 : (∑ i, ‖c i‖) ^ 2 ≤ (Real.sqrt m * ‖c‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (m : ℝ)), h2]
    exact h1
  have h5 : (0 : ℝ) ≤ Real.sqrt m * ‖c‖ := by positivity
  nlinarith [h4, h3, h5]

private theorem norm_defect_synthesis_le {m d : ℕ} (w : Fin m → E)
    (V : EuclideanSpace ℂ (Fin d) →L[ℂ] E) {delta : ℝ}
    (hdelta : ∀ i, ‖w i - V (ContinuousLinearMap.adjoint V (w i))‖ ≤ delta)
    (c : EuclideanSpace ℂ (Fin m)) :
    ‖synthesis w c - V (ContinuousLinearMap.adjoint V (synthesis w c))‖
      ≤ delta * (Real.sqrt m * ‖c‖) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  have hd0 : 0 ≤ delta := le_trans (norm_nonneg _) (hdelta ⟨0, hm⟩)
  have hsplit : synthesis w c - V (ContinuousLinearMap.adjoint V (synthesis w c))
      = ∑ i, c i • (w i - V (ContinuousLinearMap.adjoint V (w i))) := by
    simp only [synthesis_apply, smul_sub, Finset.sum_sub_distrib, map_sum, map_smul]
  rw [hsplit]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ i : Fin m, ‖c i • (w i - V (ContinuousLinearMap.adjoint V (w i)))‖
      ≤ ‖c i‖ * delta := by
    intro i
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hdelta i) (norm_nonneg _)
  calc ∑ i, ‖c i • (w i - V (ContinuousLinearMap.adjoint V (w i)))‖
      ≤ ∑ i, ‖c i‖ * delta := Finset.sum_le_sum fun i _ => hterm i
    _ = delta * ∑ i, ‖c i‖ := by rw [← Finset.sum_mul]; ring
    _ ≤ delta * (Real.sqrt m * ‖c‖) :=
        mul_le_mul_of_nonneg_left (sum_norm_coord_le c) hd0

end SirkGramAux
namespace SirkCutoffAux
open scoped InnerProductSpace
open ContinuousLinearMap SirkGramAux
open BookProof.ChapterSirkGramWhitening BookProof.ChapterSirkGramCutoff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {m : ℕ} {w : Fin m → E}
variable {u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))} {lam : Fin m → ℝ}

private theorem exists_gramEigen {m : ℕ} (w : Fin m → E) :
    ∃ (u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))) (lam : Fin m → ℝ),
      IsGramEigen w u lam := by
  have hsymm : ((gramOp w : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)) :
      EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)).IsSymmetric := by
    intro x y
    have hsa := gramOp_isSelfAdjoint w
    rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint] at hsa
    change ⟪gramOp w x, y⟫_ℂ = ⟪x, gramOp w y⟫_ℂ
    conv_lhs => rw [← hsa]
    rw [ContinuousLinearMap.adjoint_inner_left]
  have hfr : Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) = m := by simp
  exact ⟨hsymm.eigenvectorBasis hfr, fun k => hsymm.eigenvalues hfr k,
    fun k => hsymm.apply_eigenvectorBasis hfr k⟩

private theorem inner_synthesis_gramEigen (heig : IsGramEigen w u lam) (k l : Fin m) :
    ⟪synthesis w (u k), synthesis w (u l)⟫_ℂ = if k = l then (lam l : ℂ) else 0 := by
  have hortho : ⟪u k, u l⟫_ℂ = if k = l then (1 : ℂ) else 0 :=
    orthonormal_iff_ite.mp u.orthonormal k l
  rw [← inner_gramOp, heig l, inner_smul_right, hortho]
  by_cases h : k = l <;> simp [h]

private theorem norm_sq_synthesis_gramEigen (heig : IsGramEigen w u lam) (k : Fin m) :
    ‖synthesis w (u k)‖ ^ 2 = lam k := by
  have h := inner_synthesis_gramEigen heig k k
  rw [if_pos rfl, inner_self_eq_norm_sq_to_K] at h
  have h2 : ((‖synthesis w (u k)‖ ^ 2 : ℝ) : ℂ) = ((lam k : ℝ) : ℂ) := by
    push_cast
    exact h
  exact Complex.ofReal_inj.mp h2

private theorem gramEigen_nonneg (heig : IsGramEigen w u lam) (k : Fin m) : 0 ≤ lam k := by
  rw [← norm_sq_synthesis_gramEigen heig k]; positivity

private theorem norm_sub_proj_le_of_mem_range {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (V : F →L[ℂ] E)
    (hV : (adjoint V).comp V = ContinuousLinearMap.id ℂ F)
    (x : E) {y : E} (hy : ∃ z, V z = y) :
    ‖x - V (adjoint V x)‖ ≤ ‖x - y‖ := by
  obtain ⟨z, rfl⟩ := hy
  set Q := V (adjoint V x) with hQ
  have hVadj : ∀ t : F, adjoint V (V t) = t := by
    intro t
    have h := congrArg (fun (A : F →L[ℂ] F) => A t) hV
    simpa using h
  have hperp : ∀ t : F, ⟪x - Q, V t⟫_ℂ = 0 := by
    intro t
    have h1 : ⟪V t, x - Q⟫_ℂ = ⟪t, adjoint V (x - Q)⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_right V t (x - Q)).symm
    have h2 : adjoint V (x - Q) = 0 := by
      rw [map_sub, hQ, hVadj]; simp
    rw [← inner_conj_symm, h1, h2, inner_zero_right, map_zero]
  have hkey : ⟪x - Q, x - V z⟫_ℂ = ⟪x - Q, x - Q⟫_ℂ := by
    have hsp : x - V z = (x - Q) + V (adjoint V x - z) := by
      rw [map_sub, hQ]; abel
    rw [hsp, inner_add_right, hperp, add_zero]
  have h2 : ‖x - Q‖ ^ 2 = RCLike.re ⟪x - Q, x - V z⟫_ℂ := by
    rw [hkey, inner_self_eq_norm_sq]
  have h3 : RCLike.re ⟪x - Q, x - V z⟫_ℂ ≤ ‖x - Q‖ * ‖x - V z‖ :=
    le_trans (RCLike.re_le_norm _) (norm_inner_le_norm _ _)
  rcases eq_or_lt_of_le (norm_nonneg (x - Q)) with h0 | h0
  · rw [← h0]; positivity
  · have h4 := h2.trans_le h3
    nlinarith

private theorem retainedVec_orthonormal (heig : IsGramEigen w u lam) {d : ℕ} {e : Fin d → Fin m}
    (he : Function.Injective e) (hpos : ∀ j, 0 < lam (e j)) :
    Orthonormal ℂ (retainedVec w u lam e) := by
  rw [orthonormal_iff_ite]
  intro j l
  have hjl : ⟪synthesis w (u (e j)), synthesis w (u (e l))⟫_ℂ
      = if j = l then (lam (e l) : ℂ) else 0 := by
    rw [inner_synthesis_gramEigen heig]
    by_cases h : j = l
    · simp [h]
    · simp only [h, if_false]
      exact if_neg fun hh => h (he hh)
  have hexp : ⟪retainedVec w u lam e j, retainedVec w u lam e l⟫_ℂ
      = (starRingEnd ℂ) ((Real.sqrt (lam (e j)) : ℂ)⁻¹) *
          (((Real.sqrt (lam (e l)) : ℂ))⁻¹ *
            ⟪synthesis w (u (e j)), synthesis w (u (e l))⟫_ℂ) := by
    simp only [retainedVec, inner_smul_left, inner_smul_right]
    ring
  rw [hexp, hjl]
  by_cases h : j = l
  · subst h
    have hp := hpos j
    have hsne : ((Real.sqrt (lam (e j)) : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      positivity
    have hsq : ((Real.sqrt (lam (e j)) : ℝ) : ℂ) * ((Real.sqrt (lam (e j)) : ℝ) : ℂ)
        = (lam (e j) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp.le]
    have hconj : (starRingEnd ℂ) (((Real.sqrt (lam (e j)) : ℝ) : ℂ)⁻¹)
        = (((Real.sqrt (lam (e j)) : ℝ) : ℂ))⁻¹ := by
      rw [map_inv₀, Complex.conj_ofReal]
    rw [if_pos rfl, if_pos rfl, hconj, ← hsq]
    field_simp
  · simp [h]

private theorem synthesis_isometry_of_orthonormal {d : ℕ} {v : Fin d → E} (hv : Orthonormal ℂ v) :
    (adjoint (synthesis v)).comp (synthesis v)
      = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin d)) := by
  refine adjoint_comp_self_of_inner _ fun a b => ?_
  have hortho : ∀ i j, ⟪v i, v j⟫_ℂ = if i = j then (1 : ℂ) else 0 :=
    orthonormal_iff_ite.mp hv
  rw [synthesis_apply, synthesis_apply, sum_inner]
  have hstep : ∀ i : Fin d, ⟪a i • v i, ∑ j, b j • v j⟫_ℂ
      = (starRingEnd ℂ) (a i) * b i := by
    intro i
    rw [inner_sum, Finset.sum_eq_single i]
    · rw [inner_smul_left, inner_smul_right, hortho i i, if_pos rfl, mul_one]
    · intro j _ hj
      rw [inner_smul_left, inner_smul_right, hortho i j, if_neg (Ne.symm hj)]
      ring
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [Finset.sum_congr rfl fun i _ => hstep i]
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

private theorem retainedEmbedding_isometry (heig : IsGramEigen w u lam) {d : ℕ} {e : Fin d → Fin m}
    (he : Function.Injective e) (hpos : ∀ j, 0 < lam (e j)) :
    (adjoint (retainedEmbedding w u lam e)).comp (retainedEmbedding w u lam e)
      = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin d)) :=
  synthesis_isometry_of_orthonormal (retainedVec_orthonormal heig he hpos)

private theorem range_retainedEmbedding {d : ℕ} (w : Fin m → E)
    (u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))) (lam : Fin m → ℝ)
    (e : Fin d → Fin m) :
    LinearMap.range (retainedEmbedding w u lam e :
        EuclideanSpace ℂ (Fin d) →ₗ[ℂ] E)
      = Submodule.span ℂ (Set.range (retainedVec w u lam e)) :=
  range_synthesis _

private theorem mem_range_retainedEmbedding {d : ℕ} {e : Fin d → Fin m}
    (hpos : ∀ j : Fin d, 0 < lam (e j)) (j : Fin d) :
    ∃ z, retainedEmbedding w u lam e z = synthesis w (u (e j)) := by
  refine ⟨EuclideanSpace.single j ((Real.sqrt (lam (e j)) : ℂ)), ?_⟩
  have hs : Real.sqrt (lam (e j)) ≠ 0 := by
    have := hpos j; positivity
  have h1 : retainedEmbedding w u lam e (EuclideanSpace.single j
      ((Real.sqrt (lam (e j)) : ℂ))) = (Real.sqrt (lam (e j)) : ℂ) • retainedVec w u lam e j := by
    rw [retainedEmbedding, synthesis_apply, Finset.sum_eq_single j]
    · simp
    · intro l _ hl; simp [EuclideanSpace.single_apply, hl]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  have hsne : ((Real.sqrt (lam (e j)) : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hs
  rw [h1, retainedVec, smul_smul]
  rw [mul_inv_cancel₀ hsne, one_smul]

end SirkCutoffAux

-- Generated from ChapterSirkGramCutoff.lean — theorem BookProof.ChapterSirkGramCutoff.retainedVec_orthonormal
open BookProof.ChapterSirkGramCutoff









noncomputable section


open scoped InnerProductSpace
open BookProof.ChapterSirkGramWhitening
open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]






variable {m : ℕ} {w : Fin m → E}
variable {u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))} {lam : Fin m → ℝ}
open SirkGramAux SirkCutoffAux

theorem solution (heig : IsGramEigen w u lam) {d : ℕ} {e : Fin d → Fin m}
    (he : Function.Injective e) (hpos : ∀ j, 0 < lam (e j)) :
    Orthonormal ℂ (retainedVec w u lam e) := by
  rw [orthonormal_iff_ite]
  intro j l
  have hjl : ⟪synthesis w (u (e j)), synthesis w (u (e l))⟫_ℂ
      = if j = l then (lam (e l) : ℂ) else 0 := by
    rw [inner_synthesis_gramEigen heig]
    by_cases h : j = l
    · simp [h]
    · simp only [h, if_false]
      exact if_neg fun hh => h (he hh)
  have hexp : ⟪retainedVec w u lam e j, retainedVec w u lam e l⟫_ℂ
      = (starRingEnd ℂ) ((Real.sqrt (lam (e j)) : ℂ)⁻¹) *
          (((Real.sqrt (lam (e l)) : ℂ))⁻¹ *
            ⟪synthesis w (u (e j)), synthesis w (u (e l))⟫_ℂ) := by
    simp only [retainedVec, inner_smul_left, inner_smul_right]
    ring
  rw [hexp, hjl]
  by_cases h : j = l
  · subst h
    have hp := hpos j
    have hsne : ((Real.sqrt (lam (e j)) : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      positivity
    have hsq : ((Real.sqrt (lam (e j)) : ℝ) : ℂ) * ((Real.sqrt (lam (e j)) : ℝ) : ℂ)
        = (lam (e j) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp.le]
    have hconj : (starRingEnd ℂ) (((Real.sqrt (lam (e j)) : ℝ) : ℂ)⁻¹)
        = (((Real.sqrt (lam (e j)) : ℝ) : ℂ))⁻¹ := by
      rw [map_inv₀, Complex.conj_ofReal]
    rw [if_pos rfl, if_pos rfl, hconj, ← hsq]
    field_simp
  · simp [h]

#print axioms solution
