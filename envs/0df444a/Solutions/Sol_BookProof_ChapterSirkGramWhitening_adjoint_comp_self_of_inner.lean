-- Prove2me | solution 1 for BookProof.ChapterSirkGramWhitening.adjoint_comp_self_of_inner
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:19:14.236691+00:00
-- url     : https://prove2.me/submissions/b252ba0f-9ee8-4102-8317-aae3639b61ac

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

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.adjoint_comp_self_of_inner
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
open SirkGramAux

theorem solution {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (V : F →L[ℂ] E)
    (h : ∀ c d : F, ⟪V c, V d⟫_ℂ = ⟪c, d⟫_ℂ) :
    (ContinuousLinearMap.adjoint V).comp V = ContinuousLinearMap.id ℂ F := by
  ext d
  refine ext_inner_left ℂ fun c => ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.id_apply]
  exact h c d

#print axioms solution
