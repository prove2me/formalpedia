-- Prove2me | solution 1 for DerandSq.theorem_4_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:31:28.862719+00:00
-- url     : https://prove2.me/submissions/cd562606-3b09-4877-8c4d-abb379901e0e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_DerandSq_PM
import Definitions.Def_DerandSq_IsVertexTransitive
import Definitions.Def_DerandSq_dsAdj
import Definitions.Def_DerandSq_lam
import Definitions.Def_DerandSq_LambdaH
import Definitions.Def_DerandSq_permOp
import Definitions.Def_DerandSq_permMat
import Definitions.Def_DerandSq_perpCompress
import Definitions.Def_DerandSq_NCPoly_eval
import Definitions.Def_DerandSq_QH
import Definitions.Def_DerandSq_leftReg
import Definitions.Def_DerandSq_mGen
import Theorems.Thm_DerandSq_theorem_2_14
import Theorems.Thm_DerandSq_lemma_4_3
import Theorems.Thm_DerandSq_corollary_4_8

section
set_option autoImplicit false
namespace DerandSq.Dev.T41
open AccessibleMaps

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem tensorOp_apply {a : Type*} [Fintype a] [DecidableEq a] (σ : Matrix a a ℂ) (ω : E →L[ℂ] E)
    (x : Composite a E) (i : a) : (tensorOp σ ω x) i = ∑ j, σ i j • ω (x j) := by
  simp [tensorOp, inject, sum_apply]
  simp [Pi.single_apply]

theorem tensorOp_zero_left {a : Type*} [Fintype a] [DecidableEq a] (ω : E →L[ℂ] E) :
    tensorOp (0 : Matrix a a ℂ) ω = 0 := by
  ext x i
  simp [tensorOp_apply]

theorem tensorOp_add_left {a : Type*} [Fintype a] [DecidableEq a] (σ τ : Matrix a a ℂ) (ω : E →L[ℂ] E) :
    tensorOp (σ + τ) ω = tensorOp σ ω + tensorOp τ ω := by
  ext x i
  simp [tensorOp_apply, add_smul, Finset.sum_add_distrib]

theorem tensorOp_one_apply {D : ℕ} (ω : E →L[ℂ] E) (x : Composite (Fin D) E) (i : Fin D) :
    (tensorOp (1 : Matrix (Fin D) (Fin D) ℂ) ω x) i = ω (x i) := by
  simp [tensorOp_apply, Matrix.one_apply]


/-- `T ↦ 1 ⊗ T` -/
noncomputable abbrev Φ {D : ℕ} (T : E →L[ℂ] E) : Composite (Fin D) E →L[ℂ] Composite (Fin D) E :=
  tensorOp (1 : Matrix (Fin D) (Fin D) ℂ) T

theorem Φ_mul {D : ℕ} (S T : E →L[ℂ] E) : Φ (D := D) (S * T) = Φ S * Φ T := by
  ext x i
  simp [tensorOp_one_apply]

theorem Φ_add {D : ℕ} (S T : E →L[ℂ] E) : Φ (D := D) (S + T) = Φ S + Φ T := by
  ext x i
  simp [tensorOp_one_apply]

theorem Φ_zero {D : ℕ} : Φ (D := D) (0 : E →L[ℂ] E) = 0 := by
  ext x i
  simp [tensorOp_one_apply]

theorem Φ_sum {D : ℕ} {ι : Type*} (s : Finset ι) (f : ι → E →L[ℂ] E) :
    Φ (D := D) (∑ i ∈ s, f i) = ∑ i ∈ s, Φ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Φ_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Φ_add, ih]

theorem Φ_norm (T : E →L[ℂ] E) : ‖Φ (D := 1) T‖ = ‖T‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    have h0 : ‖Φ (D := 1) T x‖ = ‖T (x 0)‖ := by
      simp [PiLp.norm_eq_of_L2, tensorOp_one_apply]
    rw [h0]
    calc ‖T (x 0)‖ ≤ ‖T‖ * ‖x 0‖ := T.le_opNorm _
      _ ≤ ‖T‖ * ‖x‖ := by gcongr; exact PiLp.norm_apply_le x 0
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    set x : Composite (Fin 1) E := WithLp.toLp 2 (fun _ => v)
    have h1 : ‖x‖ = ‖v‖ := by simp [x, PiLp.norm_eq_of_L2]
    have h2 : ‖Φ (D := 1) T x‖ = ‖T v‖ := by
      simp [PiLp.norm_eq_of_L2, tensorOp_one_apply, x]
    have := (Φ (D := 1) T).le_opNorm x
    rw [h1, h2] at this
    exact this


theorem eval_def {D : ℕ} {ι : Type*} (P : NCPoly D ι) (u : ι → E →L[ℂ] E) :
    P.eval u = P.sum (fun w A => tensorOp A (wordOp u w)) := rfl

theorem eval_add {D : ℕ} {ι : Type*} (P Q : NCPoly D ι) (u : ι → E →L[ℂ] E) :
    (P + Q).eval u = P.eval u + Q.eval u := by
  simp only [eval_def]
  exact Finsupp.sum_add_index' (fun _ => tensorOp_zero_left _) (fun _ _ _ => tensorOp_add_left _ _ _)

theorem eval_zero {D : ℕ} {ι : Type*} (u : ι → E →L[ℂ] E) :
    (0 : NCPoly D ι).eval u = 0 := by
  simp [eval_def]

theorem eval_single {D : ℕ} {ι : Type*} (w : FreeMonoid (ι ⊕ ι)) (A : Matrix (Fin D) (Fin D) ℂ)
    (u : ι → E →L[ℂ] E) :
    NCPoly.eval (Finsupp.single w A : NCPoly D ι) u = tensorOp A (wordOp u w) := by
  simp only [eval_def]
  exact Finsupp.sum_single_index (tensorOp_zero_left _)

theorem eval_sum {D : ℕ} {ι : Type*} {κ : Type*} (s : Finset κ) (f : κ → NCPoly D ι)
    (u : ι → E →L[ℂ] E) : (∑ k ∈ s, f k).eval u = ∑ k ∈ s, (f k).eval u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [eval_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, eval_add, ih]

/-- the polynomial `Q_H(y)` -/
noncomputable def Ppoly (d : ℕ) (H : SimpleGraph (Fin d)) [DecidableRel H.Adj] :
    NCPoly 1 (Fin 0 ⊕ Fin d) :=
  ∑ i : Fin d, ∑ j : Fin d, if i < j ∧ H.Adj i j then
    (Finsupp.single (FreeMonoid.of (Sum.inl (Sum.inr i)) * FreeMonoid.of (Sum.inl (Sum.inr j)) :
        FreeMonoid ((Fin 0 ⊕ Fin d) ⊕ (Fin 0 ⊕ Fin d))) (1 : Matrix (Fin 1) (Fin 1) ℂ) +
     Finsupp.single (FreeMonoid.of (Sum.inr (Sum.inr j)) * FreeMonoid.of (Sum.inr (Sum.inr i)) :
        FreeMonoid ((Fin 0 ⊕ Fin d) ⊕ (Fin 0 ⊕ Fin d))) (1 : Matrix (Fin 1) (Fin 1) ℂ)) else 0

theorem eval_Ppoly {d : ℕ} (H : SimpleGraph (Fin d)) [DecidableRel H.Adj]
    (u0 : Fin 0 → E →L[ℂ] E) (V : Fin d → E →L[ℂ] E) :
    (Ppoly d H).eval (Sum.elim u0 V) = Φ (∑ i : Fin d, ∑ j : Fin d,
      if i < j ∧ H.Adj i j then V i * V j + star (V j) * star (V i) else 0) := by
  classical
  simp only [Ppoly, eval_sum, Φ_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : i < j ∧ H.Adj i j
  · simp only [h, and_self, if_true, eval_add, eval_single]
    have w1 : wordOp (Sum.elim u0 V) (FreeMonoid.of (Sum.inl (Sum.inr i)) *
        FreeMonoid.of (Sum.inl (Sum.inr j))) = V i * V j := by
      simp [wordOp, letterOp]
    have w2 : wordOp (Sum.elim u0 V) (FreeMonoid.of (Sum.inr (Sum.inr j)) *
        FreeMonoid.of (Sum.inr (Sum.inr i))) = star (V j) * star (V i) := by
      simp [wordOp, letterOp]
    rw [w1, w2, Φ_add]
  · simp [h, eval_zero, Φ_zero]


theorem permOp_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (x : EuclideanSpace ℂ (Fin N)) (v : Fin N) :
    permOp σ x v = x (σ⁻¹ v) := by
  simp [permOp, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]

theorem toEuclideanCLM_perm {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) ((permMat σ).map (Complex.ofReal)) = permOp σ := by
  ext x v
  have : x = WithLp.toLp 2 (x.ofLp) := rfl
  rw [this, Matrix.toEuclideanCLM_toLp, permOp_apply]
  simp only [WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, Matrix.map_apply, permMat, Matrix.of_apply]
  rw [Finset.sum_eq_single (σ⁻¹ v)]
  · simp
  · intro b _ hb
    have : σ b ≠ v := fun h => hb (by rw [← h]; simp)
    simp [this]
  · simp


section cplx
variable {N : ℕ}

noncomputable def reV (x : EuclideanSpace ℂ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 fun k => (x k).re
noncomputable def imV (x : EuclideanSpace ℂ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 fun k => (x k).im
noncomputable def ofV (u : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 fun k => ((u k : ℝ) : ℂ)

theorem norm_sq_split (x : EuclideanSpace ℂ (Fin N)) : ‖x‖ ^ 2 = ‖reV x‖ ^ 2 + ‖imV x‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, reV, imV, Real.norm_eq_abs, sq_abs,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem norm_ofV (u : EuclideanSpace ℝ (Fin N)) : ‖ofV u‖ = ‖u‖ := by
  have h := norm_sq_split (ofV u)
  have h1 : reV (ofV u) = u := by ext k; simp [reV, ofV]
  have h2 : imV (ofV u) = 0 := by ext k; simp [imV, ofV]
  rw [h1, h2] at h
  simp at h
  exact h

theorem cplx_apply (B : Matrix (Fin N) (Fin N) ℝ) (x : EuclideanSpace ℂ (Fin N)) :
    reV (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) (B.map Complex.ofReal) x) =
      Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) B (reV x) ∧
    imV (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) (B.map Complex.ofReal) x) =
      Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) B (imV x) := by
  have : x = WithLp.toLp 2 (x.ofLp) := rfl
  rw [this]
  constructor
  · ext k
    simp [Matrix.toEuclideanCLM_toLp, reV, Matrix.mulVec, dotProduct]
  · ext k
    simp [Matrix.toEuclideanCLM_toLp, imV, Matrix.mulVec, dotProduct]

theorem cplx_ofV (B : Matrix (Fin N) (Fin N) ℝ) (u : EuclideanSpace ℝ (Fin N)) :
    Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) (B.map Complex.ofReal) (ofV u) =
      ofV (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) B u) := by
  have : u = WithLp.toLp 2 (u.ofLp) := rfl
  rw [this]
  ext k
  simp [ofV, Matrix.toEuclideanCLM_toLp, Matrix.mulVec, dotProduct]

theorem cplx_norm (B : Matrix (Fin N) (Fin N) ℝ) :
    ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) (B.map Complex.ofReal)‖ =
      ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) B‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    obtain ⟨h1, h2⟩ := cplx_apply B x
    have hs := norm_sq_split (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) (B.map Complex.ofReal) x)
    rw [h1, h2] at hs
    have a1 := (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) B).le_opNorm (reV x)
    have a2 := (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) B).le_opNorm (imV x)
    have hx := norm_sq_split x
    set C := ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) B‖
    have : ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) (B.map Complex.ofReal) x‖ ^ 2 ≤
        (C * ‖x‖) ^ 2 := by
      rw [hs, mul_pow, hx]
      have b1 := pow_le_pow_left₀ (norm_nonneg _) a1 2
      have b2 := pow_le_pow_left₀ (norm_nonneg _) a2 2
      rw [mul_pow] at b1 b2
      nlinarith
    exact le_of_sq_le_sq this (by positivity)
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => ?_
    have := (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) (B.map Complex.ofReal)).le_opNorm (ofV u)
    rwa [cplx_ofV, norm_ofV, norm_ofV] at this

end cplx

section matside

theorem star_permOp {N : ℕ} (σ : Equiv.Perm (Fin N)) (hσ : ∀ x, σ (σ x) = x) :
    star (permOp σ) = permOp σ := by
  rw [← toEuclideanCLM_perm, ← map_star]
  congr 1
  ext w v
  have key : σ w = v ↔ σ v = w := ⟨fun h => by rw [← h, hσ], fun h => by rw [← h, hσ]⟩
  simp [permMat, key]

theorem perp_Φ {D N : ℕ} (T : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
    perpCompress D N (Φ T) =
      Φ (Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - (N : ℂ)⁻¹ • Matrix.of (fun _ _ : Fin N => (1 : ℂ))) *
        T * Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - (N : ℂ)⁻¹ • Matrix.of (fun _ _ : Fin N => (1 : ℂ)))) := by
  simp only [perpCompress, Φ_mul]
  ext x : 1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply]

theorem Q_map (N : ℕ) :
    (1 - (N : ℂ)⁻¹ • Matrix.of (fun _ _ : Fin N => (1 : ℂ))) =
      ((1 - (N : ℝ)⁻¹ • Matrix.of (fun _ _ : Fin N => (1 : ℝ))).map Complex.ofReal) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem matrix_side {n d k : ℕ} (H : SimpleGraph (Fin d)) [DecidableRel H.Adj]
    (hH : H.IsRegularOfDegree k) (M : Fin d → PM (2 * n)) (u0 : Fin 0 → EuclideanSpace ℂ (Fin (2 * n)) →L[ℂ] EuclideanSpace ℂ (Fin (2 * n))) :
    ‖perpCompress 1 (2 * n) ((Ppoly d H).eval (Sum.elim u0 (fun j => permOp (M j).1)))‖ =
      lam (dsAdj (fun j => (M j).1) H) := by
  have hstar : ∀ j, star (permOp (M j).1) = permOp (M j).1 := fun j =>
    star_permOp _ (fun x => (M j).2 x |>.1)
  rw [eval_Ppoly, perp_Φ, Φ_norm]
  simp only [hstar]
  have h43 := (DerandSq.lemma_4_3 H hH (fun j => (M j).1)).2
  set Qr : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ := 1 - ((2 * n : ℕ) : ℝ)⁻¹ • Matrix.of (fun _ _ : Fin (2 * n) => (1 : ℝ)) with hQr
  have hS : (∑ i : Fin d, ∑ j : Fin d, if i < j ∧ H.Adj i j then
        permOp (M i).1 * permOp (M j).1 + permOp (M j).1 * permOp (M i).1 else 0) =
      Matrix.toEuclideanCLM (n := Fin (2 * n)) (𝕜 := ℂ) ((dsAdj (fun j => (M j).1) H).map Complex.ofReal) := by
    rw [h43]
    have : ∀ A : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ, A.map Complex.ofReal = (Complex.ofRealHom.mapMatrix A) := fun _ => rfl
    rw [this]
    simp only [map_sum, apply_ite, map_add, map_mul, map_zero]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · rw [show Complex.ofRealHom.mapMatrix (permMat (M i).1) = (permMat (M i).1).map Complex.ofReal from rfl,
        show Complex.ofRealHom.mapMatrix (permMat (M j).1) = (permMat (M j).1).map Complex.ofReal from rfl,
        toEuclideanCLM_perm, toEuclideanCLM_perm]
    · rfl
  rw [hS, Q_map]
  have : ∀ A B C : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ,
      Matrix.toEuclideanCLM (n := Fin (2 * n)) (𝕜 := ℂ) (A.map Complex.ofReal) *
      Matrix.toEuclideanCLM (n := Fin (2 * n)) (𝕜 := ℂ) (B.map Complex.ofReal) *
      Matrix.toEuclideanCLM (n := Fin (2 * n)) (𝕜 := ℂ) (C.map Complex.ofReal) =
      Matrix.toEuclideanCLM (n := Fin (2 * n)) (𝕜 := ℂ) ((A * B * C).map Complex.ofReal) := by
    intro A B C
    have hm : ∀ X Y : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ,
        (X * Y).map Complex.ofReal = X.map Complex.ofReal * Y.map Complex.ofReal :=
      fun X Y => map_mul Complex.ofRealHom.mapMatrix X Y
    rw [← map_mul, ← map_mul, hm, hm]
  rw [this, cplx_norm]
  rfl

end matside


section reindex
variable {G G' : Type*}

noncomputable def reL (e : G ≃ G') : lp (fun _ : G => ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : G' => ℂ) 2 where
  toFun f := ⟨fun g' => f (e.symm g'), by
    have hf := (lp.memℓp f)
    rw [memℓp_gen_iff (by norm_num)] at hf
    show Memℓp (fun g' : G' => f (e.symm g')) 2
    rw [memℓp_gen_iff (by norm_num)]
    exact e.symm.summable_iff.mpr hf⟩
  map_add' f f' := by ext h; rfl
  map_smul' c f := by ext h; rfl
  norm_map' f := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.symm.tsum_eq (fun h => ‖f h‖ ^ (2 : ENNReal).toReal)

theorem reL_apply (e : G ≃ G') (f : lp (fun _ : G => ℂ) 2) (g' : G') : reL e f g' = f (e.symm g') := rfl

noncomputable def reLE (e : G ≃ G') : lp (fun _ : G => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : G' => ℂ) 2 :=
  { toLinearEquiv := LinearEquiv.ofLinear (reL e).toLinearMap (reL e.symm).toLinearMap
      (by ext f g; simp [reL_apply]) (by ext f g; simp [reL_apply])
    norm_map' := (reL e).norm_map }

theorem reLE_apply (e : G ≃ G') (f : lp (fun _ : G => ℂ) 2) (g' : G') :
    reLE e f g' = f (e.symm g') := rfl



theorem reLE_symm_apply (e : G ≃ G') (y : lp (fun _ : G' => ℂ) 2) (g : G) :
    (reLE e).symm y g = y (e g) := rfl

theorem leftReg_apply {Γ : Type*} [Group Γ] (g : Γ) (f : L2 Γ) (h : Γ) :
    leftReg g f h = f (g⁻¹ * h) := rfl

theorem conj_leftReg {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G') (g : G) :
    (reLE φ.toEquiv).conjStarAlgEquiv (leftReg g) = leftReg (φ g) := by
  ext y h'
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, reLE_apply, leftReg_apply, leftReg_apply]
  change ((reLE φ.toEquiv).symm y) (g⁻¹ * φ.symm h') = _
  rw [reLE_symm_apply]
  simp

theorem conj_norm {G G' : Type*} (e : lp (fun _ : G => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : G' => ℂ) 2)
    (T : lp (fun _ : G => ℂ) 2 →L[ℂ] lp (fun _ : G => ℂ) 2) : ‖e.conjStarAlgEquiv T‖ = ‖T‖ := by
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply]
  rw [ContinuousLinearMap.opNorm_linearIsometryEquiv_comp, ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

noncomputable def inrEquiv (d : ℕ) : Gam d ≃* Monoid.Coprod (FreeGroup (Fin 0)) (Gam d) :=
  MonoidHom.toMulEquiv (Monoid.Coprod.inr)
    (Monoid.Coprod.lift (FreeGroup.lift (fun i : Fin 0 => i.elim0)) (MonoidHom.id (Gam d)))
    (MonoidHom.ext fun x => by simp)
    (by
      apply Monoid.Coprod.hom_ext
      · apply FreeGroup.ext_hom
        intro i; exact i.elim0
      · exact MonoidHom.ext fun x => by simp)

theorem inrEquiv_apply (d : ℕ) (g : Gam d) : inrEquiv d g = Monoid.Coprod.inr g := rfl

end reindex

section limside

theorem limit_side {d : ℕ} (H : SimpleGraph (Fin d)) [DecidableRel H.Adj] :
    ‖(Ppoly d H).eval (Sum.elim
      (fun i : Fin 0 => leftReg (Monoid.Coprod.inl (FreeGroup.of i) :
        Monoid.Coprod (FreeGroup (Fin 0)) (Gam d)))
      (fun j => leftReg (Monoid.Coprod.inr (mGen j) :
        Monoid.Coprod (FreeGroup (Fin 0)) (Gam d))))‖ = ‖QH H‖ := by
  classical
  rw [eval_Ppoly, Φ_norm]
  have hj : ∀ j, (leftReg (Monoid.Coprod.inr (mGen j) : Monoid.Coprod (FreeGroup (Fin 0)) (Gam d))) =
      (reLE (inrEquiv d).toEquiv).conjStarAlgEquiv (leftReg (mGen j)) := by
    intro j
    have := conj_leftReg (G := Gam d) (G' := Monoid.Coprod (FreeGroup (Fin 0)) (Gam d)) (inrEquiv d) (mGen j)
    rw [inrEquiv_apply] at this
    exact this.symm
  simp only [hj]
  rw [← conj_norm (reLE (inrEquiv d).toEquiv) (QH H)]
  congr 1
  unfold QH
  simp only [← map_star, ← map_mul, ← map_add, map_sum, apply_ite, map_zero]

end limside

section prob

theorem coinProb_nonneg {Ω : Type*} [Fintype Ω] (A : Ω → Prop) : 0 ≤ PunctSketch.coinProb A := by
  unfold PunctSketch.coinProb
  positivity

theorem coinProb_mono {Ω : Type*} [Fintype Ω] (A B : Ω → Prop) (h : ∀ x, A x → B x) :
    PunctSketch.coinProb A ≤ PunctSketch.coinProb B := by
  classical
  unfold PunctSketch.coinProb
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (fun x hx => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact h x hx)

theorem coinProb_equiv {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] (e : Ω ≃ Ω') (B : Ω' → Prop) :
    PunctSketch.coinProb (fun x => B (e x)) = PunctSketch.coinProb B := by
  classical
  unfold PunctSketch.coinProb
  rw [Fintype.card_congr e]
  congr 2
  apply Finset.card_equiv e
  intro x
  simp

end prob

end DerandSq.Dev.T41

namespace DerandSq
open DerandSq.Dev.T41 in
theorem chk_theorem_4_1 {d k : ℕ} (hd : 3 ≤ d) (hk : 1 ≤ k) (H : SimpleGraph (Fin d))
    [DecidableRel H.Adj] (hH : H.IsRegularOfDegree k) (hvt : IsVertexTransitive H)
    (ε : ℝ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun n : ℕ => PunctSketch.coinProb (fun M : Fin d → PM (2 * n) =>
        LambdaH d H + ε ≤ lam (dsAdj (fun j => (M j).1) H)))
      Filter.atTop (nhds 0) := by
  have h := (DerandSq.theorem_2_14 1 0 d ε hε).2 (Ppoly d H)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun n => coinProb_nonneg _) (fun n => ?_)
  let e : (Fin d → PM (2 * n)) ≃ (Fin 0 → Equiv.Perm (Fin (2 * n))) × (Fin d → PM (2 * n)) :=
    { toFun := fun M => (fun i => i.elim0, M)
      invFun := Prod.snd
      left_inv := fun _ => rfl
      right_inv := fun p => by
        ext i
        · exact i.elim0
        · rfl }
  rw [← coinProb_equiv e]
  apply coinProb_mono
  intro M hM
  have h1 := matrix_side H hH M (fun i => permOp ((e M).1 i))
  have h2 := limit_side H
  have h3 := corollary_4_8 hd hk H hH hvt
  change ε ≤ |‖perpCompress 1 (2 * n) ((Ppoly d H).eval
    (Sum.elim (fun i => permOp ((e M).1 i)) (fun j => permOp (M j).1)))‖ - _|
  rw [h1, h2, h3]
  exact le_trans (by linarith) (le_abs_self _)

end DerandSq
end

theorem solution : type_of% @DerandSq.chk_theorem_4_1 := @DerandSq.chk_theorem_4_1
