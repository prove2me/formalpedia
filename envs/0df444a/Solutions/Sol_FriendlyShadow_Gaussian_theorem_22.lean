-- Prove2me | solution 1 for FriendlyShadow.Gaussian.theorem_22
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T15:44:32.751937+00:00
-- url     : https://prove2.me/submissions/6344def8-fbba-4a5a-a41a-89b0e4573f5d

import Mathlib
import Definitions.Def_FriendlyShadow_Gaussian_Model
import Definitions.Def_FriendlyShadow_Gaussian_Shape

-- ===== CV2.lean =====

open MeasureTheory

namespace FSCV

/-- Linear change of variables for lower integrals on `Fin d → ℝ` (no measurability needed). -/
theorem cv_lin {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.det ≠ 0)
    (g : (Fin d → ℝ) → ENNReal) :
    ∫⁻ w, g w = ENNReal.ofReal |M.det| * ∫⁻ v, g (M.mulVec v) := by
  have hdet : LinearMap.det (Matrix.toLin' M) ≠ 0 := by rwa [LinearMap.det_toLin']
  set e : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
    (LinearMap.toContinuousLinearMap (Matrix.toLin' M)).toContinuousLinearEquivOfDetNeZero
      hdet with he
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := volume)
    (f := Matrix.toLin' M) hdet
  have hcoe : ⇑(Matrix.toLin' M) = ⇑e.toHomeomorph.toMeasurableEquiv := by
    funext v; rfl
  rw [hcoe] at hmap
  have h1 : ∫⁻ v, g (M.mulVec v) = ∫⁻ w, g w ∂(Measure.map
      (⇑e.toHomeomorph.toMeasurableEquiv) volume) := by
    rw [lintegral_map_equiv]
    rfl
  rw [h1, hmap, lintegral_smul_measure, LinearMap.det_toLin', smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (abs_nonneg _), abs_inv, mul_inv_cancel₀ (abs_ne_zero.2 hM),
    ENNReal.ofReal_one, one_mul]

/-- The graph-coordinate matrix: row `i` is `(y i, 1)`, so `(M y).mulVec (snoc c t) i = ⟪y i, c⟫ + t`. -/
noncomputable def gmat {m : ℕ} (y : Fin (m + 1) → Fin m → ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.of fun i => Fin.snoc (y i) 1

lemma gmat_mulVec {m : ℕ} (y : Fin (m + 1) → Fin m → ℝ) (c : Fin m → ℝ) (t : ℝ)
    (i : Fin (m + 1)) :
    (gmat y).mulVec (Fin.snoc c t) i = ∑ k, y i k * c k + t := by
  simp [gmat, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]

/-- Signed cofactors along column `j` (they do not depend on column `j` of `A`). -/
noncomputable def cof {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (j i : Fin (m + 1)) : ℝ :=
  (-1) ^ ((i : ℕ) + j) * (A.submatrix i.succAbove j.succAbove).det

/-- The determinant is linear in column `j`, with the cofactor vector as coefficients. -/
lemma det_updateCol_eq {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (j : Fin (m + 1))
    (v : Fin (m + 1) → ℝ) : (A.updateCol j v).det = ∑ i, v i * cof A j i := by
  rw [Matrix.det_succ_column _ j]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsub : (A.updateCol j v).submatrix i.succAbove j.succAbove =
      A.submatrix i.succAbove j.succAbove := by
    ext a b; simp [Matrix.updateCol_ne (Fin.succAbove_ne j b)]
  rw [hsub, Matrix.updateCol_self]; unfold cof; ring

/-- Cofactors along column `j` annihilate every other column: `Σ_i A i k · C_i = 0`. -/
lemma cof_kernel {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (j k : Fin (m + 1))
    (hk : k ≠ j) : ∑ i, A i k * cof A j i = 0 := by
  rw [← det_updateCol_eq]
  exact Matrix.det_zero_of_column_eq hk (fun i => by
    simp [Matrix.updateCol_self, Matrix.updateCol_ne hk])

/-- Cofactors depend only on the columns other than `j`. -/
lemma cof_updateCol {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (j : Fin (m + 1))
    (v : Fin (m + 1) → ℝ) : cof (A.updateCol j v) j = cof A j := by
  funext i; unfold cof
  congr 2
  ext a b; simp [Matrix.updateCol_ne (Fin.succAbove_ne j b)]

lemma gmat_continuous {m : ℕ} : Continuous fun y : Fin (m + 1) → Fin m → ℝ => gmat y := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp only [gmat, Matrix.of_apply, Fin.snoc_last]; exact continuous_const
  · simp only [gmat, Matrix.of_apply, Fin.snoc_castSucc]
    exact (continuous_apply k).comp (continuous_apply i)

/-- C6b: graph change of variables, Tonelli form. -/
theorem cv_graph {m : ℕ} (F : (Fin (m + 1) → Fin m → ℝ) → (Fin (m + 1) → ℝ) → ENNReal)
    (hF : Measurable (Function.uncurry F))
    (h0 : ∀ y w, (gmat y).det = 0 → F y w = 0) :
    ∫⁻ y, ∫⁻ w, F y w =
      ∫⁻ v, ∫⁻ y, ENNReal.ofReal |(gmat y).det| * F y ((gmat y).mulVec v) := by
  have hin : ∀ y, ∫⁻ w, F y w =
      ∫⁻ v, ENNReal.ofReal |(gmat y).det| * F y ((gmat y).mulVec v) := by
    intro y
    by_cases hy : (gmat y).det = 0
    · simp [h0 y _ hy, hy]
    · rw [cv_lin (gmat y) hy (F y), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp_rw [hin]
  refine lintegral_lintegral_swap ?_
  refine Measurable.aemeasurable ?_
  have hg : Continuous fun p : (Fin (m + 1) → Fin m → ℝ) × (Fin (m + 1) → ℝ) => gmat p.1 :=
    gmat_continuous.comp continuous_fst
  refine Measurable.mul ?_ ?_
  · exact ENNReal.measurable_ofReal.comp (hg.matrix_det.abs.measurable)
  · exact hF.comp (measurable_fst.prodMk
      ((hg.matrix_mulVec continuous_snd).measurable))

/-- Cofactor as a determinant with column `j` replaced by a basis vector. -/
lemma cof_eq_det {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (j i : Fin (m + 1)) :
    cof A j i = (A.updateCol j (Pi.single i 1)).det := by
  rw [det_updateCol_eq]; simp [Pi.single_apply]

/-- Cofactors along column `j` are invariant under adding multiples of column `o ≠ j`
to the other columns (translation invariance when column `o` is all ones). -/
lemma cof_colop {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (j o : Fin (m + 1))
    (hoj : o ≠ j) (x : Fin (m + 1) → ℝ) (hxj : x j = 0) (hxo : x o = 0) :
    cof (Matrix.of fun i k => A i k + A i o * x k) j = cof A j := by
  funext i
  rw [cof_eq_det, cof_eq_det]
  have hT : (Matrix.of fun i k => A i k + A i o * x k).updateCol j (Pi.single i 1) =
      A.updateCol j (Pi.single i 1) *
        (1 + Matrix.replicateCol (Fin 1) (Pi.single o (1 : ℝ)) *
          Matrix.replicateRow (Fin 1) x) := by
    ext i' k
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, ← Matrix.mul_assoc]
    have hc : ∀ r, (A.updateCol j (Pi.single i 1) * Matrix.replicateCol (Fin 1)
        (Pi.single o (1 : ℝ))) i' r = A i' o := by
      intro r
      simp [Matrix.mul_apply, Matrix.replicateCol_apply, Pi.single_apply,
        Matrix.updateCol_ne hoj]
    rw [Matrix.mul_apply, Fin.sum_univ_one, hc, Matrix.replicateRow_apply]
    by_cases hk : k = j
    · subst hk; simp [Matrix.updateCol_self, hxj]
    · rw [Matrix.updateCol_ne hk, Matrix.updateCol_ne hk]; simp
  have hd1 : (1 + Matrix.replicateCol (Fin 1) (Pi.single o (1 : ℝ)) *
      Matrix.replicateRow (Fin 1) x).det = 1 := by
    have h := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Fin 1)
      (Pi.single o (1 : ℝ)) x
    calc _ = 1 + x ⬝ᵥ Pi.single o (1 : ℝ) := h
      _ = 1 := by simp [dotProduct, Pi.single_apply, hxo]
  rw [hT, Matrix.det_mul, hd1, mul_one]

/-- C6c linear algebra: if `e_last, a₁ - a₀, …, a_m - a₀` are linearly independent, the graph
matrix of the horizontal parts `Y k = (a k)|_{Fin m}` is invertible. -/
lemma det_ne_of_li {m : ℕ} (a : Fin (m + 1) → EuclideanSpace ℝ (Fin (m + 1)))
    (h : LinearIndependent ℝ (Fin.append ![EuclideanSpace.single (Fin.last m) (1 : ℝ)]
      (fun k : Fin m => a k.succ - a 0))) :
    (gmat (fun k j => a k (Fin.castSucc j))).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set c : Fin m → ℝ := Fin.init v with hcdef
  set t : ℝ := v (Fin.last m) with htdef
  have hvct : v = Fin.snoc c t := (Fin.snoc_init_self v).symm
  have hrow : ∀ k, ∑ j, a k (Fin.castSucc j) * c j + t = 0 := by
    intro k
    have := congrFun hv k
    rw [hvct, gmat_mulVec] at this
    simpa using this
  have hc : c ≠ 0 := by
    intro hc0
    have h0 := hrow 0
    simp [hc0] at h0
    apply hv0
    rw [hvct, hc0, h0]
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  obtain ⟨j0, hj0⟩ : ∃ j0, c j0 ≠ 0 := by
    by_contra hne; simp only [not_exists, not_not] at hne; exact hc (funext hne)
  let φ : EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] ℝ :=
    ∑ j, c j • ((EuclideanSpace.proj (Fin.castSucc j) :
      EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] ℝ) : EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] ℝ)
  have hφ : ∀ x : EuclideanSpace ℝ (Fin (m + 1)), φ x = ∑ j, c j * x (Fin.castSucc j) := by
    intro x; simp [φ]
  have hker : Submodule.span ℝ (Set.range (Fin.append ![EuclideanSpace.single (Fin.last m) (1 : ℝ)]
      (fun k : Fin m => a k.succ - a 0))) ≤ LinearMap.ker φ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hφ]
    refine Fin.addCases (fun l => ?_) (fun k => ?_) i
    · simp only [Fin.append_left]
      have hl : l = 0 := Subsingleton.elim _ _
      subst hl
      simp [EuclideanSpace.single_apply, Fin.castSucc_ne_last]
    · simp only [Fin.append_right, PiLp.sub_apply, mul_sub, Finset.sum_sub_distrib]
      have h1 := hrow k.succ
      have h2 := hrow 0
      simp only [mul_comm (c _)] at h1 h2 ⊢
      linarith
  have hfr := Submodule.finrank_mono hker
  rw [finrank_span_eq_card h] at hfr
  have hrn := LinearMap.finrank_range_add_finrank_ker φ
  rw [finrank_euclideanSpace_fin] at hrn
  have hrange : Module.finrank ℝ (LinearMap.range φ) ≠ 0 := by
    rw [Ne, Submodule.finrank_eq_zero]
    intro hbot
    have : φ (EuclideanSpace.single (Fin.castSucc j0) 1) ∈ LinearMap.range φ := ⟨_, rfl⟩
    rw [hbot, Submodule.mem_bot, hφ] at this
    simp [EuclideanSpace.single_apply] at this
    exact hj0 this
  simp only [Fintype.card_fin] at hfr
  omega

end FSCV


-- ===== GRAPH.lean =====

open MeasureTheory

namespace FSGraph

/-- Rows of `Fin (m+1)` points of `ℝ^{m+1}` in graph coordinates `(Y k, w k)` (last coordinate `w k`). -/
theorem graph_coords {m : ℕ} (G : (Fin (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) → ENNReal)
    (hG : Measurable G) :
    ∫⁻ a, G a = ∫⁻ Y : Fin (m + 1) → Fin m → ℝ, ∫⁻ w : Fin (m + 1) → ℝ,
      G (fun k => WithLp.toLp 2 (Fin.snoc (Y k) (w k) : Fin (m + 1) → ℝ)) := by
  have h1 := (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => (volume : Measure ℝ))
    (Fin.last m)).symm
  have h2 := (PiLp.volume_preserving_toLp (Fin (m + 1))).comp h1
  have hfun : (fun p : ℝ × (Fin m → ℝ) => WithLp.toLp 2 (Fin.snoc p.2 p.1 : Fin (m + 1) → ℝ)) =
      (WithLp.toLp 2) ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ)
        (Fin.last m)).symm := by
    funext p
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
    first | rfl | simp [Fin.snocEquiv]
  have hrow : MeasurePreserving
      (fun p : ℝ × (Fin m → ℝ) => WithLp.toLp 2 (Fin.snoc p.2 p.1 : Fin (m + 1) → ℝ))
      volume volume := by
    rw [hfun]; exact h2
  have hall := volume_preserving_pi (fun _ : Fin (m + 1) => hrow)
  have harr := (measurePreserving_arrowProdEquivProdArrow ℝ (Fin m → ℝ) (Fin (m + 1))
    (fun _ => volume) (fun _ => volume)).symm
  have hΦ := hall.comp harr
  rw [← hΦ.lintegral_comp hG]
  refine (lintegral_prod _ (hG.comp hΦ.measurable).aemeasurable).trans ?_
  rw [lintegral_lintegral_swap]
  · rfl
  · exact (hG.comp hΦ.measurable).aemeasurable

end FSGraph


-- ===== PERV4.lean =====

open MeasureTheory

/-! C6d library: affine change of variables in graph coordinates, (u,h) splitting, height cofactors.
Self-contained (gmat/cof copied from CV.lean with the same definitions). -/

namespace FSC6

noncomputable def gmat {m : ℕ} (y : Fin (m + 1) → Fin m → ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.of fun i => Fin.snoc (y i) 1

noncomputable def cof {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (j i : Fin (m + 1)) : ℝ :=
  (-1) ^ ((i : ℕ) + j) * (A.submatrix i.succAbove j.succAbove).det

lemma det_updateCol_eq {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (j : Fin (m + 1))
    (v : Fin (m + 1) → ℝ) : (A.updateCol j v).det = ∑ i, v i * cof A j i := by
  rw [Matrix.det_succ_column _ j]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsub : (A.updateCol j v).submatrix i.succAbove j.succAbove =
      A.submatrix i.succAbove j.succAbove := by
    ext a b; simp [Matrix.updateCol_ne (Fin.succAbove_ne j b)]
  rw [hsub, Matrix.updateCol_self]; unfold cof; ring

lemma cof_kernel {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (j k : Fin (m + 1))
    (hk : k ≠ j) : ∑ i, A i k * cof A j i = 0 := by
  rw [← det_updateCol_eq]
  exact Matrix.det_zero_of_column_eq hk (fun i => by
    simp [Matrix.updateCol_self, Matrix.updateCol_ne hk])

/-- (a) affine substitution in every row multiplies `det gmat` by `det A`. -/
lemma det_gmat_affine {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (y0 : Fin m → ℝ)
    (ξ : Fin (m + 1) → Fin m → ℝ) :
    (gmat (fun j => y0 + A.mulVec (ξ j))).det = A.det * (gmat ξ).det := by
  set M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := Matrix.of fun l j =>
    Fin.lastCases (motive := fun _ => ℝ) (Fin.snoc (α := fun _ : Fin (m + 1) => ℝ) y0 1 j)
      (fun l' => Fin.snoc (α := fun _ : Fin (m + 1) => ℝ) (fun j' => A j' l') 0 j) l with hM
  have hmul : gmat (fun j => y0 + A.mulVec (ξ j)) = gmat ξ * M := by
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, gmat, Matrix.of_apply, Fin.snoc_castSucc,
      Fin.snoc_last, hM, Fin.lastCases_castSucc, Fin.lastCases_last, one_mul]
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · simp
    · simp [Matrix.mulVec, dotProduct, mul_comm, add_comm]
  have hdetM : M.det = A.det := by
    rw [Matrix.det_succ_column M (Fin.last m), Fin.sum_univ_castSucc]
    have hz : ∀ i : Fin m, M (Fin.castSucc i) (Fin.last m) = 0 := by
      intro i; simp [hM]
    simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
    have hl : M (Fin.last m) (Fin.last m) = 1 := by simp [hM]
    rw [hl, Fin.succAbove_last]
    have hsub : M.submatrix Fin.castSucc Fin.castSucc = A.transpose := by
      ext a b; simp [hM]
    rw [hsub, Matrix.det_transpose]
    simp [← two_mul, pow_mul]
  rw [hmul, Matrix.det_mul, hdetM, mul_comm]

/-- (b) affine change of variables on the row product. -/
theorem cv_pi_affine {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.det ≠ 0) (y0 : Fin m → ℝ)
    (f : (Fin (m + 1) → Fin m → ℝ) → ENNReal) :
    ∫⁻ y, f y = ENNReal.ofReal (|A.det| ^ (m + 1)) *
      ∫⁻ ξ : Fin (m + 1) → Fin m → ℝ, f (fun j => y0 + A.mulVec (ξ j)) := by
  set T : (Fin (m + 1) → Fin m → ℝ) →ₗ[ℝ] (Fin (m + 1) → Fin m → ℝ) :=
    LinearMap.pi (fun i => (Matrix.toLin' A).comp (LinearMap.proj i)) with hT
  have hdetT : LinearMap.det T = A.det ^ (m + 1) := by
    rw [hT, LinearMap.det_pi]; simp [LinearMap.det_toLin']
  have hdet : LinearMap.det T ≠ 0 := by rw [hdetT]; exact pow_ne_zero _ hA
  set e : (Fin (m + 1) → Fin m → ℝ) ≃L[ℝ] (Fin (m + 1) → Fin m → ℝ) :=
    (LinearMap.toContinuousLinearMap T).toContinuousLinearEquivOfDetNeZero hdet with he
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := volume) (f := T) hdet
  have hcoe : ⇑T = ⇑e.toHomeomorph.toMeasurableEquiv := by funext v; rfl
  rw [hcoe] at hmap
  set g : (Fin (m + 1) → Fin m → ℝ) → ENNReal := fun y => f ((fun _ => y0) + y) with hg
  have h0 : ∫⁻ y, f y = ∫⁻ y, g y := by
    rw [hg]; exact (lintegral_add_left_eq_self f (fun _ => y0)).symm
  have h1 : ∫⁻ ξ : Fin (m + 1) → Fin m → ℝ, f (fun j => y0 + A.mulVec (ξ j)) = ∫⁻ ξ : Fin (m + 1) → Fin m → ℝ, g (e.toHomeomorph.toMeasurableEquiv ξ) := by
    refine lintegral_congr fun ξ => ?_
    simp only [hg]
    congr 1
  have h2 : ∫⁻ ξ : Fin (m + 1) → Fin m → ℝ, g (e.toHomeomorph.toMeasurableEquiv ξ) = ∫⁻ w, g w ∂(Measure.map
      (⇑e.toHomeomorph.toMeasurableEquiv) volume) := by
    rw [lintegral_map_equiv]
  rw [h0, h1, h2, hmap, lintegral_smul_measure, hdetT, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), abs_inv, abs_pow, mul_inv_cancel₀ (pow_ne_zero _ (abs_ne_zero.2 hA)),
    ENNReal.ofReal_one, one_mul]

/-- (c0) splitting each row `ξ j ∈ ℝ^{k+2}` as `(u j, h j) ∈ ℝ^{k+1} × ℝ`. -/
theorem split_uh0 {k n : ℕ} (f : (Fin n → Fin (k + 2) → ℝ) → ENNReal) (hf : Measurable f) :
    ∫⁻ ξ, f ξ = ∫⁻ u : Fin n → Fin (k + 1) → ℝ, ∫⁻ h : Fin n → ℝ,
      f (fun j => Fin.snoc (u j) (h j)) := by
  have h1 := (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 2) => (volume : Measure ℝ))
    (Fin.last (k + 1))).symm
  have hfun : (fun p : ℝ × (Fin (k + 1) → ℝ) => (Fin.snoc p.2 p.1 : Fin (k + 2) → ℝ)) =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 2) => ℝ) (Fin.last (k + 1))).symm := by
    funext p
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
    first | rfl | simp [Fin.snocEquiv]
  have hrow : MeasurePreserving
      (fun p : ℝ × (Fin (k + 1) → ℝ) => (Fin.snoc p.2 p.1 : Fin (k + 2) → ℝ)) volume volume := by
    rw [hfun]; exact h1
  have hall := volume_preserving_pi (fun _ : Fin n => hrow)
  have harr := (measurePreserving_arrowProdEquivProdArrow ℝ (Fin (k + 1) → ℝ) (Fin n)
    (fun _ => volume) (fun _ => volume)).symm
  have hΦ := hall.comp harr
  rw [← hΦ.lintegral_comp hf]
  refine (lintegral_prod _ (hf.comp hΦ.measurable).aemeasurable).trans ?_
  rw [lintegral_lintegral_swap]
  · rfl
  · exact (hf.comp hΦ.measurable).aemeasurable

/-- (c) splitting each row `ξ j ∈ ℝ^{k+2}` as `(u j, h j) ∈ E' × ℝ`. -/
theorem split_uh {k n : ℕ} (f : (Fin n → Fin (k + 2) → ℝ) → ENNReal) (hf : Measurable f) :
    ∫⁻ ξ, f ξ = ∫⁻ u : Fin n → EuclideanSpace ℝ (Fin (k + 1)), ∫⁻ h : Fin n → ℝ,
      f (fun j => Fin.snoc (WithLp.ofLp (u j)) (h j)) := by
  rw [split_uh0 f hf]
  have hp : MeasurePreserving (fun u : Fin n → EuclideanSpace ℝ (Fin (k + 1)) => fun j => WithLp.ofLp (u j))
      volume volume := volume_preserving_pi (fun _ : Fin n => PiLp.volume_preserving_ofLp (Fin (k + 1)))
  have he : MeasurableEmbedding (fun u : Fin n → EuclideanSpace ℝ (Fin (k + 1)) => fun j => WithLp.ofLp (u j)) :=
    (MeasurableEquiv.piCongrRight (fun _ : Fin n => (MeasurableEquiv.toLp 2 (Fin (k + 1) → ℝ)).symm)).measurableEmbedding
  exact (hp.lintegral_comp_emb he (fun u => ∫⁻ h : Fin n → ℝ, f (fun j => Fin.snoc (u j) (h j)))).symm

/-- (d) height cofactors: `det gmat (u, h) = Σ hᵢ Cᵢ(u)`. -/
noncomputable def hcof {k : ℕ} (u : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1))) : Fin (k + 3) → ℝ :=
  cof (gmat (fun j => (Fin.snoc (WithLp.ofLp (u j)) (0 : ℝ) : Fin (k + 2) → ℝ)))
    (Fin.castSucc (Fin.last (k + 1)))

lemma det_snoc_h {k : ℕ} (u : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1))) (h : Fin (k + 3) → ℝ) :
    (gmat (fun j => (Fin.snoc (WithLp.ofLp (u j)) (h j) : Fin (k + 2) → ℝ))).det =
      ∑ i, h i * hcof u i := by
  have hupd : gmat (fun j => (Fin.snoc (WithLp.ofLp (u j)) (h j) : Fin (k + 2) → ℝ)) =
      (gmat (fun j => (Fin.snoc (WithLp.ofLp (u j)) (0 : ℝ) : Fin (k + 2) → ℝ))).updateCol
        (Fin.castSucc (Fin.last (k + 1))) h := by
    ext i l
    induction l using Fin.lastCases with
    | last =>
      rw [Matrix.updateCol_ne (show Fin.last (k + 2) ≠ Fin.castSucc (Fin.last (k + 1)) from by
        simp [Fin.ext_iff])]
      simp [gmat]
    | cast l' =>
      induction l' using Fin.lastCases with
      | last => simp [gmat]
      | cast l'' =>
        rw [Matrix.updateCol_ne (show Fin.castSucc (Fin.castSucc l'') ≠ Fin.castSucc (Fin.last (k + 1))
          from by simp [Fin.ext_iff]; omega)]
        simp [gmat]
  rw [hupd, det_updateCol_eq]; rfl

lemma hcof_sum {k : ℕ} (u : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1))) :
    ∑ i, hcof u i = 0 := by
  have := cof_kernel (gmat (fun j => (Fin.snoc (WithLp.ofLp (u j)) (0 : ℝ) : Fin (k + 2) → ℝ)))
    (Fin.castSucc (Fin.last (k + 1))) (Fin.last (k + 2)) (by simp [Fin.ext_iff])
  simpa [gmat, hcof] using this

lemma hcof_kernel {k : ℕ} (u : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1))) :
    ∑ i, hcof u i • u i = 0 := by
  ext l
  have := cof_kernel (gmat (fun j => (Fin.snoc (WithLp.ofLp (u j)) (0 : ℝ) : Fin (k + 2) → ℝ)))
    (Fin.castSucc (Fin.last (k + 1))) (Fin.castSucc (Fin.castSucc l))
    (by simp [Fin.ext_iff]; omega)
  simp only [gmat, Matrix.of_apply, Fin.snoc_castSucc] at this
  rw [WithLp.ofLp_sum]
  simp only [Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, WithLp.ofLp_zero,
    Pi.zero_apply]
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [hcof, gmat, mul_comm]

end FSC6

open MeasureTheory Module
open scoped RealInnerProductSpace

set_option autoImplicit false

/-! C6d(e): an orthonormal frame `(ι, ω)` of the hyperplane `H_v` (graph of `x ↦ ⟪x, c⟫ + t`)
with `ω` spanning `dir H_v ∩ W`, and the affine matrix change `Pt (y0 + A ξ) = o + ι u + h ω`. -/

namespace FSFrame

/-- Linear part of the graph map: `x ↦ (x, Σ xᵢ cᵢ)`. -/
noncomputable def Lc {k : ℕ} (c : Fin (k + 2) → ℝ) :
    (Fin (k + 2) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin (k + 3)) where
  toFun x := WithLp.toLp 2 (Fin.snoc x (∑ i, x i * c i) : Fin (k + 3) → ℝ)
  map_add' x y := by
    ext j
    induction j using Fin.lastCases with
    | last => simp [Finset.sum_add_distrib, add_mul]
    | cast j => simp
  map_smul' a x := by
    ext j
    induction j using Fin.lastCases with
    | last => simp [Finset.mul_sum, mul_assoc]
    | cast j => simp

/-- First `k+2` coordinates. -/
noncomputable def piL (k : ℕ) : EuclideanSpace ℝ (Fin (k + 3)) →ₗ[ℝ] (Fin (k + 2) → ℝ) where
  toFun p i := WithLp.ofLp p (Fin.castSucc i)
  map_add' p q := by funext i; simp
  map_smul' a p := by funext i; simp

/-- The graph point `(x, Σ xᵢ cᵢ + t)` (the row `toLp (snoc (Y k) (w k))` of `cv_graph`). -/
noncomputable def Pt {k : ℕ} (c : Fin (k + 2) → ℝ) (t : ℝ) (x : Fin (k + 2) → ℝ) :
    EuclideanSpace ℝ (Fin (k + 3)) :=
  WithLp.toLp 2 (Fin.snoc x (∑ i, x i * c i + t) : Fin (k + 3) → ℝ)

lemma piL_Lc {k : ℕ} (c : Fin (k + 2) → ℝ) (x : Fin (k + 2) → ℝ) : piL k (Lc c x) = x := by
  funext i; simp [piL, Lc]

lemma Lc_piL {k : ℕ} (c : Fin (k + 2) → ℝ) (p : EuclideanSpace ℝ (Fin (k + 3)))
    (hp : p ∈ LinearMap.range (Lc c)) : Lc c (piL k p) = p := by
  obtain ⟨x, rfl⟩ := hp; rw [piL_Lc]

lemma Pt_eq {k : ℕ} (c : Fin (k + 2) → ℝ) (t : ℝ) (x : Fin (k + 2) → ℝ) :
    Pt c t x = Lc c x + Pt c t 0 := by
  ext j
  induction j using Fin.lastCases with
  | last => simp [Pt, Lc]
  | cast j => simp [Pt, Lc]

lemma Lc_injective {k : ℕ} (c : Fin (k + 2) → ℝ) : Function.Injective (Lc c) :=
  fun x y h => by rw [← piL_Lc c x, h, piL_Lc]

theorem frame {k : ℕ} (c : Fin (k + 2) → ℝ) (t : ℝ)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin (k + 3)))) (hW : finrank ℝ W = 2)
    (hK : finrank ℝ ↥(LinearMap.range (Lc c) ⊓ W) = 1) :
    ∃ (o ω : EuclideanSpace ℝ (Fin (k + 3)))
      (ι : EuclideanSpace ℝ (Fin (k + 1)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k + 3)))
      (A : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ) (y0 : Fin (k + 2) → ℝ),
      A.det ≠ 0 ∧ o ∈ W ∧ ω ∈ W ∧ ‖ω‖ = 1 ∧ (∀ x, ⟪ι x, ω⟫ = 0) ∧
      (∀ u (h : ℝ), Pt c t (y0 + A.mulVec (Fin.snoc (WithLp.ofLp u) h)) = o + ι u + h • ω) ∧
      (∀ x (h : ℝ), o + ι x + h • ω ∈ W → x = 0) := by
  classical
  set R := LinearMap.range (Lc c) with hR
  set K := R ⊓ W with hKdef
  -- ω
  obtain ⟨w0, hw0K, hw0⟩ : ∃ w0 ∈ K, w0 ≠ 0 := by
    have hpos : 0 < finrank ℝ K := by rw [hK]; norm_num
    obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    exact ⟨x, x.2, fun h => hx (Subtype.ext h)⟩
  set ω : EuclideanSpace ℝ (Fin (k + 3)) := ‖w0‖⁻¹ • w0 with hωdef
  have hωK : ω ∈ K := K.smul_mem _ hw0K
  have hωn : ‖ω‖ = 1 := by
    rw [hωdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw0)]
  have hω0 : ω ≠ 0 := by intro h; rw [h, norm_zero] at hωn; exact zero_ne_one hωn
  have hωR : ω ∈ R := (Submodule.mem_inf.mp hωK).1
  have hωW : ω ∈ W := (Submodule.mem_inf.mp hωK).2
  clear_value ω
  have hKspan : ∀ v ∈ K, ∃ a : ℝ, v = a • ω := by
    intro v hv
    have hω0' : (⟨ω, hωK⟩ : K) ≠ 0 := by
      intro h; exact hω0 (congrArg Subtype.val h)
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨ω, hωK⟩ : K) hω0').mp hK ⟨v, hv⟩
    exact ⟨a, (congrArg Subtype.val ha).symm⟩
  -- R and F
  have hRr : finrank ℝ R = k + 2 := by
    rw [hR, LinearMap.finrank_range_of_inj (Lc_injective c)]; simp
  have hspan_le : (ℝ ∙ ω) ≤ R := (Submodule.span_singleton_le_iff_mem _ _).mpr hωR
  set F := (ℝ ∙ ω)ᗮ ⊓ R with hFdef
  have hF : finrank ℝ F = k + 1 := by
    have h := Submodule.finrank_add_inf_finrank_orthogonal hspan_le
    rw [← hFdef, finrank_span_singleton hω0, hRr] at h; omega
  set b := (stdOrthonormalBasis ℝ F).reindex (finCongr hF) with hb
  set ι : EuclideanSpace ℝ (Fin (k + 1)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k + 3)) :=
    F.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry with hι
  have hιF : ∀ x, ι x ∈ F := fun x => (b.repr.symm x).2
  have hιω : ∀ x, ⟪ι x, ω⟫ = 0 := by
    intro x
    have h1 := (Submodule.mem_inf.mp (hιF x)).1
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at h1
    rw [real_inner_comm]; exact h1
  have hιR : ∀ x, ι x ∈ R := fun x => (Submodule.mem_inf.mp (hιF x)).2
  -- o
  have hsup : W ⊔ R = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h := Submodule.finrank_sup_add_finrank_inf_eq W R
    have hWR : W ⊓ R = K := inf_comm W R
    rw [hWR, hK, hW, hRr] at h
    rw [finrank_euclideanSpace_fin]; omega
  have hP0 : Pt c t 0 ∈ W ⊔ R := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨o, ho, r, hr, hor⟩ := Submodule.mem_sup.mp hP0
  obtain ⟨xr, rfl⟩ := hr
  have hPy0 : Pt c t (-xr) = o := by
    rw [Pt_eq, map_neg, ← hor]; abel
  -- Φ
  let Φl : (Fin (k + 2) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin (k + 3)) :=
    { toFun := fun ξ => ι (WithLp.toLp 2 (fun i => ξ (Fin.castSucc i))) + ξ (Fin.last (k + 1)) • ω
      map_add' := fun x y => by
        have : (WithLp.toLp 2 (fun i => (x + y) (Fin.castSucc i)) : EuclideanSpace ℝ (Fin (k + 1))) =
            WithLp.toLp 2 (fun i => x (Fin.castSucc i)) + WithLp.toLp 2 (fun i => y (Fin.castSucc i)) := by
          ext i; simp
        rw [this, map_add, Pi.add_apply, add_smul]; abel
      map_smul' := fun a x => by
        have : (WithLp.toLp 2 (fun i => (a • x) (Fin.castSucc i)) : EuclideanSpace ℝ (Fin (k + 1))) =
            a • WithLp.toLp 2 (fun i => x (Fin.castSucc i)) := by
          ext i; simp
        rw [this, map_smul, Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add] }
  have hΦR : ∀ ξ, Φl ξ ∈ R := fun ξ => R.add_mem (hιR _) (R.smul_mem _ hωR)
  set A := LinearMap.toMatrix' ((piL k).comp Φl) with hA
  have hAξ : ∀ ξ, Lc c (A.mulVec ξ) = Φl ξ := by
    intro ξ
    rw [hA, LinearMap.toMatrix'_mulVec, LinearMap.comp_apply, Lc_piL c _ (hΦR ξ)]
  have hinjΦ : Function.Injective ((piL k).comp Φl) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ξ hξ
    have h0 : Φl ξ = 0 := by
      rw [← Lc_piL c _ (hΦR ξ)]
      have : piL k (Φl ξ) = 0 := hξ
      rw [this, map_zero]
    have hlast : ξ (Fin.last (k + 1)) = 0 := by
      have h1 : ⟪Φl ξ, ω⟫ = 0 := by rw [h0, inner_zero_left]
      change ⟪ι (WithLp.toLp 2 (fun i => ξ (Fin.castSucc i))) + ξ (Fin.last (k + 1)) • ω, ω⟫ = 0 at h1
      rw [inner_add_left, hιω, inner_smul_left, real_inner_self_eq_norm_sq, hωn] at h1
      simpa using h1
    have hinit : ι (WithLp.toLp 2 (fun i => ξ (Fin.castSucc i))) = 0 := by
      have : Φl ξ = ι (WithLp.toLp 2 (fun i => ξ (Fin.castSucc i))) + ξ (Fin.last (k + 1)) • ω := rfl
      rw [this, hlast, zero_smul, add_zero] at h0; exact h0
    have hinit' : (WithLp.toLp 2 (fun i => ξ (Fin.castSucc i)) : EuclideanSpace ℝ (Fin (k + 1))) = 0 :=
      ι.injective (by rw [hinit, map_zero])
    funext j
    induction j using Fin.lastCases with
    | last => exact hlast
    | cast j =>
      have := congrArg (fun p : EuclideanSpace ℝ (Fin (k + 1)) => WithLp.ofLp p j) hinit'
      simpa using this
  have hdet : A.det ≠ 0 := by
    have hinj : Function.Injective (Matrix.toLin' A) := by
      rw [hA, Matrix.toLin'_toMatrix']; exact hinjΦ
    have hu := (LinearEquiv.ofInjectiveEndo (Matrix.toLin' A) hinj).isUnit_det'
    change IsUnit (LinearMap.det (Matrix.toLin' A)) at hu
    rw [LinearMap.det_toLin'] at hu
    exact hu.ne_zero
  refine ⟨o, ω, ι, A, -xr, hdet, ho, hωW, hωn, hιω, ?_, ?_⟩
  · intro u h
    rw [Pt_eq, map_add, hAξ, add_right_comm, ← Pt_eq, hPy0, add_assoc]
    congr 1
    change ι (WithLp.toLp 2 (fun i => (Fin.snoc (WithLp.ofLp u) h : Fin (k + 2) → ℝ) (Fin.castSucc i))) +
      (Fin.snoc (WithLp.ofLp u) h : Fin (k + 2) → ℝ) (Fin.last (k + 1)) • ω = ι u + h • ω
    simp
  · intro x h hW'
    have hmemW : ι x + h • ω ∈ W := by
      have := W.sub_mem hW' ho
      rwa [add_assoc, add_sub_cancel_left] at this
    have hmemR : ι x + h • ω ∈ R := R.add_mem (hιR x) (R.smul_mem _ hωR)
    obtain ⟨a, ha⟩ := hKspan _ (Submodule.mem_inf.mpr ⟨hmemR, hmemW⟩)
    have h1 : ⟪ι x + h • ω, ω⟫ = ⟪a • ω, ω⟫ := by rw [ha]
    rw [inner_add_left, hιω, inner_smul_left, inner_smul_left, real_inner_self_eq_norm_sq, hωn] at h1
    simp at h1
    rw [h1] at ha
    have : ι x = 0 := by
      have := congrArg (fun p => p - a • ω) ha
      simpa using this
    exact ι.injective (by rw [this, map_zero])

end FSFrame

namespace FSPerV
open FSC6 FSFrame

lemma gmat_continuous {m : ℕ} : Continuous fun y : Fin (m + 1) → Fin m → ℝ => FSC6.gmat y := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp only [FSC6.gmat, Matrix.of_apply, Fin.snoc_last]; exact continuous_const
  · simp only [FSC6.gmat, Matrix.of_apply, Fin.snoc_castSucc]
    exact (continuous_apply k).comp (continuous_apply i)

lemma Pt_continuous {k : ℕ} (c : Fin (k + 2) → ℝ) (t : ℝ) : Continuous (Pt c t) := by
  have : Pt c t = fun x => Lc c x + Pt c t 0 := funext (Pt_eq c t)
  rw [this]
  exact (Lc c).continuous_of_finiteDimensional.add continuous_const

/-- C6d per hyperplane: graph coordinates `Y` over `H_v` become frame coordinates `(u, h)`;
the Jacobian `|det gmat Y|` becomes `K · |Σ hᵢ Cᵢ(u)|` with a constant `0 < K < ∞`. -/
theorem per_v {k : ℕ} (c : Fin (k + 2) → ℝ) (t : ℝ)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin (k + 3)))) (hW : Module.finrank ℝ W = 2)
    (hK : Module.finrank ℝ ↥(LinearMap.range (Lc c) ⊓ W) = 1) :
    ∃ (o ω : EuclideanSpace ℝ (Fin (k + 3)))
      (ι : EuclideanSpace ℝ (Fin (k + 1)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k + 3))) (K : ENNReal),
      K ≠ 0 ∧ K ≠ ⊤ ∧ o ∈ W ∧ ω ∈ W ∧ ‖ω‖ = 1 ∧ (∀ x, ⟪ι x, ω⟫ = 0) ∧
      (∀ x (h : ℝ), o + ι x + h • ω ∈ W → x = 0) ∧
      ∀ G : (Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 3))) → ENNReal, Measurable G →
        ∫⁻ y : Fin (k + 3) → Fin (k + 2) → ℝ,
            ENNReal.ofReal |(FSC6.gmat y).det| * G (fun j => Pt c t (y j)) =
          K * ∫⁻ u : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1)), ∫⁻ h : Fin (k + 3) → ℝ,
            ENNReal.ofReal |∑ i, h i * hcof u i| * G (fun j => o + ι (u j) + h j • ω) := by
  obtain ⟨o, ω, ι, A, y0, hdet, ho, hωW, hωn, hιω, hPt, hW0⟩ := frame c t W hW hK
  refine ⟨o, ω, ι, ENNReal.ofReal (|A.det| ^ (k + 2 + 1)) * ENNReal.ofReal |A.det|, ?_, ?_, ho, hωW,
    hωn, hιω, hW0, ?_⟩
  · have h1 : 0 < |A.det| := abs_pos.mpr hdet
    exact mul_ne_zero (by simp [ENNReal.ofReal_eq_zero, not_le, hdet])
      (by simp [ENNReal.ofReal_eq_zero, not_le, h1, hdet])
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  intro G hG
  rw [cv_pi_affine A hdet y0]
  have hdg : ∀ ξ : Fin (k + 3) → Fin (k + 2) → ℝ,
      ENNReal.ofReal |(FSC6.gmat (fun j => y0 + A.mulVec (ξ j))).det| =
        ENNReal.ofReal |A.det| * ENNReal.ofReal |(FSC6.gmat ξ).det| := by
    intro ξ
    rw [det_gmat_affine, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
  simp_rw [hdg, mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hmeas : Measurable fun ξ : Fin (k + 3) → Fin (k + 2) → ℝ =>
      ENNReal.ofReal |(FSC6.gmat ξ).det| * G (fun j => Pt c t (y0 + A.mulVec (ξ j))) := by
    refine Measurable.mul ?_ ?_
    · exact ENNReal.measurable_ofReal.comp
        ((continuous_abs.comp ((continuous_id.matrix_det).comp gmat_continuous)).measurable)
    · refine hG.comp (Continuous.measurable ?_)
      refine continuous_pi fun j => (Pt_continuous c t).comp ?_
      refine continuous_const.add ?_
      exact (Matrix.toLin' A).continuous_of_finiteDimensional.comp (continuous_apply j)
  have hI : ∫⁻ ξ : Fin (k + 3) → Fin (k + 2) → ℝ,
      ENNReal.ofReal |(FSC6.gmat ξ).det| * G (fun j => Pt c t (y0 + A.mulVec (ξ j))) =
      ∫⁻ u : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1)), ∫⁻ h : Fin (k + 3) → ℝ,
        ENNReal.ofReal |∑ i, h i * hcof u i| * G (fun j => o + ι (u j) + h j • ω) := by
    rw [split_uh _ hmeas]
    refine lintegral_congr fun u => lintegral_congr fun h => ?_
    rw [det_snoc_h]
    congr 2
    funext j
    exact hPt (u j) (h j)
  rw [hI]


theorem per_v' {k : ℕ} (c : Fin (k + 2) → ℝ) (t : ℝ)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin (k + 3)))) (hW : Module.finrank ℝ W = 2)
    (hK : Module.finrank ℝ ↥(LinearMap.range (Lc c) ⊓ W) = 1) :
    ∃ (o ω : EuclideanSpace ℝ (Fin (k + 3)))
      (ι : EuclideanSpace ℝ (Fin (k + 1)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k + 3))) (K : ENNReal),
      K ≠ 0 ∧ K ≠ ⊤ ∧ o ∈ W ∧ ω ∈ W ∧ ‖ω‖ = 1 ∧ (∀ x, ⟪ι x, ω⟫ = 0) ∧
      (∀ x (h : ℝ), o + ι x + h • ω ∈ W → x = 0) ∧
      (∀ x (h : ℝ), ∃ y, Pt c t y = o + ι x + h • ω) ∧
      ∀ G : (Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 3))) → ENNReal, Measurable G →
        ∫⁻ y : Fin (k + 3) → Fin (k + 2) → ℝ,
            ENNReal.ofReal |(FSC6.gmat y).det| * G (fun j => Pt c t (y j)) =
          K * ∫⁻ u : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1)), ∫⁻ h : Fin (k + 3) → ℝ,
            ENNReal.ofReal |∑ i, h i * hcof u i| * G (fun j => o + ι (u j) + h j • ω) := by
  obtain ⟨o, ω, ι, A, y0, hdet, ho, hωW, hωn, hιω, hPt, hW0⟩ := frame c t W hW hK
  refine ⟨o, ω, ι, ENNReal.ofReal (|A.det| ^ (k + 2 + 1)) * ENNReal.ofReal |A.det|, ?_, ?_, ho, hωW,
    hωn, hιω, hW0, fun x h => ⟨_, hPt x h⟩, ?_⟩
  · have h1 : 0 < |A.det| := abs_pos.mpr hdet
    exact mul_ne_zero (by simp [ENNReal.ofReal_eq_zero, not_le, hdet])
      (by simp [ENNReal.ofReal_eq_zero, not_le, h1, hdet])
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  intro G hG
  rw [cv_pi_affine A hdet y0]
  have hdg : ∀ ξ : Fin (k + 3) → Fin (k + 2) → ℝ,
      ENNReal.ofReal |(FSC6.gmat (fun j => y0 + A.mulVec (ξ j))).det| =
        ENNReal.ofReal |A.det| * ENNReal.ofReal |(FSC6.gmat ξ).det| := by
    intro ξ
    rw [det_gmat_affine, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
  simp_rw [hdg, mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hmeas : Measurable fun ξ : Fin (k + 3) → Fin (k + 2) → ℝ =>
      ENNReal.ofReal |(FSC6.gmat ξ).det| * G (fun j => Pt c t (y0 + A.mulVec (ξ j))) := by
    refine Measurable.mul ?_ ?_
    · exact ENNReal.measurable_ofReal.comp
        ((continuous_abs.comp ((continuous_id.matrix_det).comp gmat_continuous)).measurable)
    · refine hG.comp (Continuous.measurable ?_)
      refine continuous_pi fun j => (Pt_continuous c t).comp ?_
      refine continuous_const.add ?_
      exact (Matrix.toLin' A).continuous_of_finiteDimensional.comp (continuous_apply j)
  have hI : ∫⁻ ξ : Fin (k + 3) → Fin (k + 2) → ℝ,
      ENNReal.ofReal |(FSC6.gmat ξ).det| * G (fun j => Pt c t (y0 + A.mulVec (ξ j))) =
      ∫⁻ u : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1)), ∫⁻ h : Fin (k + 3) → ℝ,
        ENNReal.ofReal |∑ i, h i * hcof u i| * G (fun j => o + ι (u j) + h j • ω) := by
    rw [split_uh _ hmeas]
    refine lintegral_congr fun u => lintegral_congr fun h => ?_
    rw [det_snoc_h]
    congr 2
    funext j
    exact hPt (u j) (h j)
  rw [hI]


end FSPerV

namespace FSC6E
open FSC6

lemma cof_eq_det {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (j i : Fin (m + 1)) :
    cof A j i = (A.updateCol j (Pi.single i 1)).det := by
  rw [det_updateCol_eq]; simp [Pi.single_apply]

lemma cof_colop {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (j o : Fin (m + 1))
    (hoj : o ≠ j) (x : Fin (m + 1) → ℝ) (hxj : x j = 0) (hxo : x o = 0) :
    cof (Matrix.of fun i k => A i k + A i o * x k) j = cof A j := by
  funext i
  rw [cof_eq_det, cof_eq_det]
  have hT : (Matrix.of fun i k => A i k + A i o * x k).updateCol j (Pi.single i 1) =
      A.updateCol j (Pi.single i 1) *
        (1 + Matrix.replicateCol (Fin 1) (Pi.single o (1 : ℝ)) *
          Matrix.replicateRow (Fin 1) x) := by
    ext i' k
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, ← Matrix.mul_assoc]
    have hc : ∀ r, (A.updateCol j (Pi.single i 1) * Matrix.replicateCol (Fin 1)
        (Pi.single o (1 : ℝ))) i' r = A i' o := by
      intro r
      simp [Matrix.mul_apply, Matrix.replicateCol_apply, Pi.single_apply,
        Matrix.updateCol_ne hoj]
    rw [Matrix.mul_apply, Fin.sum_univ_one, hc, Matrix.replicateRow_apply]
    by_cases hk : k = j
    · subst hk; simp [Matrix.updateCol_self, hxj]
    · rw [Matrix.updateCol_ne hk, Matrix.updateCol_ne hk]; simp
  have hd1 : (1 + Matrix.replicateCol (Fin 1) (Pi.single o (1 : ℝ)) *
      Matrix.replicateRow (Fin 1) x).det = 1 := by
    have h := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Fin 1)
      (Pi.single o (1 : ℝ)) x
    calc _ = 1 + x ⬝ᵥ Pi.single o (1 : ℝ) := h
      _ = 1 := by simp [dotProduct, Pi.single_apply, hxo]
  rw [hT, Matrix.det_mul, hd1, mul_one]

/-- Height cofactors are translation invariant. -/
lemma hcof_translate {k : ℕ} (x : EuclideanSpace ℝ (Fin (k + 1)))
    (s : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1))) :
    hcof (fun j => x + s j) = hcof s := by
  unfold hcof
  set x' : Fin (k + 3) → ℝ :=
    Fin.snoc (Fin.snoc (WithLp.ofLp x) (0 : ℝ) : Fin (k + 2) → ℝ) (0 : ℝ) with hx'
  have hM : gmat (fun j => (Fin.snoc (WithLp.ofLp (x + s j)) (0 : ℝ) : Fin (k + 2) → ℝ)) =
      Matrix.of fun i l =>
        gmat (fun j => (Fin.snoc (WithLp.ofLp (s j)) (0 : ℝ) : Fin (k + 2) → ℝ)) i l +
        gmat (fun j => (Fin.snoc (WithLp.ofLp (s j)) (0 : ℝ) : Fin (k + 2) → ℝ)) i
          (Fin.last (k + 2)) * x' l := by
    ext i l
    induction l using Fin.lastCases with
    | last => simp [gmat, hx']
    | cast l' =>
      induction l' using Fin.lastCases with
      | last => simp [gmat, hx']
      | cast l'' => simp [gmat, hx', add_comm]
  rw [hM, cof_colop _ _ (Fin.last (k + 2)) (by simp [Fin.ext_iff]) x' (by simp [hx'])
    (by simp [hx'])]

/-- The normalised height cofactors `z = C / ‖C‖₁`. -/
noncomputable def zc {k : ℕ} (u : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1))) : Fin (k + 3) → ℝ :=
  fun i => hcof u i / ∑ j, |hcof u j|

/-- Normalised kernel combination of the shape `s = u - u 0` from nonzero height cofactors. -/
lemma kernel_comb {k : ℕ} (u : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1)))
    (hC : hcof u ≠ 0) :
    (∑ i, zc u i • (u i - u 0) = 0) ∧ (∑ i, zc u i = 0) ∧ (∑ i, |zc u i| = 1) := by
  simp only [zc]
  have hpos : 0 < ∑ j, |hcof u j| := by
    obtain ⟨i, hi⟩ : ∃ i, hcof u i ≠ 0 := Function.ne_iff.mp hC
    exact lt_of_lt_of_le (abs_pos.mpr hi)
      (Finset.single_le_sum (fun j _ => abs_nonneg (hcof u j)) (Finset.mem_univ i))
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, div_eq_mul_inv, mul_comm _ (_⁻¹),
      ← smul_smul, ← Finset.smul_sum, ← Finset.mul_sum, hcof_kernel, hcof_sum, mul_zero, zero_smul,
      smul_zero, sub_zero]
  · rw [← Finset.sum_div, hcof_sum, zero_div]
  · simp_rw [abs_div, abs_of_pos hpos]
    rw [← Finset.sum_div, div_self hpos.ne']

lemma abs_sum_eq {k : ℕ} (u : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1))) (h : Fin (k + 3) → ℝ) :
    |∑ i, h i * hcof u i| = (∑ j, |hcof u j|) * |∑ i, zc u i * h i| := by
  simp only [zc]
  by_cases hz : ∑ j, |hcof u j| = 0
  · have h0 : ∀ j, hcof u j = 0 := fun j => abs_eq_zero.mp
      ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg (hcof u j))).mp hz j
        (Finset.mem_univ j))
    simp [h0]
  · have hpos : 0 < ∑ j, |hcof u j| :=
      lt_of_le_of_ne (Finset.sum_nonneg fun j _ => abs_nonneg _) (Ne.symm hz)
    rw [← abs_of_pos hpos, ← abs_mul, abs_of_pos hpos]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp

/-- C6e shift/shape coordinates: `u 0 = x`, `u (j+1) = x + s' j`. -/
theorem shift_shape {k : ℕ} (F : (Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1))) → ENNReal)
    (hF : Measurable F) :
    ∫⁻ u, F u = ∫⁻ x : EuclideanSpace ℝ (Fin (k + 1)), ∫⁻ s' : Fin (k + 2) → EuclideanSpace ℝ (Fin (k + 1)),
      F (Fin.cons x (fun j => x + s' j)) := by
  have hmp := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (k + 3) => (volume : Measure (EuclideanSpace ℝ (Fin (k + 1))))) 0).symm
  refine (hmp.lintegral_comp hF).symm.trans ?_
  refine (lintegral_prod _ (hF.comp hmp.measurable).aemeasurable).trans ?_
  refine lintegral_congr fun x => ?_
  have h := lintegral_add_left_eq_self
    (μ := (volume : Measure (Fin (k + 2) → EuclideanSpace ℝ (Fin (k + 1)))))
    (fun s' => F ((MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (k + 3) => EuclideanSpace ℝ (Fin (k + 1))) 0).symm (x, s'))) (fun _ => x)
  refine h.symm.trans ?_
  refine lintegral_congr fun s' => ?_
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_zero']
  rfl

end FSC6E

namespace FSC6R
open FSC6 FSC6E

lemma dual_expand {k : ℕ} (f : Module.Dual ℝ (EuclideanSpace ℝ (Fin (k + 1))))
    (x : EuclideanSpace ℝ (Fin (k + 1))) :
    f x = ∑ m, x m * f (EuclideanSpace.single m 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).toBasis.sum_repr x]
  simp [map_sum]

/-- C6e-rest: nonzero height cofactors force the shape to span the whole frame. -/
theorem rank_of_hcof {k : ℕ} (u : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1)))
    (hC : hcof u ≠ 0) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range fun i => u i - u 0)) = k + 1 := by
  obtain ⟨i, hi⟩ : ∃ i, hcof u i ≠ 0 := Function.ne_iff.mp hC
  set A := gmat (fun j => (Fin.snoc (WithLp.ofLp (u j)) (0 : ℝ) : Fin (k + 2) → ℝ)) with hA
  have hB : (A.updateCol (Fin.castSucc (Fin.last (k + 1))) (Pi.single i 1)).det ≠ 0 := by
    rw [← cof_eq_det]; exact hi
  set p := Submodule.span ℝ (Set.range fun i => u i - u 0) with hp
  have htop : p = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hfp⟩ := Submodule.exists_le_ker_of_lt_top p (lt_top_iff_ne_top.mpr hne)
    have hfs : ∀ l, f (u l) = f (u 0) := by
      intro l
      have hmem : u l - u 0 ∈ p := Submodule.subset_span ⟨l, rfl⟩
      have := hfp hmem
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
      exact this
    set φ : Fin (k + 1) → ℝ := fun m => f (EuclideanSpace.single m 1) with hφ
    set w : Fin (k + 3) → ℝ := Fin.snoc (Fin.snoc φ (0 : ℝ) : Fin (k + 2) → ℝ) (-f (u 0)) with hw
    have hBw : Matrix.mulVec (A.updateCol (Fin.castSucc (Fin.last (k + 1))) (Pi.single i 1)) w = 0 := by
      funext l
      simp only [Matrix.mulVec, dotProduct]
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      have h1 : ∀ m : Fin (k + 1),
          (A.updateCol (Fin.castSucc (Fin.last (k + 1))) (Pi.single i 1)) l
            (Fin.castSucc (Fin.castSucc m)) * w (Fin.castSucc (Fin.castSucc m)) =
            u l m * φ m := by
        intro m
        rw [Matrix.updateCol_ne (by simp [Fin.ext_iff]; omega)]
        simp [hA, gmat, hw]
      simp_rw [h1]
      rw [Matrix.updateCol_self, Matrix.updateCol_ne (by simp [Fin.ext_iff])]
      simp only [hA, gmat, Matrix.of_apply, Fin.snoc_last, hw, Fin.snoc_castSucc, mul_zero,
        add_zero, one_mul, Pi.zero_apply]
      rw [← dual_expand, hfs l, add_neg_cancel]
    have hw0 := Matrix.eq_zero_of_mulVec_eq_zero hB hBw
    apply hf0
    refine (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).toBasis.ext fun m => ?_
    have := congrFun hw0 (Fin.castSucc (Fin.castSucc m))
    simp only [hw, Fin.snoc_castSucc, Pi.zero_apply, hφ] at this
    simpa using this
  rw [htop, finrank_top, finrank_euclideanSpace_fin]

end FSC6R

/-! C8 prep: in the frame `b i = o + ι (u i) + h i • ω`, a nonzero Jacobian weight makes the rows
span the hyperplane; then `dir(aff b) ⊓ W = ℝ ∙ ω` and the D-projection is the `u`-difference. -/
namespace FSDir
open FSC6 FSC6E FSC6R
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem span_full {k : ℕ} (o ω : V) (ι : EuclideanSpace ℝ (Fin (k + 1)) →ₗᵢ[ℝ] V)
    (u : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1))) (h : Fin (k + 3) → ℝ)
    (hdet : ∑ i, h i * hcof u i ≠ 0) (x : EuclideanSpace ℝ (Fin (k + 1))) (t : ℝ) :
    ι x + t • ω ∈ Submodule.span ℝ (Set.range fun i =>
      (o + ι (u i) + h i • ω) - (o + ι (u 0) + h 0 • ω)) := by
  by_contra hx
  obtain ⟨f, hfx, hfp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  set φ : Module.Dual ℝ (EuclideanSpace ℝ (Fin (k + 1))) := f.comp ι.toLinearMap with hφ
  set γ := f ω with hγ
  have hfv : ∀ i, φ (u i) - φ (u 0) + γ * (h i - h 0) = 0 := by
    intro i
    have hmem : (o + ι (u i) + h i • ω) - (o + ι (u 0) + h 0 • ω) ∈
        Submodule.span ℝ (Set.range fun i =>
          (o + ι (u i) + h i • ω) - (o + ι (u 0) + h 0 • ω)) := Submodule.subset_span ⟨i, rfl⟩
    have := Submodule.mem_map_of_mem (f := f) hmem
    rw [hfp, Submodule.mem_bot] at this
    rw [← this]
    simp only [hφ, hγ, LinearMap.comp_apply, map_sub, map_add, map_smul, smul_eq_mul]
    simp
    ring
  set M := gmat (fun j => (Fin.snoc (WithLp.ofLp (u j)) (h j) : Fin (k + 2) → ℝ)) with hM
  have hMdet : M.det ≠ 0 := by rw [hM, det_snoc_h]; exact hdet
  set ψ : Fin (k + 1) → ℝ := fun m => φ (EuclideanSpace.single m 1) with hψ
  set w : Fin (k + 3) → ℝ :=
    Fin.snoc (Fin.snoc ψ γ : Fin (k + 2) → ℝ) (-(φ (u 0) + γ * h 0)) with hw
  have hMw : Matrix.mulVec M w = 0 := by
    funext l
    simp only [Matrix.mulVec, dotProduct]
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [hM, gmat, Matrix.of_apply, Fin.snoc_castSucc, Fin.snoc_last, hw, one_mul,
      Pi.zero_apply]
    rw [← dual_expand]
    linarith [hfv l]
  have hw0 := Matrix.eq_zero_of_mulVec_eq_zero hMdet hMw
  have hγ0 : γ = 0 := by
    have := congrFun hw0 (Fin.castSucc (Fin.last (k + 1)))
    simpa [hw] using this
  have hφ0 : φ = 0 := by
    refine (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).toBasis.ext fun m => ?_
    have := congrFun hw0 (Fin.castSucc (Fin.castSucc m))
    simp only [hw, Fin.snoc_castSucc, Pi.zero_apply, hψ] at this
    simpa using this
  apply hfx
  have e1 : f (ι x) = φ x := rfl
  rw [map_add, map_smul, e1, hφ0, ← hγ, hγ0]
  simp

theorem dir_inf_W {k : ℕ} (W : Submodule ℝ V) (o ω : V)
    (ι : EuclideanSpace ℝ (Fin (k + 1)) →ₗᵢ[ℝ] V) (hoW : o ∈ W) (hωW : ω ∈ W)
    (hWx : ∀ x (t : ℝ), o + ι x + t • ω ∈ W → x = 0)
    (u : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1))) (h : Fin (k + 3) → ℝ)
    (hdet : ∑ i, h i * hcof u i ≠ 0) :
    (affineSpan ℝ (Set.range fun i => o + ι (u i) + h i • ω)).direction ⊓ W = ℝ ∙ ω := by
  rw [direction_affineSpan, vectorSpan_range_eq_span_range_vsub_right ℝ _ 0]
  simp only [vsub_eq_sub]
  set S := LinearMap.range (ι.toLinearMap.coprod (LinearMap.toSpanSingleton ℝ V ω)) with hS
  have hspan : Submodule.span ℝ (Set.range fun i =>
      (o + ι (u i) + h i • ω) - (o + ι (u 0) + h 0 • ω)) ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨(u i - u 0, h i - h 0), ?_⟩
    simp [LinearMap.coprod_apply, map_sub]
    abel
  apply le_antisymm
  · rintro y ⟨hy, hyW⟩
    obtain ⟨⟨x, t⟩, rfl⟩ := hspan hy
    simp only [LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply,
      LinearIsometry.coe_toLinearMap] at hyW ⊢
    have hx0 : x = 0 := hWx x t (by
      rw [add_assoc]; exact W.add_mem hoW hyW)
    rw [hx0, map_zero, zero_add]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self ω)
  · rw [Submodule.span_le]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    refine ⟨?_, hωW⟩
    have := span_full o ω ι u h hdet 0 1
    simpa using this

theorem proj_norm [FiniteDimensional ℝ V] {k : ℕ} (ω : V)
    (ι : EuclideanSpace ℝ (Fin (k + 1)) →ₗᵢ[ℝ] V) (hιω : ∀ x, ⟪ι x, ω⟫ = 0)
    (x : EuclideanSpace ℝ (Fin (k + 1))) (t : ℝ) :
    ‖(ℝ ∙ ω)ᗮ.starProjection (ι x + t • ω)‖ = ‖x‖ := by
  have hmem : ι x ∈ (ℝ ∙ ω)ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]; exact hιω x
  have : (ℝ ∙ ω)ᗮ.starProjection (ι x + t • ω) = ι x := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero hmem fun w hw => ?_
    rw [add_sub_cancel_left, inner_smul_left]
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hw
    simp [hw]
  rw [this, LinearIsometry.norm_map]

end FSDir


-- ===== SLICE.lean =====

open scoped RealInnerProductSpace

set_option autoImplicit false

namespace FSL36
open FriendlyShadow.Gaussian

lemma hull_iff {d : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E] (b : Fin d → E) (p : E) :
    p ∈ convexHull ℝ (Set.range b) ↔
      ∃ l : Fin d → ℝ, (∀ i, 0 ≤ l i) ∧ ∑ i, l i = 1 ∧ ∑ i, l i • b i = p := by
  classical
  constructor
  · intro hp
    have e : convexHull ℝ (Set.range b) =
        (Fintype.linearCombination ℝ b) '' stdSimplex ℝ (Fin d) := by
      have hf : (⇑(Fintype.linearCombination ℝ b) ∘ fun i j : Fin d => if i = j then (1:ℝ) else 0)
          = b := by
        funext i; simp [Fintype.linearCombination_apply, ite_smul]
      rw [← convexHull_basis_eq_stdSimplex, LinearMap.image_convexHull, ← Set.range_comp, hf]
    rw [e] at hp
    obtain ⟨l, ⟨hl0, hl1⟩, rfl⟩ := hp
    exact ⟨l, hl0, hl1, by simp [Fintype.linearCombination_apply]⟩
  · rintro ⟨l, hl0, hl1, rfl⟩
    exact mem_convexHull_of_exists_fintype l b hl0 hl1 (fun i => Set.mem_range_self i) rfl

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma b_decomp {d : ℕ} [NeZero d] (ω : V) (b : Fin d → V) (i : Fin d) :
    b i = projPerp ω (b 0) + shapeOf ω b i + ⟪ω, b i⟫ • ω := by
  simp only [shapeOf, projPerp]; abel

lemma inner_projPerp (ω v : V) (hω : ‖ω‖ = 1) : ⟪ω, projPerp ω v⟫ = 0 := by
  simp only [projPerp, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hω]; ring

lemma inner_shape {d : ℕ} [NeZero d] (ω : V) (hω : ‖ω‖ = 1) (b : Fin d → V) (i : Fin d) :
    ⟪ω, shapeOf ω b i⟫ = 0 := by
  simp only [shapeOf, inner_sub_right, inner_projPerp ω _ hω, sub_zero]

lemma inner_comb {d : ℕ} [NeZero d] (ω : V) (hω : ‖ω‖ = 1) (b : Fin d → V) (l : Fin d → ℝ) :
    ⟪ω, ∑ i, l i • shapeOf ω b i⟫ = 0 := by
  simp [inner_sum, inner_smul_right, inner_shape ω hω b]

lemma sum_decomp {d : ℕ} [NeZero d] (ω : V) (b : Fin d → V) (l : Fin d → ℝ) :
    ∑ i, l i • b i = (∑ i, l i) • projPerp ω (b 0) + ∑ i, l i • shapeOf ω b i +
      (∑ i, l i * ⟪ω, b i⟫) • ω := by
  rw [Finset.sum_congr rfl (fun i _ => congrArg (l i • ·) (b_decomp ω b i))]
  simp only [smul_add, Finset.sum_add_distrib, Finset.sum_smul, smul_smul]

lemma mem_T {d : ℕ} [NeZero d] (b : Fin d → V) (ω : V) (hω : ‖ω‖ = 1) (q : V)
    (hq : ⟪ω, q⟫ = 0) (p : V) :
    p ∈ ({p | ∃ t : ℝ, p = projPerp ω (b 0) + q + t • ω} ∩ convexHull ℝ (Set.range b)) ↔
      ∃ l ∈ chordSet (shapeOf ω b) q,
        p = projPerp ω (b 0) + q + (∑ i, l i * ⟪ω, b i⟫) • ω := by
  have hωω : ⟪ω, ω⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hω]; norm_num
  constructor
  · rintro ⟨⟨t, ht⟩, hp⟩
    obtain ⟨l, hl0, hl1, hlp⟩ := (hull_iff b p).mp hp
    rw [sum_decomp ω b l, hl1, one_smul, ht, add_assoc, add_assoc] at hlp
    have e1 := add_left_cancel hlp
    have e2 := congrArg (fun v => ⟪ω, v⟫) e1
    simp only [inner_add_right, inner_smul_right, inner_comb ω hω b l, hq, hωω] at e2
    have htl : t = ∑ i, l i * ⟪ω, b i⟫ := by linarith
    rw [← htl] at e1
    have e3 : ∑ i, l i • shapeOf ω b i = q := add_right_cancel e1
    exact ⟨l, ⟨hl0, hl1, e3⟩, by rw [ht, htl]⟩
  · rintro ⟨l, ⟨hl0, hl1, hls⟩, rfl⟩
    refine ⟨⟨_, rfl⟩, (hull_iff b _).mpr ⟨l, hl0, hl1, ?_⟩⟩
    rw [sum_decomp ω b l, hl1, one_smul, hls]

/-- Under the rank condition the difference of two chord combinations is a multiple of the
kernel combination. -/
lemma diff_mul {d : ℕ} [NeZero d] (hd : 3 ≤ d) (s : Fin d → V) (hs0 : s 0 = 0)
    (hrank : Module.finrank ℝ (Submodule.span ℝ (Set.range s)) = d - 2)
    (z : Fin d → ℝ) (hz : IsKernelComb s z) (q : V) (l l' : Fin d → ℝ)
    (hl : l ∈ chordSet s q) (hl' : l' ∈ chordSet s q) :
    ∃ c : ℝ, ∀ i, l i - l' i = c * z i := by
  classical
  obtain ⟨hzs, hz0, hz1⟩ := hz
  obtain ⟨-, hl1, hls⟩ := hl
  obtain ⟨-, hl1', hls'⟩ := hl'
  set A := Fintype.linearCombination ℝ s with hA
  have hAapp : ∀ f : Fin d → ℝ, A f = ∑ i, f i • s i := fun f => by
    rw [hA, Fintype.linearCombination_apply]
  have hrk : Module.finrank ℝ (LinearMap.range A) = d - 2 := by
    rw [hA, Fintype.range_linearCombination]; exact hrank
  have hker : Module.finrank ℝ (LinearMap.ker A) = 2 := by
    have := LinearMap.finrank_range_add_finrank_ker A
    rw [hrk, Module.finrank_fin_fun] at this
    omega
  set e0 : Fin d → ℝ := Pi.single 0 1 with he0
  have he0A : e0 ∈ LinearMap.ker A := by
    rw [LinearMap.mem_ker, hAapp]
    simp [he0, Pi.single_apply, ite_smul, hs0]
  have hzA : z ∈ LinearMap.ker A := by rw [LinearMap.mem_ker, hAapp]; exact hzs
  have hzne : z ≠ 0 := by
    rintro rfl; simp at hz1
  have hsum_e0 : ∑ i, e0 i = 1 := by simp [he0]
  have hli : LinearIndependent ℝ ![e0, z] := by
    rw [LinearIndependent.pair_iff]
    intro a c hac
    have h1 := congrArg (fun f : Fin d → ℝ => ∑ i, f i) hac
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hsum_e0, hz0, Pi.zero_apply, Finset.sum_const_zero] at h1
    have ha : a = 0 := by linarith
    refine ⟨ha, ?_⟩
    rw [ha, zero_smul, zero_add] at hac
    exact (smul_eq_zero.mp hac).resolve_right hzne
  have hP : Submodule.span ℝ (Set.range ![e0, z]) = LinearMap.ker A := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact he0A
      · exact hzA
    · rw [finrank_span_eq_card hli, hker]; simp
  have hδ : l - l' ∈ LinearMap.ker A := by
    rw [LinearMap.mem_ker, hAapp]
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hls, hls', sub_self]
  rw [← hP, Submodule.mem_span_range_iff_exists_fun] at hδ
  obtain ⟨c, hc⟩ := hδ
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hc
  have h2 := congrArg (fun f : Fin d → ℝ => ∑ i, f i) hc
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, hsum_e0, hz0, Pi.sub_apply, Finset.sum_sub_distrib, hl1, hl1'] at h2
  have hc0 : c 0 = 0 := by linarith
  refine ⟨c 1, fun i => ?_⟩
  have h3 := congrFun hc i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc0, zero_mul, zero_add,
    Pi.sub_apply] at h3
  linarith

lemma sum_abs_le_two {d : ℕ} {s : Fin d → V} {q : V} {l l' : Fin d → ℝ}
    (hl : l ∈ chordSet s q) (hl' : l' ∈ chordSet s q) : ∑ i, |l i - l' i| ≤ 2 := by
  obtain ⟨h0, h1, -⟩ := hl
  obtain ⟨h0', h1', -⟩ := hl'
  calc ∑ i, |l i - l' i| ≤ ∑ i, (l i + l' i) :=
        Finset.sum_le_sum (fun i _ => abs_le.mpr ⟨by linarith [h0 i, h0' i], by linarith [h0 i, h0' i]⟩)
    _ = 2 := by rw [Finset.sum_add_distrib, h1, h1']; norm_num



variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma D_bdd {d : ℕ} (s : Fin d → V) (q : V) :
    BddAbove {t | ∃ l ∈ chordSet s q, ∃ l' ∈ chordSet s q, t = ∑ i, |l i - l' i|} :=
  ⟨2, by rintro _ ⟨l, hl, l', hl', rfl⟩; exact sum_abs_le_two hl hl'⟩

lemma C_ne {d : ℕ} (s : Fin d → V) (q : V) (hq : q ∈ convexHull ℝ (Set.range s)) :
    ∃ l, l ∈ chordSet s q := by
  obtain ⟨l, h0, h1, h2⟩ := (hull_iff s q).mp hq
  exact ⟨l, h0, h1, h2⟩

lemma D_ne {d : ℕ} (s : Fin d → V) (q : V) (hq : q ∈ convexHull ℝ (Set.range s)) :
    {t | ∃ l ∈ chordSet s q, ∃ l' ∈ chordSet s q, t = ∑ i, |l i - l' i|}.Nonempty := by
  obtain ⟨l, hl⟩ := C_ne s q hq
  exact ⟨_, l, hl, l, hl, rfl⟩

lemma le_two {d : ℕ} (s : Fin d → V) (q : V) (hq : q ∈ convexHull ℝ (Set.range s)) :
    chordLen s q ≤ 2 :=
  csSup_le (D_ne s q hq) (by rintro _ ⟨l, hl, l', hl', rfl⟩; exact sum_abs_le_two hl hl')

lemma oriented {d : ℕ} [NeZero d] (hd : 3 ≤ d) (s : Fin d → V) (hs0 : s 0 = 0)
    (hrank : Module.finrank ℝ (Submodule.span ℝ (Set.range s)) = d - 2)
    (z : Fin d → ℝ) (hz : IsKernelComb s z) (q : V) (l l' : Fin d → ℝ)
    (hl : l ∈ chordSet s q) (hl' : l' ∈ chordSet s q) :
    ∃ m ∈ chordSet s q, ∃ m' ∈ chordSet s q,
      ∀ i, m i - m' i = (∑ j, |l j - l' j|) * z i := by
  obtain ⟨c, hc⟩ := diff_mul hd s hs0 hrank z hz q l l' hl hl'
  have e : ∑ j, |l j - l' j| = |c| := by
    simp only [hc, abs_mul, ← Finset.mul_sum, hz.2.2, mul_one]
  rw [e]
  rcases le_total 0 c with h | h
  · exact ⟨l, hl, l', hl', fun i => by rw [abs_of_nonneg h, hc i]⟩
  · exact ⟨l', hl', l, hl, fun i => by rw [abs_of_nonpos h]; linarith [hc i]⟩

lemma comb_mem {d : ℕ} (s : Fin d → V) (q1 q2 : V) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (m1 m2 : Fin d → ℝ) (h1 : m1 ∈ chordSet s q1) (h2 : m2 ∈ chordSet s q2) :
    (fun i => a * m1 i + b * m2 i) ∈ chordSet s (a • q1 + b • q2) := by
  obtain ⟨p1, s1, v1⟩ := h1
  obtain ⟨p2, s2, v2⟩ := h2
  refine ⟨fun i => add_nonneg (mul_nonneg ha (p1 i)) (mul_nonneg hb (p2 i)), ?_, ?_⟩
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, s1, s2]; linarith
  · simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum, v1, v2]

lemma sup_comb (D1 D2 : Set ℝ) (M a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1n : D1.Nonempty) (h2n : D2.Nonempty)
    (h : ∀ t1 ∈ D1, ∀ t2 ∈ D2, a * t1 + b * t2 ≤ M) :
    a * sSup D1 + b * sSup D2 ≤ M := by
  have step : ∀ t2 ∈ D2, a * sSup D1 ≤ M - b * t2 := by
    intro t2 ht2
    rw [← smul_eq_mul, ← Real.sSup_smul_of_nonneg ha]
    refine csSup_le (h1n.smul_set) ?_
    rintro _ ⟨t1, ht1, rfl⟩
    have := h t1 ht1 t2 ht2
    simp only [smul_eq_mul]; linarith
  have step2 : b * sSup D2 ≤ M - a * sSup D1 := by
    rw [← smul_eq_mul, ← Real.sSup_smul_of_nonneg hb]
    refine csSup_le (h2n.smul_set) ?_
    rintro _ ⟨t2, ht2, rfl⟩
    have := step t2 ht2
    simp only [smul_eq_mul]; linarith
  linarith

end FSL36

open FriendlyShadow.Gaussian RealInnerProductSpace in
theorem FSL35_main {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {d : ℕ}
    [NeZero d] (hd : 3 ≤ d) (s : Fin d → V) (hs0 : s 0 = 0)
    (hrank : Module.finrank ℝ (Submodule.span ℝ (Set.range s)) = d - 2)
    (z : Fin d → ℝ) (hz : IsKernelComb s z) :
    ConcaveOn ℝ (convexHull ℝ (Set.range s)) (chordLen s) ∧
      chordLen s (∑ i, |z i| • s i) = 2 ∧
      ∀ q ∈ convexHull ℝ (Set.range s), chordLen s q ≤ 2 := by
  refine ⟨⟨convex_convexHull ℝ _, ?_⟩, ?_, fun q hq => FSL36.le_two s q hq⟩
  · intro q1 hq1 q2 hq2 a b ha hb hab
    simp only [smul_eq_mul]
    refine FSL36.sup_comb _ _ _ a b ha hb (FSL36.D_ne s q1 hq1) (FSL36.D_ne s q2 hq2) ?_
    rintro _ ⟨l1, hl1, l1', hl1', rfl⟩ _ ⟨l2, hl2, l2', hl2', rfl⟩
    obtain ⟨m1, hm1, m1', hm1', e1⟩ := FSL36.oriented hd s hs0 hrank z hz q1 l1 l1' hl1 hl1'
    obtain ⟨m2, hm2, m2', hm2', e2⟩ := FSL36.oriented hd s hs0 hrank z hz q2 l2 l2' hl2 hl2'
    set t1 := ∑ j, |l1 j - l1' j| with ht1
    set t2 := ∑ j, |l2 j - l2' j| with ht2
    have ht10 : 0 ≤ t1 := Finset.sum_nonneg (fun j _ => abs_nonneg _)
    have ht20 : 0 ≤ t2 := Finset.sum_nonneg (fun j _ => abs_nonneg _)
    have hn := FSL36.comb_mem s q1 q2 a b ha hb hab m1 m2 hm1 hm2
    have hn' := FSL36.comb_mem s q1 q2 a b ha hb hab m1' m2' hm1' hm2'
    have hval : ∑ i, |(a * m1 i + b * m2 i) - (a * m1' i + b * m2' i)| = a * t1 + b * t2 := by
      have : ∀ i, (a * m1 i + b * m2 i) - (a * m1' i + b * m2' i) = (a * t1 + b * t2) * z i := by
        intro i; have := e1 i; have := e2 i
        calc (a * m1 i + b * m2 i) - (a * m1' i + b * m2' i)
            = a * (m1 i - m1' i) + b * (m2 i - m2' i) := by ring
          _ = (a * t1 + b * t2) * z i := by rw [e1 i, e2 i]; ring
      simp only [this, abs_mul, ← Finset.mul_sum, hz.2.2, mul_one]
      exact abs_of_nonneg (by positivity)
    rw [← hval]
    exact le_csSup (FSL36.D_bdd s _) ⟨_, hn, _, hn', rfl⟩
  · obtain ⟨hzs, hz0, hz1⟩ := hz
    have hpm : ∀ r : ℝ, max r 0 - max (-r) 0 = r ∧ max r 0 + max (-r) 0 = |r| := by
      intro r
      rcases le_total 0 r with h | h
      · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]; constructor <;> ring
      · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]; constructor <;> ring
    set zp : Fin d → ℝ := fun i => max (z i) 0 with hzp
    set zm : Fin d → ℝ := fun i => max (-z i) 0 with hzm
    have hsub : ∀ i, zp i - zm i = z i := fun i => (hpm (z i)).1
    have hadd : ∀ i, zp i + zm i = |z i| := fun i => (hpm (z i)).2
    have hS1 : ∑ i, zp i - ∑ i, zm i = 0 := by
      rw [← Finset.sum_sub_distrib]; simp only [hsub]; exact hz0
    have hS2 : ∑ i, zp i + ∑ i, zm i = 1 := by
      rw [← Finset.sum_add_distrib]; simp only [hadd]; exact hz1
    have hV1 : ∑ i, zp i • s i = ∑ i, zm i • s i := by
      have : ∑ i, (zp i - zm i) • s i = 0 := by simp only [hsub]; exact hzs
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
      simpa only [sub_smul] using this
    have hy : ∑ i, |z i| • s i = ∑ i, (2 * zp i) • s i := by
      simp only [← hadd, add_smul, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum, hV1]
      rw [two_smul]
    have hy' : ∑ i, |z i| • s i = ∑ i, (2 * zm i) • s i := by
      rw [hy]; simp only [mul_smul, ← Finset.smul_sum, hV1]
    have hl : (fun i => 2 * zp i) ∈ chordSet s (∑ i, |z i| • s i) :=
      ⟨fun i => by positivity, by rw [← Finset.mul_sum]; linarith, hy.symm⟩
    have hl' : (fun i => 2 * zm i) ∈ chordSet s (∑ i, |z i| • s i) :=
      ⟨fun i => by positivity, by rw [← Finset.mul_sum]; linarith, hy'.symm⟩
    have hval : ∑ i, |2 * zp i - 2 * zm i| = 2 := by
      have : ∀ i, |2 * zp i - 2 * zm i| = 2 * |z i| := by
        intro i; rw [← mul_sub, hsub, abs_mul, abs_two]
      simp only [this, ← Finset.mul_sum, hz1, mul_one]
    have hq : ∑ i, |z i| • s i ∈ convexHull ℝ (Set.range s) :=
      (FSL36.hull_iff s _).mpr ⟨_, hl.1, hl.2.1, hl.2.2⟩
    refine le_antisymm (FSL36.le_two s _ hq) ?_
    rw [← hval]
    exact le_csSup (FSL36.D_bdd s _) ⟨_, hl, _, hl', rfl⟩

namespace FSL39
open MeasureTheory

lemma cv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (G : E → ENNReal) (y : E) {c : ℝ} (hc : 0 < c) :
    ∫⁻ x, G x ∂μ =
      ENNReal.ofReal (c ^ Module.finrank ℝ E) * ∫⁻ q, G (y + c • (q - y)) ∂μ := by
  have h1 : ∫⁻ q, G (y + c • (q - y)) ∂μ = ∫⁻ w, G (y + c • w) ∂μ := by
    have := lintegral_add_right_eq_self (μ := μ) (fun w => G (y + c • w)) (-y)
    simpa [sub_eq_add_neg] using this
  have h2 : ∫⁻ w, G (y + c • w) ∂μ =
      ENNReal.ofReal (|(c ^ Module.finrank ℝ E)⁻¹|) * ∫⁻ w, G (y + w) ∂μ := by
    have hm := Measure.map_addHaar_smul μ hc.ne'
    have := lintegral_map_equiv (μ := μ) (fun w => G (y + w)) (MeasurableEquiv.smul₀ c hc.ne')
    rw [show ⇑(MeasurableEquiv.smul₀ c hc.ne' : E ≃ᵐ E) = (c • · : E → E) from rfl, hm,
      lintegral_smul_measure] at this
    rw [← this]; rfl
  have h3 : ∫⁻ w, G (y + w) ∂μ = ∫⁻ x, G x ∂μ := lintegral_add_left_eq_self G y
  rw [h1, h2, h3, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hp : 0 < c ^ Module.finrank ℝ E := by positivity
  rw [abs_of_pos (inv_pos.mpr hp), mul_inv_cancel₀ hp.ne', ENNReal.ofReal_one, one_mul]

end FSL39

open FriendlyShadow.Gaussian MeasureTheory RealInnerProductSpace in
theorem FSL39_main {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    (s : Fin d → EuclideanSpace ℝ (Fin (d - 2))) (hs0 : s 0 = 0)
    (hrank : Module.finrank ℝ (Submodule.span ℝ (Set.range s)) = d - 2)
    (L R : ℝ) (hL : 0 < L) (hR : 0 ≤ R) (hdiam : ∀ i j, ‖s i - s j‖ ≤ 2 + 2 * R)
    (hLR : (d : ℝ) / 3 ≤ L * R) (z : Fin d → ℝ) (hz : IsKernelComb s z)
    (mubar : Fin d → EuclideanSpace ℝ (Fin (d - 2)) → ℝ → ℝ)
    (hpos : ∀ i u h, 0 < mubar i u h)
    (hlip : ∀ i u u' h h', mubar i u h ≤
      Real.exp (L * Real.sqrt (‖u - u'‖ ^ 2 + (h - h') ^ 2)) * mubar i u' h')
    (p : EuclideanSpace ℝ (Fin (d - 2))) :
    ENNReal.ofReal (Real.exp (-2) / (d * L * (1 + R))) *
        ∫⁻ q in convexHull ℝ (Set.range s), heightMarginal mubar s z (p - q) ≤
      ∫⁻ q in convexHull ℝ (Set.range s),
        ENNReal.ofReal (chordLen s q) * heightMarginal mubar s z (p - q) := by
  classical
  set K := convexHull ℝ (Set.range s) with hKdef
  set f : EuclideanSpace ℝ (Fin (d - 2)) → ENNReal :=
    fun q => heightMarginal mubar s z (p - q) with hfdef
  obtain ⟨hconc, hy2, -⟩ := FSL35_main hd s hs0 hrank z hz
  set y : EuclideanSpace ℝ (Fin (d - 2)) := ∑ i, |z i| • s i with hydef
  have hyK : y ∈ K := Convex.sum_mem (convex_convexHull ℝ (Set.range s))
    (fun i _ => abs_nonneg (z i)) hz.2.2 (fun i _ => subset_convexHull ℝ (Set.range s) ⟨i, rfl⟩)
  have hKc : IsCompact K := (Set.finite_range s).isCompact_convexHull ℝ
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  -- numbers
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hM : 0 < (d : ℝ) * L * (1 + R) := by positivity
  set δ : ℝ := 1 / ((d : ℝ) * L * (1 + R)) with hδdef
  have hδpos : 0 < δ := by positivity
  have hδM : δ * ((d : ℝ) * L * (1 + R)) = 1 := by rw [hδdef]; field_simp
  have hdcast : ((d - 2 : ℕ) : ℝ) = (d : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hsmall : ((d - 2 : ℕ) : ℝ) * δ ≤ 1 / 2 := by
    rw [hdcast, hδdef, mul_one_div, div_le_iff₀ hM]
    have : (d : ℝ) * (d / 3) ≤ (d : ℝ) * L * (1 + R) := by
      have := mul_le_mul_of_nonneg_left hLR hdpos.le
      nlinarith [mul_pos hdpos hL]
    nlinarith
  have hδle : δ ≤ 1 / 2 := by
    have h1 : (1 : ℝ) ≤ ((d - 2 : ℕ) : ℝ) := by rw [hdcast]; linarith
    nlinarith
  set c : ℝ := 1 - δ with hcdef
  have hcpos : 0 < c := by rw [hcdef]; linarith
  have hcn : (1 / 2 : ℝ) ≤ c ^ (d - 2) := by
    have := one_add_mul_le_pow (a := -δ) (by linarith) (d - 2)
    rw [hcdef, sub_eq_add_neg]; nlinarith
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin (d - 2))) = d - 2 := by simp
  -- pointwise facts
  have hφ : ∀ q, y + c • (q - y) = δ • y + c • q := by
    intro q; rw [hcdef]; module
  have hφK : ∀ q ∈ K, y + c • (q - y) ∈ K := by
    intro q hq; rw [hφ]
    exact convex_convexHull ℝ _ hyK hq hδpos.le hcpos.le (by rw [hcdef]; ring)
  have hg0 : ∀ q ∈ K, 0 ≤ chordLen s q := by
    intro q hq
    obtain ⟨l, hl⟩ := FSL36.C_ne s q hq
    exact le_csSup (FSL36.D_bdd s q) ⟨l, hl, l, hl, by simp⟩
  have hgφ : ∀ q ∈ K, 2 * δ ≤ chordLen s (y + c • (q - y)) := by
    intro q hq
    have h := hconc.2 hyK hq hδpos.le hcpos.le (by rw [hcdef]; ring)
    rw [hφ]
    simp only [smul_eq_mul] at h
    rw [hy2] at h
    nlinarith [hg0 q hq]
  have hdist : ∀ q ∈ K, ‖(y + c • (q - y)) - q‖ ≤ δ * (2 + 2 * R) := by
    intro q hq
    have he : (y + c • (q - y)) - q = (-δ) • (q - y) := by rw [hcdef]; module
    rw [he, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hδpos]
    refine mul_le_mul_of_nonneg_left ?_ hδpos.le
    obtain ⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, hab⟩ := convexHull_exists_dist_ge2 hq hyK
    rw [← dist_eq_norm]
    exact hab.trans (by rw [dist_eq_norm]; exact hdiam i j)
  have hf : ∀ q ∈ K, f q ≤ ENNReal.ofReal (Real.exp 2) * f (y + c • (q - y)) := by
    intro q hq
    set v := (y + c • (q - y)) - q
    have hv := hdist q hq
    have hexp : Real.exp (L * ‖v‖) ^ d ≤ Real.exp 2 := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have : (d : ℝ) * (L * ‖v‖) ≤ (d : ℝ) * (L * (δ * (2 + 2 * R))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv hL.le) hdpos.le
      nlinarith
    simp only [hfdef, heightMarginal]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun h => ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos 2).le]
    apply ENNReal.ofReal_le_ofReal
    have hprod : ∏ i, mubar i (p - q + s i) (h i) ≤
        Real.exp (L * ‖v‖) ^ d * ∏ i, mubar i (p - (y + c • (q - y)) + s i) (h i) := by
      rw [← Fin.prod_const, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod (fun i _ => (hpos _ _ _).le) (fun i _ => ?_)
      have := hlip i (p - q + s i) (p - (y + c • (q - y)) + s i) (h i) (h i)
      have hn : ‖(p - q + s i) - (p - (y + c • (q - y)) + s i)‖ = ‖v‖ := by
        congr 1; simp only [v]; abel
      rwa [hn, sub_self, zero_pow two_ne_zero, add_zero, Real.sqrt_sq (norm_nonneg _)] at this
    have hP : 0 ≤ ∏ i, mubar i (p - (y + c • (q - y)) + s i) (h i) :=
      Finset.prod_nonneg fun i _ => (hpos _ _ _).le
    calc |∑ i, z i * h i| * ∏ i, mubar i (p - q + s i) (h i)
        ≤ |∑ i, z i * h i| * (Real.exp (L * ‖v‖) ^ d *
            ∏ i, mubar i (p - (y + c • (q - y)) + s i) (h i)) :=
          mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
      _ ≤ |∑ i, z i * h i| * (Real.exp 2 *
            ∏ i, mubar i (p - (y + c • (q - y)) + s i) (h i)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp hP) (abs_nonneg _)
      _ = Real.exp 2 * (|∑ i, z i * h i| *
            ∏ i, mubar i (p - (y + c • (q - y)) + s i) (h i)) := by ring
  -- assembly
  set G : EuclideanSpace ℝ (Fin (d - 2)) → ENNReal :=
    fun q => ENNReal.ofReal (chordLen s q) * f q with hGdef
  set κ : ENNReal := ENNReal.ofReal (2 * δ) * ENNReal.ofReal (Real.exp (-2)) with hκ
  have hpt : ∀ q, K.indicator (fun q => κ * f q) q ≤ K.indicator G (y + c • (q - y)) := by
    intro q
    by_cases hq : q ∈ K
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem (hφK q hq)]
      have h1 := hf q hq
      have h2 : ENNReal.ofReal (Real.exp (-2)) * f q ≤ f (y + c • (q - y)) := by
        calc ENNReal.ofReal (Real.exp (-2)) * f q
            ≤ ENNReal.ofReal (Real.exp (-2)) *
                (ENNReal.ofReal (Real.exp 2) * f (y + c • (q - y))) := by gcongr
          _ = f (y + c • (q - y)) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
            norm_num
      simp only [hGdef, hκ, mul_assoc]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hgφ q hq)) h2
    · rw [Set.indicator_of_notMem hq]; exact bot_le
  have hR1 : ∫⁻ q in K, G q = ENNReal.ofReal (c ^ (d - 2)) *
      ∫⁻ q, K.indicator G (y + c • (q - y)) := by
    rw [← lintegral_indicator hKm, FSL39.cv volume (K.indicator G) y hcpos, hfin]
  have hL1 : ∫⁻ q, K.indicator (fun q => κ * f q) q = κ * ∫⁻ q in K, f q := by
    rw [lintegral_indicator hKm, lintegral_const_mul' _ _ (by
      rw [hκ]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  have hmain : ENNReal.ofReal (c ^ (d - 2)) * κ * ∫⁻ q in K, f q ≤ ∫⁻ q in K, G q := by
    rw [hR1, mul_assoc, ← hL1]
    gcongr with q
    exact hpt q
  refine le_trans ?_ hmain
  gcongr
  rw [hκ, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have he : Real.exp (-2) / ((d : ℝ) * L * (1 + R)) = Real.exp (-2) * δ := by
    rw [hδdef]; ring
  rw [he]
  have hE := Real.exp_pos (-2)
  nlinarith [mul_pos hE hδpos]

open MeasureTheory

set_option autoImplicit false

namespace FSL41

noncomputable def g {d : ℕ} (ν : Fin d → ℝ → ℝ) (i j k : Fin d) (x : ℝ) : ℝ :=
  ((if k = i then x else 1) * (if k = j then x else 1)) * ν k x

lemma int_x {d : ℕ} (ν : Fin d → ℝ → ℝ) (hν0 : ∀ i γ, 0 ≤ ν i γ)
    (hνint : ∀ i, Integrable (ν i)) (hν2 : ∀ i, Integrable (fun γ => γ ^ 2 * ν i γ))
    (k : Fin d) : Integrable (fun x => x * ν k x) := by
  refine Integrable.mono' ((hνint k).add (hν2 k))
    (aestronglyMeasurable_id.mul (hνint k).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  have h0 := hν0 k x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
  have : |x| ≤ 1 + x ^ 2 := by nlinarith [abs_nonneg x, sq_abs x, sq_nonneg (|x| - 1)]
  simp only [Pi.add_apply]
  nlinarith

lemma g_int {d : ℕ} (ν : Fin d → ℝ → ℝ) (hν0 : ∀ i γ, 0 ≤ ν i γ)
    (hνint : ∀ i, Integrable (ν i)) (hν2 : ∀ i, Integrable (fun γ => γ ^ 2 * ν i γ))
    (i j k : Fin d) : Integrable (g ν i j k) := by
  have hx := int_x ν hν0 hνint hν2 k
  by_cases hi : k = i <;> by_cases hj : k = j
  · have e : g ν i j k = fun x => x ^ 2 * ν k x := by
      funext x; simp only [g, if_pos hi, if_pos hj]; ring
    rw [e]; exact hν2 k
  · have e : g ν i j k = fun x => x * ν k x := by
      funext x; simp only [g, if_pos hi, if_neg hj]; ring
    rw [e]; exact hx
  · have e : g ν i j k = fun x => x * ν k x := by
      funext x; simp only [g, if_neg hi, if_pos hj]; ring
    rw [e]; exact hx
  · have e : g ν i j k = ν k := by
      funext x; simp only [g, if_neg hi, if_neg hj]; ring
    rw [e]; exact hνint k

lemma prod_g {d : ℕ} (ν : Fin d → ℝ → ℝ) (i j : Fin d) (h : Fin d → ℝ) :
    ∏ k, g ν i j k (h k) = h i * h j * ∏ k, ν k (h k) := by
  simp only [g, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]

lemma gval_ne {d : ℕ} (ν : Fin d → ℝ → ℝ) (hν1 : ∀ i, ∫ γ, ν i γ = 1)
    (i j : Fin d) (hij : i ≠ j) (k : Fin d) :
    ∫ x, g ν i j k x = (if k = i then ∫ x, x * ν k x else 1) *
      (if k = j then ∫ x, x * ν k x else 1) := by
  by_cases hi : k = i
  · have hj : k ≠ j := fun h => hij (hi.symm.trans h)
    simp only [g, if_pos hi, if_neg hj, mul_one]
  · by_cases hj : k = j
    · simp only [g, if_neg hi, if_pos hj, one_mul]
    · simp only [g, if_neg hi, if_neg hj, one_mul, mul_one]; exact hν1 k

lemma gval_eq {d : ℕ} (ν : Fin d → ℝ → ℝ) (hν1 : ∀ i, ∫ γ, ν i γ = 1)
    (i k : Fin d) :
    ∫ x, g ν i i k x = if k = i then ∫ x, x ^ 2 * ν k x else 1 := by
  by_cases hi : k = i
  · simp only [g, if_pos hi]
    congr 1; funext x; ring
  · simp only [g, if_neg hi, one_mul]; exact hν1 k

lemma F_eq {d : ℕ} (ν : Fin d → ℝ → ℝ) (i j : Fin d) :
    (fun h : Fin d → ℝ => h i * h j * ∏ k, ν k (h k)) = fun h => ∏ k, g ν i j k (h k) := by
  funext h; rw [prod_g]

lemma F_int {d : ℕ} (ν : Fin d → ℝ → ℝ) (hν0 : ∀ i γ, 0 ≤ ν i γ)
    (hνint : ∀ i, Integrable (ν i)) (hν2 : ∀ i, Integrable (fun γ => γ ^ 2 * ν i γ))
    (i j : Fin d) :
    Integrable (fun h : Fin d → ℝ => h i * h j * ∏ k, ν k (h k)) := by
  rw [F_eq, volume_pi]
  exact Integrable.fintype_prod (fun k => g_int ν hν0 hνint hν2 i j k)

lemma E_eq {d : ℕ} (ν : Fin d → ℝ → ℝ) (hν1 : ∀ i, ∫ γ, ν i γ = 1) (i j : Fin d) :
    ∫ h : Fin d → ℝ, h i * h j * ∏ k, ν k (h k) =
      if i = j then ∫ x, x ^ 2 * ν i x else (∫ x, x * ν i x) * ∫ x, x * ν j x := by
  rw [F_eq, volume_pi, integral_fintype_prod_eq_prod]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, Finset.prod_congr rfl (fun k _ => gval_eq ν hν1 i k)]
    simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true]
  · rw [if_neg hij, Finset.prod_congr rfl (fun k _ => gval_ne ν hν1 i j hij k)]
    simp only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]

lemma p_int {d : ℕ} (ν : Fin d → ℝ → ℝ) (hνint : ∀ i, Integrable (ν i)) :
    Integrable (fun h : Fin d → ℝ => ∏ k, ν k (h k)) := by
  rw [volume_pi]; exact Integrable.fintype_prod hνint

lemma p_integral {d : ℕ} (ν : Fin d → ℝ → ℝ) (hν1 : ∀ i, ∫ γ, ν i γ = 1) :
    ∫ h : Fin d → ℝ, ∏ k, ν k (h k) = 1 := by
  rw [volume_pi, integral_fintype_prod_eq_prod]
  simp only [hν1, Finset.prod_const_one]

lemma sq_expand {d : ℕ} (ν : Fin d → ℝ → ℝ) (z : Fin d → ℝ) (h : Fin d → ℝ) :
    (∑ i, z i * h i) ^ 2 * ∏ k, ν k (h k) =
      ∑ i, ∑ j, z i * z j * (h i * h j * ∏ k, ν k (h k)) := by
  rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- Second moment of `Z = Σ zᵢhᵢ` under the product density. -/
lemma second_moment {d : ℕ} (z : Fin d → ℝ)
    (ν : Fin d → ℝ → ℝ) (hν0 : ∀ i γ, 0 ≤ ν i γ) (hνint : ∀ i, Integrable (ν i))
    (hν1 : ∀ i, ∫ γ, ν i γ = 1) (hν2 : ∀ i, Integrable (fun γ => γ ^ 2 * ν i γ)) :
    Integrable (fun h : Fin d → ℝ => (∑ i, z i * h i) ^ 2 * ∏ k, ν k (h k)) ∧
    ∫ h : Fin d → ℝ, (∑ i, z i * h i) ^ 2 * ∏ k, ν k (h k) =
      (∑ i, z i * ∫ x, x * ν i x) ^ 2 +
        ∑ i, z i ^ 2 * ((∫ x, x ^ 2 * ν i x) - (∫ x, x * ν i x) ^ 2) := by
  have e : (fun h : Fin d → ℝ => (∑ i, z i * h i) ^ 2 * ∏ k, ν k (h k)) =
      fun h => ∑ i, ∑ j, z i * z j * (h i * h j * ∏ k, ν k (h k)) := by
    funext h; exact sq_expand ν z h
  have hint : ∀ i j, Integrable (fun h : Fin d → ℝ => z i * z j * (h i * h j * ∏ k, ν k (h k))) :=
    fun i j => (F_int ν hν0 hνint hν2 i j).const_mul _
  refine ⟨?_, ?_⟩
  · rw [e]
    exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))
  rw [e, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hint _ j), integral_const_mul, E_eq ν hν1]
  set m1 : Fin d → ℝ := fun i => ∫ x, x * ν i x with hm1
  set m2 : Fin d → ℝ := fun i => ∫ x, x ^ 2 * ν i x with hm2
  have key : ∀ i j, z i * z j * (if i = j then m2 i else m1 i * m1 j) =
      (z i * m1 i) * (z j * m1 j) + (if i = j then z i ^ 2 * (m2 i - m1 i ^ 2) else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp only [if_true]; ring
    · simp only [if_neg hij]; ring
  have key' : ∀ i j, z i * z j * (if i = j then ∫ x, x ^ 2 * ν i x
      else (∫ x, x * ν i x) * ∫ x, x * ν j x) =
      (z i * m1 i) * (z j * m1 j) + (if i = j then z i ^ 2 * (m2 i - m1 i ^ 2) else 0) := key
  simp_rw [key', Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sq, Finset.sum_mul_sum]

end FSL41

open MeasureTheory in
theorem FSL41_main {d : ℕ} (hd : 3 ≤ d) (z : Fin d → ℝ) (hz : ∑ i, |z i| = 1)
    (ν : Fin d → ℝ → ℝ) (hν0 : ∀ i γ, 0 ≤ ν i γ) (hνint : ∀ i, Integrable (ν i))
    (hν1 : ∀ i, ∫ γ, ν i γ = 1) (hν2 : ∀ i, Integrable (fun γ => γ ^ 2 * ν i γ))
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hvar : ∀ i, τ ^ 2 ≤ (∫ γ, γ ^ 2 * ν i γ) - (∫ γ, γ * ν i γ) ^ 2) :
    ENNReal.ofReal (τ / (2 * Real.sqrt d)) *
        ∫⁻ h : Fin d → ℝ, ENNReal.ofReal (|∑ i, z i * h i| * ∏ i, ν i (h i)) ≤
      ∫⁻ h : Fin d → ℝ, ENNReal.ofReal ((∑ i, z i * h i) ^ 2 * ∏ i, ν i (h i)) := by
  obtain ⟨hZint, hI⟩ := FSL41.second_moment z ν hν0 hνint hν1 hν2
  set I := ∫ h : Fin d → ℝ, (∑ i, z i * h i) ^ 2 * ∏ k, ν k (h k) with hIdef
  set a := τ / (2 * Real.sqrt d) with ha
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hsq : Real.sqrt d ^ 2 = d := Real.sq_sqrt hdpos.le
  have hsqpos : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdpos
  have ha0 : 0 ≤ a := by positivity
  -- lower bound on I
  have hzsq : (1 : ℝ) ≤ d * ∑ i, z i ^ 2 := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |z i|)
    simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at hcs
    rw [hz] at hcs; simpa using hcs
  have hIlow : τ ^ 2 * ∑ i, z i ^ 2 ≤ I := by
    rw [hI, Finset.mul_sum]
    have h1 : ∑ i, τ ^ 2 * z i ^ 2 ≤
        ∑ i, z i ^ 2 * ((∫ x, x ^ 2 * ν i x) - (∫ x, x * ν i x) ^ 2) :=
      Finset.sum_le_sum (fun i _ => by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hvar i) (sq_nonneg _))
    nlinarith [sq_nonneg (∑ i, z i * ∫ x, x * ν i x)]
  have ha2 : a ^ 2 ≤ I := by
    have e : a ^ 2 = τ ^ 2 / (4 * d) := by
      rw [ha, div_pow, mul_pow, hsq]; ring
    rw [e]
    have hτd : τ ^ 2 / (4 * d) ≤ τ ^ 2 * ∑ i, z i ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg τ]
    linarith
  -- pointwise AM-GM
  have hp0 : ∀ h : Fin d → ℝ, 0 ≤ ∏ k, ν k (h k) :=
    fun h => Finset.prod_nonneg (fun k _ => hν0 k (h k))
  have hpint := FSL41.p_int ν hνint
  have hp1 := FSL41.p_integral ν hν1
  have hGint : Integrable (fun h : Fin d → ℝ =>
      ((∑ i, z i * h i) ^ 2 * ∏ k, ν k (h k) + a ^ 2 * ∏ k, ν k (h k)) / 2) :=
    (hZint.add (hpint.const_mul (a ^ 2))).div_const 2
  have hG : ∫ h : Fin d → ℝ,
      ((∑ i, z i * h i) ^ 2 * ∏ k, ν k (h k) + a ^ 2 * ∏ k, ν k (h k)) / 2 = (I + a ^ 2) / 2 := by
    rw [integral_div, integral_add hZint (hpint.const_mul _), integral_const_mul, hp1, mul_one]
  have step1 : ENNReal.ofReal a *
      ∫⁻ h : Fin d → ℝ, ENNReal.ofReal (|∑ i, z i * h i| * ∏ i, ν i (h i)) =
      ∫⁻ h : Fin d → ℝ, ENNReal.ofReal (a * (|∑ i, z i * h i| * ∏ i, ν i (h i))) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1; funext h; rw [ENNReal.ofReal_mul ha0]
  rw [step1]
  calc ∫⁻ h : Fin d → ℝ, ENNReal.ofReal (a * (|∑ i, z i * h i| * ∏ i, ν i (h i)))
      ≤ ∫⁻ h : Fin d → ℝ, ENNReal.ofReal
          (((∑ i, z i * h i) ^ 2 * ∏ k, ν k (h k) + a ^ 2 * ∏ k, ν k (h k)) / 2) := by
        refine lintegral_mono (fun h => ENNReal.ofReal_le_ofReal ?_)
        have hp := hp0 h
        have hZ2 : (∑ i, z i * h i) ^ 2 = |∑ i, z i * h i| ^ 2 := (sq_abs _).symm
        rw [hZ2]
        nlinarith [mul_nonneg (sq_nonneg (|∑ i, z i * h i| - a)) hp]
    _ = ENNReal.ofReal ((I + a ^ 2) / 2) := by
        rw [← hG, ofReal_integral_eq_lintegral_ofReal hGint
          (Filter.Eventually.of_forall (fun h => by
            have := hp0 h; positivity))]
    _ ≤ ENNReal.ofReal I := ENNReal.ofReal_le_ofReal (by linarith)
    _ = ∫⁻ h : Fin d → ℝ, ENNReal.ofReal ((∑ i, z i * h i) ^ 2 * ∏ i, ν i (h i)) := by
        rw [hIdef, ofReal_integral_eq_lintegral_ofReal hZint
          (Filter.Eventually.of_forall (fun h => by
            have := hp0 h; positivity))]

namespace FSU41
open MeasureTheory

/-- Unnormalised Lemma 41 (finite second moments): line densities `ν i` of positive finite mass
`M i`, variance condition in the cross-multiplied `LineVarianceGE` form. -/
theorem fin_case {d : ℕ} (hd : 3 ≤ d) (z : Fin d → ℝ) (hz : ∑ i, |z i| = 1)
    (ν : Fin d → ℝ → ℝ) (hν0 : ∀ i γ, 0 ≤ ν i γ) (hνint : ∀ i, Integrable (ν i))
    (hM : ∀ i, 0 < ∫ γ, ν i γ) (hν2 : ∀ i, Integrable (fun γ => γ ^ 2 * ν i γ))
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hvar : ∀ i, τ ^ 2 * (∫ γ, ν i γ) ^ 2 ≤
      (∫ γ, γ ^ 2 * ν i γ) * (∫ γ, ν i γ) - (∫ γ, γ * ν i γ) ^ 2) :
    ENNReal.ofReal (τ / (2 * Real.sqrt d)) *
        ∫⁻ h : Fin d → ℝ, ENNReal.ofReal (|∑ i, z i * h i| * ∏ i, ν i (h i)) ≤
      ∫⁻ h : Fin d → ℝ, ENNReal.ofReal ((∑ i, z i * h i) ^ 2 * ∏ i, ν i (h i)) := by
  set M : Fin d → ℝ := fun i => ∫ γ, ν i γ with hMdef
  set ν' : Fin d → ℝ → ℝ := fun i γ => ν i γ / M i with hν'def
  have hν'0 : ∀ i γ, 0 ≤ ν' i γ := fun i γ => div_nonneg (hν0 i γ) (hM i).le
  have hν'int : ∀ i, Integrable (ν' i) := fun i => (hνint i).div_const (M i)
  have hν'1 : ∀ i, ∫ γ, ν' i γ = 1 := by
    intro i; simp only [hν'def]; rw [integral_div]; exact div_self (hM i).ne'
  have e2 : ∀ i, (fun γ => γ ^ 2 * ν' i γ) = fun γ => (γ ^ 2 * ν i γ) / M i := by
    intro i; funext γ; simp only [hν'def]; ring
  have e1 : ∀ i, (fun γ => γ * ν' i γ) = fun γ => (γ * ν i γ) / M i := by
    intro i; funext γ; simp only [hν'def]; ring
  have hν'2 : ∀ i, Integrable (fun γ => γ ^ 2 * ν' i γ) := by
    intro i; rw [e2 i]; exact (hν2 i).div_const (M i)
  have hvar' : ∀ i, τ ^ 2 ≤ (∫ γ, γ ^ 2 * ν' i γ) - (∫ γ, γ * ν' i γ) ^ 2 := by
    intro i
    rw [e2 i, e1 i, integral_div, integral_div]
    have hMi := hM i
    have key : (∫ γ, γ ^ 2 * ν i γ) / M i - ((∫ γ, γ * ν i γ) / M i) ^ 2 =
        ((∫ γ, γ ^ 2 * ν i γ) * M i - (∫ γ, γ * ν i γ) ^ 2) / M i ^ 2 := by
      field_simp
    rw [key, le_div_iff₀ (by positivity)]
    exact hvar i
  have hmain := FSL41_main hd z hz ν' hν'0 hν'int hν'1 hν'2 τ hτ hvar'
  have hprod : ∀ h : Fin d → ℝ, ∏ i, ν i (h i) = (∏ i, M i) * ∏ i, ν' i (h i) := by
    intro h; rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [hν'def]; field_simp [(hM i).ne']
    rw [mul_div_cancel_right₀ _ (hM i).ne']
  have hPM : 0 ≤ ∏ i, M i := Finset.prod_nonneg fun i _ => (hM i).le
  have hsc : ∀ F : (Fin d → ℝ) → ℝ, (∀ h, 0 ≤ F h) →
      ∫⁻ h : Fin d → ℝ, ENNReal.ofReal (F h * ∏ i, ν i (h i)) =
        ENNReal.ofReal (∏ i, M i) * ∫⁻ h : Fin d → ℝ, ENNReal.ofReal (F h * ∏ i, ν' i (h i)) := by
    intro F hF
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun h => ?_
    rw [← ENNReal.ofReal_mul hPM, hprod h]; ring_nf
  rw [hsc _ (fun h => abs_nonneg _), hsc _ (fun h => sq_nonneg _), mul_left_comm]
  gcongr

/-- Infinite second moment in a coordinate with `z i ≠ 0` makes the right side infinite. -/
theorem inf_case {m : ℕ} (z : Fin (m + 1) → ℝ) (ν : Fin (m + 1) → ℝ → ℝ)
    (hpos : ∀ j γ, 0 < ν j γ) (hνm : ∀ j, Measurable (ν j)) (i : Fin (m + 1)) (hzi : z i ≠ 0)
    (hfin : ∫⁻ γ, ENNReal.ofReal (ν i γ) ≠ ⊤)
    (hinf : ∫⁻ γ, ENNReal.ofReal (γ ^ 2 * ν i γ) = ⊤) :
    ∫⁻ h : Fin (m + 1) → ℝ, ENNReal.ofReal ((∑ k, z k * h k) ^ 2 * ∏ k, ν k (h k)) = ⊤ := by
  set F : (Fin (m + 1) → ℝ) → ENNReal :=
    fun h => ENNReal.ofReal ((∑ k, z k * h k) ^ 2 * ∏ k, ν k (h k)) with hF
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i
  have hmp : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i
  have h1 : ∫⁻ p : ℝ × (Fin m → ℝ), F (e.symm p) = ∫⁻ h, F h :=
    hmp.symm.lintegral_comp_emb e.symm.measurableEmbedding F
  -- inner integral is infinite for every fixed c
  have hinner : ∀ c : ℝ, ∫⁻ x, ENNReal.ofReal ((z i * x + c) ^ 2 * ν i x) = ⊤ := by
    intro c
    by_contra hne
    have hz2 : 0 < z i ^ 2 := by positivity
    have hpt : ∀ x, ENNReal.ofReal (x ^ 2 * ν i x) ≤
        ENNReal.ofReal (2 / z i ^ 2) * ENNReal.ofReal ((z i * x + c) ^ 2 * ν i x) +
          ENNReal.ofReal (2 * c ^ 2 / z i ^ 2) * ENNReal.ofReal (ν i x) := by
      intro x
      have hν := (hpos i x).le
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have key : z i ^ 2 * x ^ 2 ≤ 2 * (z i * x + c) ^ 2 + 2 * c ^ 2 := by
        nlinarith [sq_nonneg (z i * x + 2 * c)]
      have : x ^ 2 ≤ 2 / z i ^ 2 * (z i * x + c) ^ 2 + 2 * c ^ 2 / z i ^ 2 := by
        rw [div_mul_eq_mul_div, ← add_div, le_div_iff₀ hz2]; linarith
      calc x ^ 2 * ν i x ≤ (2 / z i ^ 2 * (z i * x + c) ^ 2 + 2 * c ^ 2 / z i ^ 2) * ν i x :=
            mul_le_mul_of_nonneg_right this hν
        _ = _ := by ring
    have hmeas : Measurable fun x =>
        ENNReal.ofReal (2 / z i ^ 2) * ENNReal.ofReal ((z i * x + c) ^ 2 * ν i x) := by
      have := hνm i; fun_prop
    have hsum := lintegral_mono (μ := volume) hpt
    rw [hinf, lintegral_add_left hmeas, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hsum
    have : ENNReal.ofReal (2 / z i ^ 2) * (∫⁻ x, ENNReal.ofReal ((z i * x + c) ^ 2 * ν i x)) +
        ENNReal.ofReal (2 * c ^ 2 / z i ^ 2) * (∫⁻ x, ENNReal.ofReal (ν i x)) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hne,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin⟩
    exact this (top_le_iff.mp hsum)
  -- the slice through each h'
  have hslice : ∀ h' : Fin m → ℝ, ∫⁻ x, F (e.symm (x, h')) = ⊤ := by
    intro h'
    have hP : 0 < ∏ j, ν (i.succAbove j) (h' j) := Finset.prod_pos fun j _ => hpos _ _
    have hrw : ∀ x, F (e.symm (x, h')) = ENNReal.ofReal (∏ j, ν (i.succAbove j) (h' j)) *
        ENNReal.ofReal ((z i * x + ∑ j, z (i.succAbove j) * h' j) ^ 2 * ν i x) := by
      intro x
      rw [← ENNReal.ofReal_mul hP.le, show e.symm (x, h') = Fin.insertNth i x h' from rfl]
      simp only [hF, Fin.sum_univ_succAbove _ i, Fin.prod_univ_succAbove _ i,
        Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      congr 1; ring
    simp_rw [hrw]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hinner]
    exact ENNReal.mul_top (by simpa using hP)
  have hFm : Measurable F := by
    refine ENNReal.measurable_ofReal.comp (Measurable.mul ?_ ?_)
    · exact (Finset.measurable_sum _ fun k _ => by fun_prop).pow_const 2
    · exact Finset.measurable_prod _ fun k _ => (hνm k).comp (measurable_pi_apply k)
  have heq : ∫⁻ p : ℝ × (Fin m → ℝ), F (e.symm p) ∂(volume.prod volume) =
      ∫⁻ h' : Fin m → ℝ, ∫⁻ x : ℝ, F (e.symm (x, h')) :=
    lintegral_prod_symm' (fun p : ℝ × (Fin m → ℝ) => F (e.symm p)) (hFm.comp e.symm.measurable)
  simp_rw [hslice] at heq
  rw [lintegral_const, ENNReal.top_mul (isOpen_univ.measure_ne_zero volume Set.univ_nonempty)] at heq
  rw [← h1]; exact heq

end FSU41

open MeasureTheory

namespace FSU41c

/-- One-coordinate swap: if `G` ignores coordinate `i`, replacing the line density in coordinate
`i` by another of the same mass leaves `∫⁻ G · Π ν` unchanged. -/
theorem swap {m : ℕ} (i : Fin (m + 1)) (G : (Fin (m + 1) → ℝ) → ℝ) (hG0 : ∀ h, 0 ≤ G h)
    (hGm : Measurable G) (hGi : ∀ h γ, G (Function.update h i γ) = G h)
    (ν ν' : Fin (m + 1) → ℝ → ℝ) (hν0 : ∀ k γ, 0 ≤ ν k γ) (hν'0 : ∀ k γ, 0 ≤ ν' k γ)
    (hνm : ∀ k, Measurable (ν k)) (hν'm : ∀ k, Measurable (ν' k))
    (hoff : ∀ k, k ≠ i → ν' k = ν k)
    (hmass : ∫⁻ γ, ENNReal.ofReal (ν i γ) = ∫⁻ γ, ENNReal.ofReal (ν' i γ)) :
    ∫⁻ h, ENNReal.ofReal (G h * ∏ k, ν k (h k)) =
      ∫⁻ h, ENNReal.ofReal (G h * ∏ k, ν' k (h k)) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i
  have hmp : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i
  have key : ∀ ρ : Fin (m + 1) → ℝ → ℝ, (∀ k γ, 0 ≤ ρ k γ) → (∀ k, Measurable (ρ k)) →
      ∫⁻ h, ENNReal.ofReal (G h * ∏ k, ρ k (h k)) =
        ∫⁻ h' : Fin m → ℝ, ENNReal.ofReal (G (Fin.insertNth i 0 h') *
          ∏ j, ρ (i.succAbove j) (h' j)) * ∫⁻ x, ENNReal.ofReal (ρ i x) := by
    intro ρ hρ0 hρm
    set F : (Fin (m + 1) → ℝ) → ENNReal :=
      fun h => ENNReal.ofReal (G h * ∏ k, ρ k (h k)) with hF
    have hFm : Measurable F := by
      refine ENNReal.measurable_ofReal.comp (hGm.mul ?_)
      exact Finset.measurable_prod _ fun k _ => (hρm k).comp (measurable_pi_apply k)
    have h1 : ∫⁻ p : ℝ × (Fin m → ℝ), F (e.symm p) = ∫⁻ h, F h :=
      hmp.symm.lintegral_comp_emb e.symm.measurableEmbedding F
    have heq : ∫⁻ p : ℝ × (Fin m → ℝ), F (e.symm p) ∂(volume.prod volume) =
        ∫⁻ h' : Fin m → ℝ, ∫⁻ x : ℝ, F (e.symm (x, h')) :=
      lintegral_prod_symm' (fun p : ℝ × (Fin m → ℝ) => F (e.symm p)) (hFm.comp e.symm.measurable)
    rw [← h1]
    refine heq.trans (lintegral_congr fun h' => ?_)
    have hP : 0 ≤ G (Fin.insertNth i 0 h') * ∏ j, ρ (i.succAbove j) (h' j) :=
      mul_nonneg (hG0 _) (Finset.prod_nonneg fun j _ => hρ0 _ _)
    have hrw : ∀ x, F (e.symm (x, h')) = ENNReal.ofReal (G (Fin.insertNth i 0 h') *
        ∏ j, ρ (i.succAbove j) (h' j)) * ENNReal.ofReal (ρ i x) := by
      intro x
      rw [← ENNReal.ofReal_mul hP, show e.symm (x, h') = Fin.insertNth i x h' from rfl]
      have hGx : G (Fin.insertNth i x h') = G (Fin.insertNth i 0 h') := by
        have h2 := Fin.update_insertNth (α := fun _ : Fin (m + 1) => ℝ) i (0 : ℝ) x h'
        rw [← h2]; exact hGi _ _
      simp only [hF, hGx]
      rw [Fin.prod_univ_succAbove _ i]
      simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      ring
    simp_rw [hrw]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [key ν hν0 hνm, key ν' hν'0 hν'm, ← hmass]
  congr 1
  funext h'
  congr 3
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hoff _ (Fin.succAbove_ne i j)]

/-- The uniform density of mass `M` on `[-a, a]`. -/
noncomputable def unif (M a : ℝ) : ℝ → ℝ :=
  Set.indicator (Set.Icc (-a) a) (fun _ => M / (2 * a))

lemma unif_nonneg {M a : ℝ} (hM : 0 ≤ M) (ha : 0 < a) (γ : ℝ) : 0 ≤ unif M a γ := by
  unfold unif
  exact Set.indicator_nonneg (fun _ _ => by positivity) γ

lemma unif_meas (M a : ℝ) : Measurable (unif M a) :=
  measurable_const.indicator measurableSet_Icc

lemma unif_mom (M a : ℝ) (ha : 0 < a) (k : ℕ) :
    Integrable (fun γ => γ ^ k * unif M a γ) ∧
      ∫ γ, γ ^ k * unif M a γ = M / (2 * a) * ((a ^ (k + 1) - (-a) ^ (k + 1)) / (k + 1)) := by
  have hrw : (fun γ => γ ^ k * unif M a γ) =
      Set.indicator (Set.Icc (-a) a) (fun γ => γ ^ k * (M / (2 * a))) := by
    funext γ; unfold unif
    by_cases hγ : γ ∈ Set.Icc (-a) a
    · simp [Set.indicator_of_mem hγ]
    · simp [Set.indicator_of_notMem hγ]
  rw [hrw]
  constructor
  · rw [integrable_indicator_iff measurableSet_Icc]
    exact (Continuous.integrableOn_Icc (by fun_prop))
  · rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_mul_const,
      integral_pow]
    ring

lemma unif_int (M a : ℝ) (ha : 0 < a) : Integrable (unif M a) := by
  have := (unif_mom M a ha 0).1
  simpa using this

lemma unif_total (M a : ℝ) (ha : 0 < a) : ∫ γ, unif M a γ = M := by
  have := (unif_mom M a ha 0).2
  simp only [pow_zero, one_mul] at this
  rw [this]; field_simp; ring

lemma unif_var (M a τ : ℝ) (ha : 0 < a) (hM : 0 ≤ M) (hτa : 3 * τ ^ 2 ≤ a ^ 2) :
    τ ^ 2 * (∫ γ, unif M a γ) ^ 2 ≤
      (∫ γ, γ ^ 2 * unif M a γ) * (∫ γ, unif M a γ) - (∫ γ, γ * unif M a γ) ^ 2 := by
  have h2 := (unif_mom M a ha 2).2
  have h1 := (unif_mom M a ha 1).2
  simp only [pow_one] at h1
  rw [unif_total M a ha, h2, h1]
  have hx : M / (2 * a) * ((a ^ (2 + 1) - (-a) ^ (2 + 1)) / ((2 : ℕ) + 1 : ℝ)) = M * a ^ 2 / 3 := by
    field_simp; ring
  have hy : M / (2 * a) * ((a ^ (1 + 1) - (-a) ^ (1 + 1)) / ((1 : ℕ) + 1 : ℝ)) = 0 := by
    ring
  rw [hx, hy]
  have : τ ^ 2 * M ^ 2 ≤ M * a ^ 2 / 3 * M := by
    have := mul_le_mul_of_nonneg_left hτa (sq_nonneg M)
    nlinarith
  linarith

lemma unif_lmass (M a : ℝ) (ha : 0 < a) (hM : 0 ≤ M) :
    ∫⁻ γ, ENNReal.ofReal (unif M a γ) = ENNReal.ofReal M := by
  rw [← ofReal_integral_eq_lintegral_ofReal (unif_int M a ha)
    (Filter.Eventually.of_forall (unif_nonneg hM ha)), unif_total M a ha]

end FSU41c

namespace FSU41full
open MeasureTheory

lemma G_ignore {d : ℕ} (z : Fin d → ℝ) (φ : ℝ → ℝ) (j : Fin d) (hz : z j = 0)
    (h : Fin d → ℝ) (γ : ℝ) :
    φ (∑ k, z k * Function.update h j γ k) = φ (∑ k, z k * h k) := by
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k = j
  · subst hk; simp [hz]
  · rw [Function.update_of_ne hk]

lemma meas_lin {d : ℕ} (z : Fin d → ℝ) : Measurable (fun h : Fin d → ℝ => ∑ k, z k * h k) :=
  Finset.measurable_sum _ fun k _ => Measurable.const_mul (measurable_pi_apply (X := fun _ : Fin d => ℝ) k) (z k)

lemma swap_all {m : ℕ} (z : Fin (m + 1) → ℝ) (φ : ℝ → ℝ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hφm : Measurable φ) (ν ν' : Fin (m + 1) → ℝ → ℝ) (hν0 : ∀ k γ, 0 ≤ ν k γ)
    (hν'0 : ∀ k γ, 0 ≤ ν' k γ) (hνm : ∀ k, Measurable (ν k)) (hν'm : ∀ k, Measurable (ν' k))
    (hcase : ∀ k, ν' k = ν k ∨
      (z k = 0 ∧ ∫⁻ γ, ENNReal.ofReal (ν k γ) = ∫⁻ γ, ENNReal.ofReal (ν' k γ))) :
    ∫⁻ h : Fin (m + 1) → ℝ, ENNReal.ofReal (φ (∑ k, z k * h k) * ∏ k, ν k (h k)) =
      ∫⁻ h : Fin (m + 1) → ℝ, ENNReal.ofReal (φ (∑ k, z k * h k) * ∏ k, ν' k (h k)) := by
  classical
  let ρ : Finset (Fin (m + 1)) → Fin (m + 1) → ℝ → ℝ := fun S k => if k ∈ S then ν' k else ν k
  have hρ0 : ∀ S k γ, 0 ≤ ρ S k γ := by
    intro S k γ; dsimp only [ρ]; split_ifs
    · exact hν'0 k γ
    · exact hν0 k γ
  have hρm : ∀ S k, Measurable (ρ S k) := by
    intro S k; dsimp only [ρ]; split_ifs
    · exact hν'm k
    · exact hνm k
  have hall : ∀ S : Finset (Fin (m + 1)),
      ∫⁻ h : Fin (m + 1) → ℝ, ENNReal.ofReal (φ (∑ k, z k * h k) * ∏ k, ν k (h k)) =
        ∫⁻ h : Fin (m + 1) → ℝ, ENNReal.ofReal (φ (∑ k, z k * h k) * ∏ k, ρ S k (h k)) := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · simp [ρ]
    · intro j S hj ih
      rw [ih]
      rcases hcase j with heq | ⟨hz, hmass⟩
      · congr 1; funext h; congr 2
        refine Finset.prod_congr rfl fun k _ => ?_
        dsimp only [ρ]
        by_cases hk : k = j
        · subst hk; simp [hj, heq]
        · simp [Finset.mem_insert, hk]
      · exact FSU41c.swap j (fun h => φ (∑ k, z k * h k)) (fun _ => hφ0 _)
          (hφm.comp (meas_lin z)) (fun h γ => G_ignore z φ j hz h γ) (ρ S) (ρ (insert j S))
          (hρ0 S) (hρ0 _) (hρm S) (hρm _)
          (fun k hk => by dsimp only [ρ]; simp [Finset.mem_insert, hk])
          (by dsimp only [ρ]; simp [hj, hmass])
  rw [hall Finset.univ]
  simp [ρ]

/-- Unnormalised Lemma 41 for positive measurable integrable line densities, with the variance
condition only required where the second moment is finite (the `LineVarianceGE` form). -/
theorem full {d : ℕ} (hd : 3 ≤ d) (z : Fin d → ℝ) (hz : ∑ i, |z i| = 1)
    (ν : Fin d → ℝ → ℝ) (hpos : ∀ i γ, 0 < ν i γ) (hνm : ∀ i, Measurable (ν i))
    (hνint : ∀ i, Integrable (ν i)) (τ : ℝ) (hτ : 0 ≤ τ)
    (hvar : ∀ i, Integrable (fun γ => γ ^ 2 * ν i γ) → τ ^ 2 * (∫ γ, ν i γ) ^ 2 ≤
      (∫ γ, γ ^ 2 * ν i γ) * (∫ γ, ν i γ) - (∫ γ, γ * ν i γ) ^ 2) :
    ENNReal.ofReal (τ / (2 * Real.sqrt d)) *
        ∫⁻ h : Fin d → ℝ, ENNReal.ofReal (|∑ i, z i * h i| * ∏ i, ν i (h i)) ≤
      ∫⁻ h : Fin d → ℝ, ENNReal.ofReal ((∑ i, z i * h i) ^ 2 * ∏ i, ν i (h i)) := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have hM : ∀ i, 0 < ∫ γ, ν i γ := by
    intro i
    rw [integral_pos_iff_support_of_nonneg (fun γ => (hpos i γ).le) (hνint i)]
    have : Function.support (ν i) = Set.univ :=
      Set.eq_univ_of_forall fun γ => (hpos i γ).ne'
    rw [this, Real.volume_univ]; exact ENNReal.zero_lt_top
  by_cases hA : ∃ i, z i ≠ 0 ∧ ¬ Integrable (fun γ => γ ^ 2 * ν i γ)
  · obtain ⟨i, hzi, hni⟩ := hA
    have hinf : ∫⁻ γ, ENNReal.ofReal (γ ^ 2 * ν i γ) = ⊤ := by
      by_contra hne
      apply hni
      refine ⟨((measurable_id.pow_const 2).mul (hνm i)).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun γ =>
        mul_nonneg (sq_nonneg γ) (hpos i γ).le)]
      exact lt_top_iff_ne_top.2 hne
    rw [FSU41.inf_case z ν hpos hνm i hzi (hνint i).lintegral_lt_top.ne hinf]
    exact le_top
  simp only [not_exists, not_and, not_not] at hA
  set a : ℝ := 2 * τ + 1 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have hτa : 3 * τ ^ 2 ≤ a ^ 2 := by rw [ha]; nlinarith
  set ν' : Fin (m + 1) → ℝ → ℝ :=
    fun k => if z k = 0 then FSU41c.unif (∫ γ, ν k γ) a else ν k with hν'
  have hν'0 : ∀ k γ, 0 ≤ ν' k γ := by
    intro k γ; simp only [hν']; split_ifs
    · exact FSU41c.unif_nonneg (hM k).le ha0 γ
    · exact (hpos k γ).le
  have hν'm : ∀ k, Measurable (ν' k) := by
    intro k; simp only [hν']; split_ifs
    · exact FSU41c.unif_meas _ _
    · exact hνm k
  have hcase : ∀ k, ν' k = ν k ∨
      (z k = 0 ∧ ∫⁻ γ, ENNReal.ofReal (ν k γ) = ∫⁻ γ, ENNReal.ofReal (ν' k γ)) := by
    intro k
    by_cases hk : z k = 0
    · right; refine ⟨hk, ?_⟩
      simp only [hν', if_pos hk]
      rw [FSU41c.unif_lmass _ _ ha0 (hM k).le, ofReal_integral_eq_lintegral_ofReal (hνint k)
        (Filter.Eventually.of_forall fun γ => (hpos k γ).le)]
    · left; simp only [hν', if_neg hk]
  have hν0 : ∀ k γ, 0 ≤ ν k γ := fun k γ => (hpos k γ).le
  rw [swap_all z (fun x => |x|) (fun x => abs_nonneg x) measurable_id.abs ν ν' hν0 hν'0 hνm hν'm
      hcase,
    swap_all z (fun x => x ^ 2) (fun x => sq_nonneg x) (measurable_id.pow_const 2) ν ν' hν0 hν'0
      hνm hν'm hcase]
  refine FSU41.fin_case hd z hz ν' hν'0 ?_ ?_ ?_ τ hτ ?_
  · intro k; simp only [hν']; split_ifs
    · exact FSU41c.unif_int _ _ ha0
    · exact hνint k
  · intro k; simp only [hν']; split_ifs
    · rw [FSU41c.unif_total _ _ ha0]; exact hM k
    · exact hM k
  · intro k; simp only [hν']; split_ifs with hk
    · exact (FSU41c.unif_mom _ _ ha0 2).1
    · exact hA k hk
  · intro k; simp only [hν']; split_ifs with hk
    · exact FSU41c.unif_var _ _ _ ha0 (hM k).le hτa
    · exact hvar k (hA k hk)

end FSU41full

namespace FSSlice
open FriendlyShadow.Gaussian MeasureTheory RealInnerProductSpace

/-- SLICE: for a fixed allowed shape `s` and point `p`, Lemma 39 (translations) followed by the
unnormalised Lemma 41 (heights, pointwise in `q`). The right side carries `(Σ zᵢhᵢ)²`:
edge length `chordLen · |Σ zh|` times the Jacobian factor `|Σ zh|`. -/
theorem slice {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    (s : Fin d → EuclideanSpace ℝ (Fin (d - 2))) (hs0 : s 0 = 0)
    (hrank : Module.finrank ℝ (Submodule.span ℝ (Set.range s)) = d - 2)
    (L R : ℝ) (hL : 0 < L) (hR : 0 ≤ R) (hdiam : ∀ i j, ‖s i - s j‖ ≤ 2 + 2 * R)
    (hLR : (d : ℝ) / 3 ≤ L * R) (z : Fin d → ℝ) (hz : IsKernelComb s z)
    (mubar : Fin d → EuclideanSpace ℝ (Fin (d - 2)) → ℝ → ℝ)
    (hpos : ∀ i u h, 0 < mubar i u h)
    (hlip : ∀ i u u' h h', mubar i u h ≤
      Real.exp (L * Real.sqrt (‖u - u'‖ ^ 2 + (h - h') ^ 2)) * mubar i u' h')
    (hmeas : ∀ i u, Measurable (mubar i u)) (hint : ∀ i u, Integrable (mubar i u))
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hvar : ∀ i u, Integrable (fun γ => γ ^ 2 * mubar i u γ) →
      τ ^ 2 * (∫ γ, mubar i u γ) ^ 2 ≤
        (∫ γ, γ ^ 2 * mubar i u γ) * (∫ γ, mubar i u γ) - (∫ γ, γ * mubar i u γ) ^ 2)
    (p : EuclideanSpace ℝ (Fin (d - 2))) :
    ENNReal.ofReal (Real.exp (-2) / (d * L * (1 + R)) * (τ / (2 * Real.sqrt d))) *
        ∫⁻ q in convexHull ℝ (Set.range s), heightMarginal mubar s z (p - q) ≤
      ∫⁻ q in convexHull ℝ (Set.range s), ENNReal.ofReal (chordLen s q) *
        ∫⁻ h : Fin d → ℝ, ENNReal.ofReal ((∑ i, z i * h i) ^ 2 *
          ∏ i, mubar i (p - q + s i) (h i)) := by
  set c1 := Real.exp (-2) / (d * L * (1 + R)) with hc1def
  set c2 := τ / (2 * Real.sqrt d) with hc2def
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hc1 : 0 ≤ c1 :=
    div_nonneg (Real.exp_pos _).le (mul_nonneg (mul_nonneg hd0 hL.le) (by linarith))
  have h39 := FSL39_main hd s hs0 hrank L R hL hR hdiam hLR z hz mubar hpos hlip p
  have h41 : ∀ q, ENNReal.ofReal c2 * heightMarginal mubar s z (p - q) ≤
      ∫⁻ h : Fin d → ℝ, ENNReal.ofReal ((∑ i, z i * h i) ^ 2 *
        ∏ i, mubar i (p - q + s i) (h i)) := by
    intro q
    exact FSU41full.full hd z hz.2.2 (fun i => mubar i (p - q + s i))
      (fun i γ => hpos _ _ _) (fun i => hmeas _ _) (fun i => hint _ _) τ hτ
      (fun i => hvar i _)
  calc ENNReal.ofReal (c1 * c2) *
        ∫⁻ q in convexHull ℝ (Set.range s), heightMarginal mubar s z (p - q)
      = ENNReal.ofReal c2 * (ENNReal.ofReal c1 *
          ∫⁻ q in convexHull ℝ (Set.range s), heightMarginal mubar s z (p - q)) := by
        rw [ENNReal.ofReal_mul hc1]; ring
    _ ≤ ENNReal.ofReal c2 * ∫⁻ q in convexHull ℝ (Set.range s),
          ENNReal.ofReal (chordLen s q) * heightMarginal mubar s z (p - q) := by
        gcongr
    _ = ∫⁻ q in convexHull ℝ (Set.range s),
          ENNReal.ofReal (chordLen s q) * (ENNReal.ofReal c2 * heightMarginal mubar s z (p - q)) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun q => ?_
        ring
    _ ≤ _ := by
        refine lintegral_mono fun q => ?_
        gcongr
        exact h41 q

end FSSlice


-- ===== C7C.lean =====

open scoped RealInnerProductSpace

set_option autoImplicit false


open FriendlyShadow.Gaussian RealInnerProductSpace in
theorem FSL36_diam_main {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {d : ℕ}
    [NeZero d] (hd : 3 ≤ d) (b : Fin d → V) (ω : V) (hω : ‖ω‖ = 1)
    (hrank : Module.finrank ℝ (Submodule.span ℝ (Set.range (shapeOf ω b))) = d - 2)
    (z : Fin d → ℝ) (hz : IsKernelComb (shapeOf ω b) z)
    (q : V) (hq : q ∈ convexHull ℝ (Set.range (shapeOf ω b))) :
    Metric.diam ({p | ∃ t : ℝ, p = projPerp ω (b 0) + q + t • ω} ∩
        convexHull ℝ (Set.range b)) =
      chordLen (shapeOf ω b) q * |∑ i, z i * ⟪ω, b i⟫| := by
  set s := shapeOf ω b with hs
  set x := projPerp ω (b 0) with hx
  set T := ({p | ∃ t : ℝ, p = x + q + t • ω} ∩ convexHull ℝ (Set.range b)) with hT
  set H := |∑ i, z i * ⟪ω, b i⟫| with hH
  have hs0 : s 0 = 0 := by simp [hs, shapeOf]
  have hqω : ⟪ω, q⟫ = 0 := by
    obtain ⟨l, -, -, rfl⟩ := (FSL36.hull_iff _ q).mp hq
    exact FSL36.inner_comb ω hω b l
  -- a point of the chord set
  obtain ⟨l0, hl00, hl01, hl0s⟩ := (FSL36.hull_iff _ q).mp hq
  have hl0 : l0 ∈ chordSet s q := ⟨hl00, hl01, hl0s⟩
  -- key identity
  have key : ∀ l ∈ chordSet s q, ∀ l' ∈ chordSet s q,
      dist (x + q + (∑ i, l i * ⟪ω, b i⟫) • ω) (x + q + (∑ i, l' i * ⟪ω, b i⟫) • ω) =
        (∑ i, |l i - l' i|) * H := by
    intro l hl l' hl'
    obtain ⟨c, hc⟩ := FSL36.diff_mul hd s hs0 hrank z hz q l l' hl hl'
    rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hω, mul_one,
      Real.norm_eq_abs, ← Finset.sum_sub_distrib]
    have e1 : ∑ i, (l i * ⟪ω, b i⟫ - l' i * ⟪ω, b i⟫) = c * ∑ i, z i * ⟪ω, b i⟫ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← sub_mul, hc i]; ring
    have e2 : ∑ i, |l i - l' i| = |c| := by
      simp only [hc, abs_mul, ← Finset.mul_sum, hz.2.2, mul_one]
    rw [e1, e2, abs_mul, hH]
  set D := {t | ∃ l ∈ chordSet s q, ∃ l' ∈ chordSet s q, t = ∑ i, |l i - l' i|} with hD
  have hDbdd : BddAbove D := ⟨2, by rintro _ ⟨l, hl, l', hl', rfl⟩; exact FSL36.sum_abs_le_two hl hl'⟩
  have hDne : D.Nonempty := ⟨_, l0, hl0, l0, hl0, rfl⟩
  have hCL : chordLen s q = sSup D := rfl
  have hCL0 : 0 ≤ chordLen s q := by
    rw [hCL]
    exact le_csSup_of_le hDbdd ⟨l0, hl0, l0, hl0, rfl⟩ (by simp)
  have hTbdd : Bornology.IsBounded T :=
    (show IsCompact (convexHull ℝ (Set.range b)) from
      Set.Finite.isCompact_convexHull (𝕜 := ℝ) (Set.finite_range b)).isBounded.subset Set.inter_subset_right
  have hmem : ∀ l ∈ chordSet s q, x + q + (∑ i, l i * ⟪ω, b i⟫) • ω ∈ T := fun l hl =>
    (FSL36.mem_T b ω hω q hqω _).mpr ⟨l, hl, rfl⟩
  apply le_antisymm
  · apply Metric.diam_le_of_forall_dist_le (mul_nonneg hCL0 (abs_nonneg _))
    intro p hp p' hp'
    obtain ⟨l, hl, rfl⟩ := (FSL36.mem_T b ω hω q hqω p).mp hp
    obtain ⟨l', hl', rfl⟩ := (FSL36.mem_T b ω hω q hqω p').mp hp'
    rw [key l hl l' hl']
    exact mul_le_mul_of_nonneg_right (le_csSup hDbdd ⟨l, hl, l', hl', rfl⟩) (abs_nonneg _)
  · rcases (abs_nonneg (∑ i, z i * ⟪ω, b i⟫)).eq_or_lt with h0 | hpos
    · rw [← hH] at h0; rw [← h0, mul_zero]; exact Metric.diam_nonneg
    · rw [← hH] at hpos
      rw [← le_div_iff₀ hpos, hCL]
      refine csSup_le hDne ?_
      rintro _ ⟨l, hl, l', hl', rfl⟩
      rw [le_div_iff₀ hpos, ← key l hl l' hl']
      exact Metric.dist_le_diam_of_mem hTbdd (hmem l hl) (hmem l' hl')

/-! C7c: in the per-hyperplane frame `b i = o + ι (u i) + h i • ω`, the section `conv(b) ∩ W`
is the chord line of lemma 36, with length `chordLen s (-u 0) * |Σ z h|`. -/
namespace FSC7C
open FriendlyShadow.Gaussian

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma comb_expand {k : ℕ} (o ω : V) (ι : EuclideanSpace ℝ (Fin (k + 1)) →ₗᵢ[ℝ] V)
    (u : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1))) (h : Fin (k + 3) → ℝ) (l : Fin (k + 3) → ℝ) :
    ∑ i, l i • (o + ι (u i) + h i • ω) =
      (∑ i, l i) • o + ι (∑ i, l i • u i) + (∑ i, l i * h i) • ω := by
  simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, map_sum, map_smul, smul_smul]

lemma inner_ω_ι {k : ℕ} (ω : V) (ι : EuclideanSpace ℝ (Fin (k + 1)) →ₗᵢ[ℝ] V)
    (hιω : ∀ x, ⟪ι x, ω⟫ = 0) (x : EuclideanSpace ℝ (Fin (k + 1))) : ⟪ω, ι x⟫ = 0 := by
  rw [real_inner_comm]; exact hιω x

lemma projPerp_b0 {k : ℕ} (o ω : V) (hω : ‖ω‖ = 1) (ι : EuclideanSpace ℝ (Fin (k + 1)) →ₗᵢ[ℝ] V)
    (hιω : ∀ x, ⟪ι x, ω⟫ = 0) (x : EuclideanSpace ℝ (Fin (k + 1))) (t : ℝ) :
    projPerp ω (o + ι x + t • ω) = o + ι x - ⟪ω, o⟫ • ω := by
  have hωω : ⟪ω, ω⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hω]; norm_num
  simp only [projPerp, inner_add_right, inner_smul_right, inner_ω_ι ω ι hιω, hωω]
  module

theorem inter_line {k : ℕ} (W : Submodule ℝ V) (o ω : V)
    (ι : EuclideanSpace ℝ (Fin (k + 1)) →ₗᵢ[ℝ] V) (hoW : o ∈ W) (hωW : ω ∈ W) (hω : ‖ω‖ = 1)
    (hιω : ∀ x, ⟪ι x, ω⟫ = 0) (hWx : ∀ x (t : ℝ), o + ι x + t • ω ∈ W → x = 0)
    (u : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1))) (h : Fin (k + 3) → ℝ) :
    convexHull ℝ (Set.range fun i => o + ι (u i) + h i • ω) ∩ (W : Set V) =
      {p | ∃ t : ℝ, p = projPerp ω ((fun i => o + ι (u i) + h i • ω) 0) + -ι (u 0) + t • ω} ∩
        convexHull ℝ (Set.range fun i => o + ι (u i) + h i • ω) := by
  rw [projPerp_b0 o ω hω ι hιω]
  ext p
  constructor
  · rintro ⟨hp, hpW⟩
    refine ⟨?_, hp⟩
    obtain ⟨l, -, hl1, rfl⟩ := (FSL36.hull_iff _ p).mp hp
    rw [comb_expand, hl1, one_smul] at hpW ⊢
    have h0 := hWx _ _ hpW
    refine ⟨(∑ i, l i * h i) + ⟪ω, o⟫, ?_⟩
    rw [h0, map_zero]
    module
  · rintro ⟨⟨t, rfl⟩, hp⟩
    refine ⟨hp, ?_⟩
    have : o + ι (u 0) - ⟪ω, o⟫ • ω + -ι (u 0) + t • ω = o + (t - ⟪ω, o⟫) • ω := by module
    rw [this]
    exact W.add_mem hoW (W.smul_mem _ hωW)

theorem slice_diam {k : ℕ} (W : Submodule ℝ V) (o ω : V)
    (ι : EuclideanSpace ℝ (Fin (k + 1)) →ₗᵢ[ℝ] V) (hoW : o ∈ W) (hωW : ω ∈ W) (hω : ‖ω‖ = 1)
    (hιω : ∀ x, ⟪ι x, ω⟫ = 0) (hWx : ∀ x (t : ℝ), o + ι x + t • ω ∈ W → x = 0)
    (u : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1))) (h : Fin (k + 3) → ℝ)
    (z : Fin (k + 3) → ℝ) (hz : IsKernelComb (fun i => u i - u 0) z)
    (hrank : Module.finrank ℝ (Submodule.span ℝ (Set.range fun i => u i - u 0)) = k + 1)
    (hq : -u 0 ∈ convexHull ℝ (Set.range fun i => u i - u 0)) :
    Metric.diam (convexHull ℝ (Set.range fun i => o + ι (u i) + h i • ω) ∩ (W : Set V)) =
      chordLen (fun i => u i - u 0) (-u 0) * |∑ i, z i * h i| := by
  set b : Fin (k + 3) → V := fun i => o + ι (u i) + h i • ω with hb
  set s : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1)) := fun i => u i - u 0 with hs
  have hωω : ⟪ω, ω⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hω]; norm_num
  have hshape : shapeOf ω b = fun i => ι (s i) := by
    funext i
    simp only [shapeOf, hb, projPerp_b0 o ω hω ι hιω, hs, map_sub]
    abel
  have hinj : Function.Injective ι := ι.injective
  have hrank' : Module.finrank ℝ (Submodule.span ℝ (Set.range (shapeOf ω b))) = k + 3 - 2 := by
    rw [hshape, show (Set.range fun i => ι (s i)) = ι.toLinearMap '' Set.range s by
      rw [← Set.range_comp]; rfl, Submodule.span_image,
      ← (Submodule.equivMapOfInjective ι.toLinearMap hinj _).finrank_eq, hrank]
    omega
  have hz' : IsKernelComb (shapeOf ω b) z := by
    obtain ⟨h1, h2, h3⟩ := hz
    refine ⟨?_, h2, h3⟩
    rw [hshape]
    simp only [← map_smul, ← map_sum]
    rw [show (∑ i, z i • s i) = 0 from h1, map_zero]
  have hconv : convexHull ℝ (Set.range (shapeOf ω b)) =
      ι.toLinearMap '' convexHull ℝ (Set.range s) := by
    rw [LinearMap.image_convexHull, hshape, ← Set.range_comp]; rfl
  have hq' : -ι (u 0) ∈ convexHull ℝ (Set.range (shapeOf ω b)) := by
    rw [hconv]
    exact ⟨-u 0, hq, by simp⟩
  have hchord : chordSet (shapeOf ω b) (-ι (u 0)) = chordSet s (-u 0) := by
    ext l
    simp only [chordSet, Set.mem_setOf_eq, hshape]
    constructor
    · rintro ⟨h0, h1, h2⟩
      refine ⟨h0, h1, hinj ?_⟩
      rw [map_sum, map_neg]; simpa [map_smul] using h2
    · rintro ⟨h0, h1, h2⟩
      refine ⟨h0, h1, ?_⟩
      rw [← map_neg ι (u 0), ← h2, map_sum]; simp [map_smul]
  have hmain := FSL36_diam_main (V := V) (d := k + 3) (by omega) b ω hω hrank' z hz'
    (-ι (u 0)) hq'
  rw [inter_line W o ω ι hoW hωW hω hιω hWx u h, hmain]
  congr 1
  · simp only [chordLen, hchord]
  · congr 1
    have : ∀ i, ⟪ω, b i⟫ = ⟪ω, o⟫ + h i := by
      intro i
      simp only [hb, inner_add_right, inner_smul_right, inner_ω_ι ω ι hιω, hωω]; ring
    simp_rw [this, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hz.2.1, zero_mul, zero_add]

end FSC7C

/-! C7d: the slice section is a segment (nondegenerate when its diameter is positive);
`ediam = ofReal diam` for bounded sets. -/
namespace FSC7C
open FriendlyShadow.Gaussian

lemma ediam_eq {X : Type*} [PseudoMetricSpace X] (K : Set X) (hK : Bornology.IsBounded K) :
    Metric.ediam K = ENNReal.ofReal (Metric.diam K) := by
  rw [Metric.diam, ENNReal.ofReal_toReal hK.ediam_ne_top]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem seg_of_line (c ω : V) (hω : ω ≠ 0) (K : Set V) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hline : K ⊆ {p | ∃ t : ℝ, p = c + t • ω}) :
    ∃ t1 t2 : ℝ, t1 ≤ t2 ∧ K = segment ℝ (c + t1 • ω) (c + t2 • ω) := by
  set f : ℝ →ᵃ[ℝ] V := AffineMap.lineMap c (c + ω) with hfdef
  have hf : ∀ t : ℝ, f t = c + t • ω := by
    intro t; rw [hfdef, AffineMap.lineMap_apply_module]; module
  have hfc : Continuous f := by
    have : (f : ℝ → V) = fun t => c + t • ω := funext hf
    rw [this]; fun_prop
  set T : Set ℝ := f ⁻¹' K with hT
  have hTcl : IsClosed T := hK.isClosed.preimage hfc
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall c).1 hK.isBounded
  have hωpos : 0 < ‖ω‖ := norm_pos_iff.2 hω
  have hTsub : T ⊆ Set.Icc (-(r / ‖ω‖)) (r / ‖ω‖) := by
    intro t ht
    have h1 := hr ht
    rw [Metric.mem_closedBall, hf, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs] at h1
    have h2 : |t| ≤ r / ‖ω‖ := (le_div_iff₀ hωpos).2 h1
    exact ⟨by linarith [neg_abs_le t], le_trans (le_abs_self t) h2⟩
  have hTc : IsCompact T :=
    Metric.isCompact_of_isClosed_isBounded hTcl (Metric.isBounded_Icc _ _ |>.subset hTsub)
  have hTne : T.Nonempty := by
    obtain ⟨p, hp⟩ := hne
    obtain ⟨t, rfl⟩ := hline hp
    exact ⟨t, by rw [hT, Set.mem_preimage, hf]; exact hp⟩
  have hTconv : Convex ℝ T := hconv.affine_preimage f
  set t1 := sInf T
  set t2 := sSup T
  have ht1 : t1 ∈ T := hTc.sInf_mem hTne
  have ht2 : t2 ∈ T := hTc.sSup_mem hTne
  have h12 : t1 ≤ t2 := csInf_le hTc.bddBelow ht2
  have hTeq : T = Set.Icc t1 t2 := by
    apply Set.Subset.antisymm
    · intro t ht
      exact ⟨csInf_le hTc.bddBelow ht, le_csSup hTc.bddAbove ht⟩
    · exact (convex_iff_ordConnected.1 hTconv).out ht1 ht2
  have hKeq : K = f '' T := by
    apply Set.Subset.antisymm
    · intro p hp
      obtain ⟨t, rfl⟩ := hline hp
      exact ⟨t, by rw [hT, Set.mem_preimage, hf]; exact hp, hf t⟩
    · exact Set.image_preimage_subset f K
  refine ⟨t1, t2, h12, ?_⟩
  rw [hKeq, hTeq, ← segment_eq_Icc h12, image_segment, hf, hf]

/-- The slice section `conv(b) ∩ W` with positive diameter is a nondegenerate segment. -/
theorem slice_seg [FiniteDimensional ℝ V] {k : ℕ} (W : Submodule ℝ V) (o ω : V)
    (ι : EuclideanSpace ℝ (Fin (k + 1)) →ₗᵢ[ℝ] V) (hoW : o ∈ W) (hωW : ω ∈ W) (hω : ‖ω‖ = 1)
    (hιω : ∀ x, ⟪ι x, ω⟫ = 0) (hWx : ∀ x (t : ℝ), o + ι x + t • ω ∈ W → x = 0)
    (u : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1))) (h : Fin (k + 3) → ℝ)
    (hpos : 0 < Metric.diam (convexHull ℝ (Set.range fun i => o + ι (u i) + h i • ω) ∩
      (W : Set V))) :
    ∃ p1 p2 : V, p1 ≠ p2 ∧
      convexHull ℝ (Set.range fun i => o + ι (u i) + h i • ω) ∩ (W : Set V) =
        segment ℝ p1 p2 := by
  set K := convexHull ℝ (Set.range fun i => o + ι (u i) + h i • ω) ∩ (W : Set V) with hKdef
  have hω0 : ω ≠ 0 := by rintro rfl; simp at hω
  have hKc : IsCompact K :=
    ((Set.finite_range (fun i => o + ι (u i) + h i • ω)).isCompact_convexHull (𝕜 := ℝ)).inter_right
      (Submodule.closed_of_finiteDimensional W)
  have hKconv : Convex ℝ K := (convex_convexHull ℝ _).inter W.convex
  have hKne : K.Nonempty := by
    by_contra h0
    rw [Set.not_nonempty_iff_eq_empty] at h0
    rw [h0, Metric.diam_empty] at hpos
    exact lt_irrefl _ hpos
  have hline : K ⊆ {p | ∃ t : ℝ,
      p = projPerp ω ((fun i => o + ι (u i) + h i • ω) 0) + -ι (u 0) + t • ω} := by
    rw [hKdef, inter_line W o ω ι hoW hωW hω hιω hWx u h]
    exact Set.inter_subset_left
  obtain ⟨t1, t2, -, hseg⟩ := seg_of_line _ ω hω0 K hKc hKconv hKne hline
  refine ⟨_, _, ?_, hseg⟩
  intro heq
  rw [hseg, heq, segment_same ℝ, Metric.diam_singleton] at hpos
  exact lt_irrefl _ hpos

end FSC7C

namespace FSC7C
open FriendlyShadow.Gaussian

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A nonempty slice section forces `q = -u 0 ∈ conv(s)`. -/
theorem slice_mem_hull {k : ℕ} (W : Submodule ℝ V) (o ω : V)
    (ι : EuclideanSpace ℝ (Fin (k + 1)) →ₗᵢ[ℝ] V) (hoW : o ∈ W) (hωW : ω ∈ W) (hω : ‖ω‖ = 1)
    (hιω : ∀ x, ⟪ι x, ω⟫ = 0) (hWx : ∀ x (t : ℝ), o + ι x + t • ω ∈ W → x = 0)
    (u : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1))) (h : Fin (k + 3) → ℝ)
    (hne : (convexHull ℝ (Set.range fun i => o + ι (u i) + h i • ω) ∩ (W : Set V)).Nonempty) :
    -u 0 ∈ convexHull ℝ (Set.range fun i => u i - u 0) := by
  set b : Fin (k + 3) → V := fun i => o + ι (u i) + h i • ω with hb
  have hshape : shapeOf ω b = fun i => ι (u i - u 0) := by
    funext i
    simp only [shapeOf, hb, projPerp_b0 o ω hω ι hιω, map_sub]
    abel
  obtain ⟨p, hp⟩ := hne
  rw [inter_line W o ω ι hoW hωW hω hιω hWx u h] at hp
  have hq : ⟪ω, -ι (u 0)⟫ = 0 := by rw [inner_neg_right, inner_ω_ι ω ι hιω, neg_zero]
  obtain ⟨l, ⟨hl0, hl1, hls⟩, -⟩ := (FSL36.mem_T b ω hω (-ι (u 0)) hq p).1 hp
  rw [hshape] at hls
  refine (FSL36.hull_iff _ _).2 ⟨l, hl0, hl1, ι.injective ?_⟩
  rw [map_sum, map_neg, ← hls]
  simp [map_smul]

end FSC7C


-- ===== FACE7.lean =====

set_option autoImplicit false



/-! O1c/O1b general position: almost surely (rows with densities)
(G1) any d+1 rows affinely span ℝᵈ, (G2) W together with any d-2 rows spans ℝᵈ. -/

namespace FSGP

open MeasureTheory FriendlyShadow.Gaussian
open scoped ENNReal

theorem meas_bad {d n k : ℕ} (c : (Fin n → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    (g : (Fin n → EuclideanSpace ℝ (Fin d)) → Fin k → EuclideanSpace ℝ (Fin d))
    (hc : Continuous c) (hg : Continuous g) (i : Fin n) :
    MeasurableSet {a : Fin n → EuclideanSpace ℝ (Fin d) |
      a i - c a ∈ Submodule.span ℝ (Set.range (g a))} := by
  set C : Set ((Fin k → ℝ) × (Fin n → EuclideanSpace ℝ (Fin d))) :=
    {p | ∑ j, p.1 j • g p.2 j = p.2 i - c p.2} with hCdef
  have hCc : IsClosed C := isClosed_eq (by fun_prop) (by fun_prop)
  have hC : IsSigmaCompact C := isSigmaCompact_univ.of_isClosed_subset hCc (Set.subset_univ _)
  have himg : {a : Fin n → EuclideanSpace ℝ (Fin d) |
      a i - c a ∈ Submodule.span ℝ (Set.range (g a))} = Prod.snd '' C := by
    ext a
    simp only [Set.mem_ofPred_eq, Submodule.mem_span_range_iff_exists_fun, Set.mem_image]
    constructor
    · rintro ⟨f, hf⟩; exact ⟨(f, a), hf, rfl⟩
    · rintro ⟨q, hq, rfl⟩; exact ⟨q.1, hq⟩
  obtain ⟨K, hK, hU⟩ := hC.image continuous_snd
  rw [himg, ← hU]
  exact MeasurableSet.iUnion fun m => (hK m).isClosed.measurableSet

theorem dens_null_coset {d k : ℕ} (hk : k < d) (μ : EuclideanSpace ℝ (Fin d) → ℝ)
    (c0 : EuclideanSpace ℝ (Fin d)) (g0 : Fin k → EuclideanSpace ℝ (Fin d)) :
    densityMeasure μ {x | x - c0 ∈ Submodule.span ℝ (Set.range g0)} = 0 := by
  have hS : Submodule.span ℝ (Set.range g0) ≠ ⊤ := by
    intro h
    have h1 := finrank_range_le_card (R := ℝ) g0
    unfold Set.finrank at h1
    rw [h, finrank_top, finrank_euclideanSpace_fin, Fintype.card_fin] at h1
    omega
  have hA : AffineSubspace.mk' c0 (Submodule.span ℝ (Set.range g0)) ≠ ⊤ := by
    intro h
    apply hS
    have := congrArg AffineSubspace.direction h
    rwa [AffineSubspace.direction_mk', AffineSubspace.direction_top] at this
  have hset : {x | x - c0 ∈ Submodule.span ℝ (Set.range g0)} =
      (AffineSubspace.mk' c0 (Submodule.span ℝ (Set.range g0)) : Set (EuclideanSpace ℝ (Fin d))) := by
    ext x
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub]
  have h0 : volume ((AffineSubspace.mk' c0 (Submodule.span ℝ (Set.range g0)) :
      Set (EuclideanSpace ℝ (Fin d)))) = 0 :=
    Measure.addHaar_affineSubspace volume _ hA
  rw [hset]
  unfold densityMeasure
  exact withDensity_absolutelyContinuous _ _ h0

theorem one_row_null {d n k : ℕ} (hk : k < d) (μ : Fin (n + 1) → EuclideanSpace ℝ (Fin d) → ℝ)
    (i : Fin (n + 1)) (c : (Fin (n + 1) → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    (g : (Fin (n + 1) → EuclideanSpace ℝ (Fin d)) → Fin k → EuclideanSpace ℝ (Fin d))
    (hc : Continuous c) (hg : Continuous g)
    (hci : ∀ a x, c (Function.update a i x) = c a)
    (hgi : ∀ a x, g (Function.update a i x) = g a) :
    rowLaw μ {a | a i - c a ∈ Submodule.span ℝ (Set.range (g a))} = 0 := by
  have : ∀ j, SigmaFinite (densityMeasure (μ j)) := fun j => by
    unfold densityMeasure; infer_instance
  set B := {a : Fin (n + 1) → EuclideanSpace ℝ (Fin d) |
    a i - c a ∈ Submodule.span ℝ (Set.range (g a))} with hBdef
  have hB : MeasurableSet B := meas_bad c g hc hg i
  have hmp := MeasurePreserving.symm _
    (measurePreserving_piFinSuccAbove (fun j => densityMeasure (μ j)) i)
  unfold rowLaw
  rw [← hmp.measure_preimage_equiv B]
  set e := (MeasurableEquiv.piFinSuccAbove (fun _ => EuclideanSpace ℝ (Fin d)) i).symm with hedef
  have hB' : MeasurableSet (e ⁻¹' B) := e.measurable hB
  rw [Measure.prod_apply_symm hB']
  have hsec : ∀ y, densityMeasure (μ i) ((fun x => (x, y)) ⁻¹' (e ⁻¹' B)) = 0 := by
    intro y
    have hset : (fun x => (x, y)) ⁻¹' (e ⁻¹' B) =
        {x | x - c (e (0, y)) ∈ Submodule.span ℝ (Set.range (g (e (0, y))))} := by
      ext x
      have h1 : e (x, y) = Function.update (e (0, y)) i x := by
        simp only [hedef, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Equiv.coe_fn_mk, Fin.update_insertNth]
      simp only [Set.mem_preimage, hBdef, Set.mem_ofPred_eq]
      rw [h1, hci, hgi, Function.update_self]
    rw [hset]
    exact dens_null_coset hk _ _ _
  simp [hsec]

theorem gen_li {d n p : ℕ} (μ : Fin (n + 1) → EuclideanSpace ℝ (Fin d) → ℝ)
    (w : Fin p → EuclideanSpace ℝ (Fin d)) (hw : LinearIndependent ℝ w)
    (c : (Fin (n + 1) → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d)) (hc : Continuous c) :
    ∀ (m : ℕ) (s : Fin m → Fin (n + 1)), Function.Injective s → p + m ≤ d →
      (∀ k a x, c (Function.update a (s k) x) = c a) →
      ∀ᵐ a ∂rowLaw μ, LinearIndependent ℝ (Fin.append w (fun k => a (s k) - c a)) := by
  intro m
  induction m with
  | zero =>
    intro s _ _ _
    refine Filter.Eventually.of_forall (fun a => ?_)
    have h0 : (fun k : Fin 0 => a (s k) - c a) = Fin.elim0 := funext (fun k => k.elim0)
    rw [h0, Fin.append_elim0]
    exact hw.comp _ (Fin.cast_injective _)
  | succ m ih =>
    intro s hs hpm hcs
    have h1 := ih (s ∘ Fin.castSucc) (hs.comp (Fin.castSucc_injective m)) (by omega)
      (fun k a x => hcs _ a x)
    set i := s (Fin.last m) with hi
    have hne : ∀ k : Fin m, s k.castSucc ≠ i := fun k h =>
      (Fin.castSucc_lt_last k).ne (hs h)
    have hgc : Continuous (fun a : Fin (n + 1) → EuclideanSpace ℝ (Fin d) =>
        Fin.append w (fun k : Fin m => a (s k.castSucc) - c a)) := by
      refine continuous_pi (fun j => ?_)
      induction j using Fin.addCases with
      | left l => simp only [Fin.append_left]; exact continuous_const
      | right l => simp only [Fin.append_right]; exact (continuous_apply _).sub hc
    have h0 := one_row_null (k := p + m) (by omega) μ i c
      (fun a => Fin.append w (fun k : Fin m => a (s k.castSucc) - c a)) hc hgc
      (fun a x => hcs _ a x) (fun a x => by
        beta_reduce
        rw [hcs (Fin.last m) a x]
        congr 1
        funext k
        rw [Function.update_of_ne (hne k)])
    have h2 := measure_eq_zero_iff_ae_notMem.1 h0
    filter_upwards [h1, h2] with a ha1 ha2
    have hsn : (fun k : Fin (m + 1) => a (s k) - c a) =
        Fin.snoc (fun k : Fin m => a (s k.castSucc) - c a) (a i - c a) := by
      funext k
      induction k using Fin.lastCases with
      | last => simp [hi]
      | cast j => simp
    rw [hsn, Fin.append_snoc, linearIndependent_finSnoc]
    exact ⟨ha1, ha2⟩

/-- (G1) a.s.: for every injective `t : Fin (d+1) → Fin (n+1)` the `d` difference vectors are
linearly independent. -/
theorem g1_ae {d n : ℕ} (μ : Fin (n + 1) → EuclideanSpace ℝ (Fin d) → ℝ) :
    ∀ᵐ a ∂rowLaw μ, ∀ t : Fin (d + 1) → Fin (n + 1), Function.Injective t →
      LinearIndependent ℝ (fun k : Fin d => a (t k.succ) - a (t 0)) := by
  rw [ae_all_iff]
  intro t
  by_cases ht : Function.Injective t
  · have h := gen_li μ (Fin.elim0 : Fin 0 → EuclideanSpace ℝ (Fin d))
      (linearIndependent_empty_type) (fun a => a (t 0)) (continuous_apply _) d (t ∘ Fin.succ)
      (ht.comp (Fin.succ_injective _)) (by omega)
      (fun k a x => Function.update_of_ne (fun h => Fin.succ_ne_zero k (ht h).symm) _ _)
    filter_upwards [h] with a ha _
    rw [Fin.elim0_append] at ha
    have := ha.comp (Fin.cast (Nat.zero_add d).symm) (Fin.cast_injective _)
    simpa [Function.comp_def] using this
  · exact Filter.Eventually.of_forall (fun a h => absurd h ht)

/-- (G2) a.s.: a fixed independent pair `w` together with any `d-2` distinct rows is independent. -/
theorem g2_ae {d n : ℕ} (hd : 2 ≤ d) (μ : Fin (n + 1) → EuclideanSpace ℝ (Fin d) → ℝ)
    (w : Fin 2 → EuclideanSpace ℝ (Fin d)) (hw : LinearIndependent ℝ w) :
    ∀ᵐ a ∂rowLaw μ, ∀ t : Fin (d - 2) → Fin (n + 1), Function.Injective t →
      LinearIndependent ℝ (Fin.append w (fun k => a (t k))) := by
  rw [ae_all_iff]
  intro t
  by_cases ht : Function.Injective t
  · have h := gen_li μ w hw (fun _ => 0) continuous_const (d - 2) t ht (by omega)
      (fun _ _ _ => rfl)
    filter_upwards [h] with a ha _
    simpa using ha
  · exact Filter.Eventually.of_forall (fun a h => absurd h ht)

end FSGP


/-! O1b/O1c deterministic part: under general position, every edge of `Q ∩ W` is
`conv(a_I) ∩ W` for a unique `I` with `|I| = d`. -/

namespace FSFace

open MeasureTheory FriendlyShadow.Gaussian
open scoped ENNReal

/-- (G1) deterministic form: any `d+1` rows affinely span, with explicit coefficients. -/
def G1det {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ S : Finset (Fin n), d + 1 ≤ S.card → ∀ z : EuclideanSpace ℝ (Fin d),
    ∃ c : Fin n → ℝ, (∀ i, i ∉ S → c i = 0) ∧ ∑ i, c i = 0 ∧ ∑ i, c i • a i = z

/-- (G2) deterministic form: the hull of at most `d-1` rows meets `W` in at most one point. -/
def G2det {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ J : Finset (Fin n), J.card + 1 ≤ d → ∀ x y : EuclideanSpace ℝ (Fin d), x ∈ W → y ∈ W →
    x ∈ convexHull ℝ (a '' ↑J) → y ∈ convexHull ℝ (a '' ↑J) → x = y

theorem hull_rep {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (J : Finset (Fin n))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ convexHull ℝ (a '' ↑J)) :
    ∃ α : Fin n → ℝ, (∀ i, 0 ≤ α i) ∧ (∀ i, i ∉ J → α i = 0) ∧ ∑ i, α i = 1 ∧
      ∑ i, α i • a i = x := by
  classical
  have hsub : convexHull ℝ (a '' ↑J) ⊆ {y | ∃ α : Fin n → ℝ, (∀ i, 0 ≤ α i) ∧
      (∀ i, i ∉ J → α i = 0) ∧ ∑ i, α i = 1 ∧ ∑ i, α i • a i = y} := by
    apply convexHull_min
    · rintro _ ⟨j, hj, rfl⟩
      refine ⟨Pi.single j 1, fun i => ?_, fun i hi => ?_, by simp, by simp [Pi.single_apply]⟩
      · by_cases h : i = j
        · subst h; simp
        · simp [h]
      · have : i ≠ j := fun h => hi (h ▸ hj)
        simp [this]
    · rintro _ ⟨μ, hμ0, hμJ, hμ1, rfl⟩ _ ⟨ν, hν0, hνJ, hν1, rfl⟩ s t hs ht hst
      refine ⟨fun i => s * μ i + t * ν i, fun i => ?_, fun i hi => ?_, ?_, ?_⟩
      · have := hμ0 i; have := hν0 i; positivity
      · simp [hμJ i hi, hνJ i hi]
      · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hμ1, hν1, hst]
      · simp [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
  exact hsub hx

theorem hull_of_rep {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (J : Finset (Fin n))
    (α : Fin n → ℝ) (h0 : ∀ i, 0 ≤ α i) (hJ : ∀ i, i ∉ J → α i = 0) (h1 : ∑ i, α i = 1) :
    ∑ i, α i • a i ∈ convexHull ℝ (a '' ↑J) := by
  classical
  have e1 : ∑ i ∈ J, α i = ∑ i, α i :=
    Finset.sum_subset (Finset.subset_univ J) (fun i _ hi => hJ i hi)
  have e2 : ∑ i ∈ J, α i • a i = ∑ i, α i • a i :=
    Finset.sum_subset (Finset.subset_univ J) (fun i _ hi => by simp [hJ i hi])
  rw [← e2]
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => h0 i) (e1.trans h1)
    (fun i hi => subset_convexHull ℝ _ ⟨i, hi, rfl⟩)

theorem pert_eps {n : ℕ} (wt c : Fin n → ℝ) (h0 : ∀ i, 0 ≤ wt i)
    (hc : ∀ i, c i ≠ 0 → 0 < wt i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, 0 ≤ wt i + ε * c i := by
  set Q := ∑ i, |c i| / wt i with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun i _ => div_nonneg (abs_nonneg _) (h0 i))
  refine ⟨1 / (1 + Q), by positivity, fun i => ?_⟩
  by_cases hci : c i = 0
  · simp [hci, h0 i]
  · have hw := hc i hci
    have hle : |c i| / wt i ≤ Q :=
      Finset.single_le_sum (f := fun i => |c i| / wt i)
        (fun j _ => div_nonneg (abs_nonneg _) (h0 j)) (Finset.mem_univ i)
    have h2 : |c i| ≤ Q * wt i := (div_le_iff₀ hw).1 hle
    have h3 := neg_abs_le (c i)
    have heq : wt i + 1 / (1 + Q) * c i = (wt i * (1 + Q) + c i) / (1 + Q) := by
      field_simp
    rw [heq]
    apply div_nonneg _ (by positivity)
    nlinarith

theorem pert_mem {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (wt c : Fin n → ℝ) (h0 : ∀ i, 0 ≤ wt i)
    (h1 : ∑ i, wt i = 1) (hc0 : ∑ i, c i = 0) (hc : ∀ i, c i ≠ 0 → 0 < wt i)
    (hmW : ∑ i, wt i • a i ∈ W) (hzW : ∑ i, c i • a i ∈ W) :
    ∃ ε : ℝ, 0 < ε ∧ ∑ i, wt i • a i + ε • ∑ i, c i • a i ∈ polygon W a := by
  obtain ⟨ε, hε, hεi⟩ := pert_eps wt c h0 hc
  refine ⟨ε, hε, ?_⟩
  show _ ∈ convexHull ℝ (Set.range a) ∩ (W : Set (EuclideanSpace ℝ (Fin d)))
  refine ⟨?_, W.add_mem hmW (W.smul_mem _ hzW)⟩
  have heq : ∑ i, wt i • a i + ε • ∑ i, c i • a i = ∑ i, (wt i + ε * c i) • a i := by
    simp [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
  rw [heq]
  refine (convex_convexHull ℝ _).sum_mem (fun i _ => hεi i) ?_
    (fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩)
  simp [Finset.sum_add_distrib, ← Finset.mul_sum, h1, hc0]

theorem mid_mem_W {d n : ℕ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin d))}
    {a : Fin n → EuclideanSpace ℝ (Fin d)} {u v : EuclideanSpace ℝ (Fin d)}
    (huv : Hirsch.Adj (polygon W a) u v) : midpoint ℝ u v ∈ W := by
  have hu : u ∈ polygon W a := huv.2.1 (left_mem_segment ℝ u v)
  have hv : v ∈ polygon W a := huv.2.1 (right_mem_segment ℝ u v)
  rw [midpoint_eq_smul_add]
  exact W.smul_mem _ (W.add_mem hu.2 hv.2)

theorem mid_mem_seg {d' : ℕ} (u v : EuclideanSpace ℝ (Fin d')) : midpoint ℝ u v ∈ segment ℝ u v := by
  rw [segment_eq_image_lineMap]
  exact ⟨1/2, by norm_num, by
    rw [midpoint, AffineMap.lineMap_apply, AffineMap.lineMap_apply]; norm_num [invOf_eq_inv]⟩

/-- Key lemma (K): a positive convex representation of the midpoint of an edge uses at most `d` rows. -/
theorem key_card {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hW : Module.finrank ℝ W = 2) (a : Fin n → EuclideanSpace ℝ (Fin d)) (hG1 : G1det a)
    {u v : EuclideanSpace ℝ (Fin d)} (huv : Hirsch.Adj (polygon W a) u v) (wt : Fin n → ℝ)
    (h0 : ∀ i, 0 ≤ wt i) (h1 : ∑ i, wt i = 1) (hm : ∑ i, wt i • a i = midpoint ℝ u v) :
    (Finset.univ.filter (fun i => 0 < wt i)).card ≤ d := by
  classical
  by_contra hlt
  push_neg at hlt
  have hmW := mid_mem_W huv
  obtain ⟨z, hzW, hz⟩ : ∃ z ∈ W, z ∉ ℝ ∙ (v - u) := by
    by_contra h
    push_neg at h
    have hle : W ≤ ℝ ∙ (v - u) := fun z hz => h z hz
    have h1' := Submodule.finrank_mono hle
    have h2 := finrank_span_le_card (R := ℝ) ({v - u} : Set (EuclideanSpace ℝ (Fin d)))
    simp at h2
    omega
  obtain ⟨c, hcS, hc0, hcz⟩ := hG1 (Finset.univ.filter (fun i => 0 < wt i)) (by omega) z
  have hc : ∀ i, c i ≠ 0 → 0 < wt i := by
    intro i hci
    by_contra hw
    exact hci (hcS i (by simpa using hw))
  have hc' : ∀ i, (-c) i ≠ 0 → 0 < wt i := fun i h => hc i (by simpa using h)
  obtain ⟨ε₁, hε₁, hp₁⟩ := pert_mem W a wt c h0 h1 hc0 hc (hm ▸ hmW) (hcz ▸ hzW)
  obtain ⟨ε₂, hε₂, hp₂⟩ := pert_mem W a wt (-c) h0 h1 (by simp [hc0]) hc' (hm ▸ hmW)
    (by simpa [neg_smul, Finset.sum_neg_distrib, hcz] using W.neg_mem hzW)
  rw [hm, hcz] at hp₁
  have hneg : ∑ i, (-c) i • a i = -z := by simp [neg_smul, Finset.sum_neg_distrib, hcz]
  rw [hm, hneg] at hp₂
  set m := midpoint ℝ u v with hmdef
  have hopen : m ∈ openSegment ℝ (m + ε₂ • -z) (m + ε₁ • z) := by
    have hs : ε₁ + ε₂ ≠ 0 := by positivity
    have hab : ε₁ / (ε₁ + ε₂) + ε₂ / (ε₁ + ε₂) = 1 := by field_simp
    have hab2 : ε₂ / (ε₁ + ε₂) * ε₁ - ε₁ / (ε₁ + ε₂) * ε₂ = 0 := by ring
    refine ⟨ε₁ / (ε₁ + ε₂), ε₂ / (ε₁ + ε₂), by positivity, by positivity, hab, ?_⟩
    calc (ε₁ / (ε₁ + ε₂)) • (m + ε₂ • -z) + (ε₂ / (ε₁ + ε₂)) • (m + ε₁ • z)
        = (ε₁ / (ε₁ + ε₂) + ε₂ / (ε₁ + ε₂)) • m +
          (ε₂ / (ε₁ + ε₂) * ε₁ - ε₁ / (ε₁ + ε₂) * ε₂) • z := by module
      _ = m := by rw [hab, hab2, zero_smul, one_smul, add_zero]
  have hseg := huv.2.right_mem_of_mem_openSegment hp₂ hp₁ (mid_mem_seg u v) hopen
  rw [segment_eq_image'] at hseg
  obtain ⟨θ, _, hθ⟩ := hseg
  apply hz
  have hez : ε₁ • z = (θ - 1 / 2) • (v - u) := by
    have : m = u + (1 / 2 : ℝ) • (v - u) := by
      rw [hmdef, midpoint_eq_smul_add]; simp only [invOf_eq_inv]; module
    rw [this] at hθ
    have := congrArg (fun x => x - (u + (1 / 2 : ℝ) • (v - u))) hθ
    simp only [add_sub_cancel_left] at this
    rw [← this]; module
  have : z = ε₁⁻¹ • ((θ - 1 / 2) • (v - u)) := by
    rw [← hez, smul_smul, inv_mul_cancel₀ hε₁.ne', one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

theorem core_seg {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) {u v : EuclideanSpace ℝ (Fin d)}
    (huv : Hirsch.Adj (polygon W a) u v) (wt : Fin n → ℝ)
    (h0 : ∀ i, 0 ≤ wt i) (h1 : ∑ i, wt i = 1) (hm : ∑ i, wt i • a i = midpoint ℝ u v)
    (y : EuclideanSpace ℝ (Fin d))
    (hy : y ∈ convexHull ℝ (a '' ↑(Finset.univ.filter (fun i => 0 < wt i)))) (hyW : y ∈ W) :
    y ∈ segment ℝ u v := by
  classical
  obtain ⟨γ, hγ0, hγS, hγ1, hγy⟩ := hull_rep a _ y hy
  have hc : ∀ i, (wt - γ) i ≠ 0 → 0 < wt i := by
    intro i hi
    by_contra hw
    have hw0 : wt i = 0 := le_antisymm (not_lt.1 hw) (h0 i)
    have : γ i = 0 := hγS i (by simp [hw])
    exact hi (by simp [hw0, this])
  have hzsum : ∑ i, (wt - γ) i • a i = midpoint ℝ u v - y := by
    simp [sub_smul, Finset.sum_sub_distrib, hm, hγy]
  have hmW := mid_mem_W huv
  obtain ⟨ε, hε, hp⟩ := pert_mem W a wt (wt - γ) h0 h1
    (by simp [Finset.sum_sub_distrib, h1, hγ1]) hc (hm ▸ hmW)
    (hzsum ▸ W.sub_mem hmW hyW)
  rw [hm, hzsum] at hp
  have hyP : y ∈ polygon W a := by
    show y ∈ convexHull ℝ (Set.range a) ∩ (W : Set (EuclideanSpace ℝ (Fin d)))
    exact ⟨convexHull_mono (Set.image_subset_range _ _) hy, hyW⟩
  have hopen : midpoint ℝ u v ∈
      openSegment ℝ (midpoint ℝ u v + ε • (midpoint ℝ u v - y)) y := by
    have hs : 1 + ε ≠ 0 := by positivity
    have hab : 1 / (1 + ε) + ε / (1 + ε) = 1 := by field_simp
    have hab1 : 1 / (1 + ε) * (1 + ε) = 1 := by field_simp
    have hab2 : ε / (1 + ε) - 1 / (1 + ε) * ε = 0 := by ring
    refine ⟨1 / (1 + ε), ε / (1 + ε), by positivity, by positivity, hab, ?_⟩
    calc (1 / (1 + ε)) • (midpoint ℝ u v + ε • (midpoint ℝ u v - y)) + (ε / (1 + ε)) • y
        = (1 / (1 + ε) * (1 + ε)) • midpoint ℝ u v + (ε / (1 + ε) - 1 / (1 + ε) * ε) • y := by
          module
      _ = midpoint ℝ u v := by rw [hab1, hab2, zero_smul, one_smul, add_zero]
  exact huv.2.right_mem_of_mem_openSegment hp hyP (mid_mem_seg u v) hopen

theorem mid_rep {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (u v : EuclideanSpace ℝ (Fin d))
    (α β : Fin n → ℝ) (hαu : ∑ i, α i • a i = u) (hβv : ∑ i, β i • a i = v) :
    ∑ i, ((α i + β i) / 2) • a i = midpoint ℝ u v := by
  have : ∑ i, ((α i + β i) / 2) • a i = (1 / 2 : ℝ) • (∑ i, α i • a i + ∑ i, β i • a i) := by
    rw [← Finset.sum_add_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    module
  rw [this, hαu, hβv, midpoint_eq_smul_add]
  simp only [invOf_eq_inv]
  module

theorem face_exists {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hW : Module.finrank ℝ W = 2) (a : Fin n → EuclideanSpace ℝ (Fin d)) (hG1 : G1det a)
    (hG2 : G2det W a) {u v : EuclideanSpace ℝ (Fin d)} (huv : Hirsch.Adj (polygon W a) u v) :
    ∃ I : Finset (Fin n), I.card = d ∧
      convexHull ℝ (a '' ↑I) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) = segment ℝ u v := by
  classical
  have hu : u ∈ polygon W a := huv.2.1 (left_mem_segment ℝ u v)
  have hv : v ∈ polygon W a := huv.2.1 (right_mem_segment ℝ u v)
  have hrange : convexHull ℝ (Set.range a) = convexHull ℝ (a '' ↑(Finset.univ : Finset (Fin n))) := by
    rw [Finset.coe_univ, Set.image_univ]
  obtain ⟨α, hα0, -, hα1, hαu⟩ := hull_rep a Finset.univ u (hrange ▸ hu.1)
  obtain ⟨β, hβ0, -, hβ1, hβv⟩ := hull_rep a Finset.univ v (hrange ▸ hv.1)
  set wt : Fin n → ℝ := fun i => (α i + β i) / 2 with hwt
  have h0 : ∀ i, 0 ≤ wt i := fun i => by have := hα0 i; have := hβ0 i; positivity
  have h1 : ∑ i, wt i = 1 := by
    simp only [hwt, ← Finset.sum_div, Finset.sum_add_distrib, hα1, hβ1]; norm_num
  have hm : ∑ i, wt i • a i = midpoint ℝ u v := mid_rep a u v α β hαu hβv
  set S := Finset.univ.filter (fun i => 0 < wt i) with hS
  have hcard := key_card W hW a hG1 huv wt h0 h1 hm
  have hαS : ∀ i, i ∉ S → α i = 0 := by
    intro i hi
    have : ¬ 0 < wt i := by simpa [hS] using hi
    have := hα0 i; have := hβ0 i
    simp only [hwt] at *
    linarith [not_lt.1 ‹¬ 0 < (α i + β i) / 2›]
  have hβS : ∀ i, i ∉ S → β i = 0 := by
    intro i hi
    have : ¬ 0 < wt i := by simpa [hS] using hi
    have := hα0 i; have := hβ0 i
    simp only [hwt] at *
    linarith [not_lt.1 ‹¬ 0 < (α i + β i) / 2›]
  have huS : u ∈ convexHull ℝ (a '' ↑S) := hαu ▸ hull_of_rep a S α hα0 hαS hα1
  have hvS : v ∈ convexHull ℝ (a '' ↑S) := hβv ▸ hull_of_rep a S β hβ0 hβS hβ1
  refine ⟨S, le_antisymm hcard ?_, ?_⟩
  · by_contra hlt
    push_neg at hlt
    exact huv.1 (hG2 S (by omega) u v hu.2 hv.2 huS hvS)
  · apply Set.Subset.antisymm
    · rintro y ⟨hy, hyW⟩
      exact core_seg W a huv wt h0 h1 hm y hy hyW
    · exact ((convex_convexHull ℝ _).inter W.convex).segment_subset ⟨huS, hu.2⟩ ⟨hvS, hv.2⟩

theorem supp_cover {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (hG2 : G2det W a) (I : Finset (Fin n))
    (hI : I.card = d) {u v : EuclideanSpace ℝ (Fin d)} (hne : u ≠ v) (huW : u ∈ W) (hvW : v ∈ W)
    (α β : Fin n → ℝ) (hα0 : ∀ i, 0 ≤ α i) (hαI : ∀ i, i ∉ I → α i = 0) (hα1 : ∑ i, α i = 1)
    (hαu : ∑ i, α i • a i = u) (hβ0 : ∀ i, 0 ≤ β i) (hβI : ∀ i, i ∉ I → β i = 0)
    (hβ1 : ∑ i, β i = 1) (hβv : ∑ i, β i • a i = v) :
    ∀ i ∈ I, 0 < α i + β i := by
  classical
  intro i hi
  by_contra hle
  push_neg at hle
  have hαi : α i = 0 := le_antisymm (by linarith [hβ0 i]) (hα0 i)
  have hβi : β i = 0 := le_antisymm (by linarith [hα0 i]) (hβ0 i)
  have hsub : ∀ j, j ∉ I.erase i → j = i ∨ j ∉ I := by
    intro j hj
    by_cases h : j = i
    · exact Or.inl h
    · exact Or.inr (fun hjI => hj (Finset.mem_erase.2 ⟨h, hjI⟩))
  have hu' : u ∈ convexHull ℝ (a '' ↑(I.erase i)) := hαu ▸ hull_of_rep a _ α hα0
    (fun j hj => (hsub j hj).elim (fun h => h ▸ hαi) (hαI j)) hα1
  have hv' : v ∈ convexHull ℝ (a '' ↑(I.erase i)) := hβv ▸ hull_of_rep a _ β hβ0
    (fun j hj => (hsub j hj).elim (fun h => h ▸ hβi) (hβI j)) hβ1
  have hc : (I.erase i).card + 1 ≤ d := by
    rw [Finset.card_erase_of_mem hi]; have := Finset.card_pos.2 ⟨i, hi⟩; omega
  exact hne (hG2 _ hc u v huW hvW hu' hv')

theorem face_unique {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hW : Module.finrank ℝ W = 2) (a : Fin n → EuclideanSpace ℝ (Fin d)) (hG1 : G1det a)
    (hG2 : G2det W a) (I J : Finset (Fin n)) (hI : I.card = d) (hJ : J.card = d)
    {u v : EuclideanSpace ℝ (Fin d)} (huv : Hirsch.Adj (polygon W a) u v)
    (hIe : convexHull ℝ (a '' ↑I) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) = segment ℝ u v)
    (hJe : convexHull ℝ (a '' ↑J) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) = segment ℝ u v) :
    I = J := by
  classical
  have huI : u ∈ convexHull ℝ (a '' ↑I) ∩ (W : Set _) := hIe ▸ left_mem_segment ℝ u v
  have hvI : v ∈ convexHull ℝ (a '' ↑I) ∩ (W : Set _) := hIe ▸ right_mem_segment ℝ u v
  have huJ : u ∈ convexHull ℝ (a '' ↑J) ∩ (W : Set _) := hJe ▸ left_mem_segment ℝ u v
  have hvJ : v ∈ convexHull ℝ (a '' ↑J) ∩ (W : Set _) := hJe ▸ right_mem_segment ℝ u v
  obtain ⟨α, hα0, hαI, hα1, hαu⟩ := hull_rep a I u huI.1
  obtain ⟨β, hβ0, hβI, hβ1, hβv⟩ := hull_rep a I v hvI.1
  obtain ⟨α', hα0', hαJ', hα1', hαu'⟩ := hull_rep a J u huJ.1
  obtain ⟨β', hβ0', hβJ', hβ1', hβv'⟩ := hull_rep a J v hvJ.1
  have hcI := supp_cover W a hG2 I hI huv.1 huI.2 hvI.2 α β hα0 hαI hα1 hαu hβ0 hβI hβ1 hβv
  have hcJ := supp_cover W a hG2 J hJ huv.1 huI.2 hvI.2 α' β' hα0' hαJ' hα1' hαu' hβ0' hβJ'
    hβ1' hβv'
  set wt : Fin n → ℝ := fun i => ((α i + α' i) / 2 + (β i + β' i) / 2) / 2 with hwt
  have h0 : ∀ i, 0 ≤ wt i := fun i => by
    have := hα0 i; have := hβ0 i; have := hα0' i; have := hβ0' i; positivity
  have hu2 : ∑ i, ((α i + α' i) / 2) • a i = u := by
    rw [mid_rep a u u α α' hαu hαu', midpoint_self]
  have hv2 : ∑ i, ((β i + β' i) / 2) • a i = v := by
    rw [mid_rep a v v β β' hβv hβv', midpoint_self]
  have hm : ∑ i, wt i • a i = midpoint ℝ u v := mid_rep a u v _ _ hu2 hv2
  have h1 : ∑ i, wt i = 1 := by
    simp only [hwt, ← Finset.sum_div, Finset.sum_add_distrib, hα1, hβ1, hα1', hβ1']; norm_num
  have hcard := key_card W hW a hG1 huv wt h0 h1 hm
  have hsub : I ∪ J ⊆ Finset.univ.filter (fun i => 0 < wt i) := by
    intro i hi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have := hα0 i; have := hβ0 i; have := hα0' i; have := hβ0' i
    rcases Finset.mem_union.1 hi with h | h
    · have := hcI i h; simp only [hwt]; linarith
    · have := hcJ i h; simp only [hwt]; linarith
  have hU : (I ∪ J).card ≤ d := (Finset.card_le_card hsub).trans hcard
  have h1' : I = I ∪ J := Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
  have h2' : J = I ∪ J := Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
  exact h1'.trans h2'.symm

theorem hA_det {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hW : Module.finrank ℝ W = 2) (a : Fin n → EuclideanSpace ℝ (Fin d)) (hG1 : G1det a)
    (hG2 : G2det W a) :
    (edgeCount (polygon W a) : ℝ≥0∞) ≤
      ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
        {a' | edgeEvent W a' I}.indicator 1 a := by
  classical
  set T := (Finset.univ : Finset (Fin n)).powersetCard d with hT
  have hsum : ∑ I ∈ T, {a' | edgeEvent W a' I}.indicator 1 a =
      ((T.filter (fun I => edgeEvent W a I)).card : ℝ≥0∞) := by
    simp [Set.indicator_apply, Finset.sum_boole]
  rw [hsum]
  have hle : edgeCount (polygon W a) ≤ (T.filter (fun I => edgeEvent W a I)).card := by
    unfold edgeCount
    let f : Set (EuclideanSpace ℝ (Fin d)) → Finset (Fin n) := fun e =>
      if h : ∃ I : Finset (Fin n), I.card = d ∧
          convexHull ℝ (a '' ↑I) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) = e
      then h.choose else ∅
    have hf : ∀ e ∈ edges (polygon W a), (f e).card = d ∧
        convexHull ℝ (a '' ↑(f e)) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) = e := by
      rintro e ⟨u, v, huv, rfl⟩
      have h := face_exists W hW a hG1 hG2 huv
      simp only [f, dif_pos h]
      exact h.choose_spec
    rw [← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard_of_injOn f ?_ ?_ (Finset.finite_toSet _)
    · intro e he
      obtain ⟨hc, heq⟩ := hf e he
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.subset_univ _, hc⟩, ?_⟩
      obtain ⟨u, v, huv, rfl⟩ := he
      exact ⟨u, v, huv, heq⟩
    · intro e₁ he₁ e₂ he₂ h
      rw [← (hf e₁ he₁).2, ← (hf e₂ he₂).2, h]
  exact_mod_cast hle

theorem hB_det {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hW : Module.finrank ℝ W = 2) (a : Fin n → EuclideanSpace ℝ (Fin d)) (hG1 : G1det a)
    (hG2 : G2det W a) :
    ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
      {a' | edgeEvent W a' I}.indicator (fun a' => edgeLen W a' I) a ≤
        perimeter (polygon W a) := by
  classical
  set T := (Finset.univ : Finset (Fin n)).powersetCard d with hT
  have hsum : ∑ I ∈ T, {a' | edgeEvent W a' I}.indicator (fun a' => edgeLen W a' I) a =
      ∑ I ∈ T.filter (fun I => edgeEvent W a I), edgeLen W a I := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun I _ => ?_)
    simp [Set.indicator_apply]
  rw [hsum, ← Finset.tsum_subtype]
  have hmem : ∀ I : (T.filter (fun I => edgeEvent W a I)),
      convexHull ℝ (a '' ↑(I : Finset (Fin n))) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) ∈
        edges (polygon W a) := by
    rintro ⟨I, hI⟩
    obtain ⟨u, v, huv, heq⟩ := (Finset.mem_filter.1 hI).2
    exact ⟨u, v, huv, heq⟩
  let φ : (T.filter (fun I => edgeEvent W a I)) → edges (polygon W a) := fun I => ⟨_, hmem I⟩
  have hφ : Function.Injective φ := by
    rintro ⟨I, hI⟩ ⟨J, hJ⟩ h
    have h' : convexHull ℝ (a '' ↑I) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) =
        convexHull ℝ (a '' ↑J) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) := congrArg Subtype.val h
    obtain ⟨hIT, u, v, huv, heq⟩ := Finset.mem_filter.1 hI
    have hIc := (Finset.mem_powersetCard.1 hIT).2
    have hJc := (Finset.mem_powersetCard.1 (Finset.mem_filter.1 hJ).1).2
    exact Subtype.ext (face_unique W hW a hG1 hG2 I J hIc hJc huv heq (h' ▸ heq))
  unfold perimeter
  exact ENNReal.tsum_comp_le_tsum_of_injective hφ
    (fun e : edges (polygon W a) => Metric.ediam (e : Set (EuclideanSpace ℝ (Fin d))))

theorem bridge1 {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (hLI : ∀ t : Fin (d + 1) → Fin n, Function.Injective t →
      LinearIndependent ℝ (fun k : Fin d => a (t k.succ) - a (t 0))) : G1det a := by
  classical
  intro S hS z
  obtain ⟨S', hS'S, hS'c⟩ := Finset.exists_subset_card_eq hS
  set t : Fin (d + 1) → Fin n := fun k => S'.orderEmbOfFin hS'c k with htdef
  have ht : Function.Injective t := (S'.orderEmbOfFin hS'c).injective
  have hmemt : ∀ k, t k ∈ S := fun k => hS'S (Finset.orderEmbOfFin_mem S' hS'c k)
  have hli := hLI t ht
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp)
  have hz : z ∈ Submodule.span ℝ (Set.range (fun k : Fin d => a (t k.succ) - a (t 0))) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hz
  refine ⟨fun i => (∑ k : Fin d, if t k.succ = i then β k else 0) -
      (if t 0 = i then ∑ k : Fin d, β k else 0),
    ?_, ?_, ?_⟩
  · intro i hi
    have h1 : ∀ k : Fin d, t k.succ ≠ i := fun k h => hi (h ▸ hmemt _)
    have h2 : t 0 ≠ i := fun h => hi (h ▸ hmemt _)
    simp [h1, h2]
  · rw [Finset.sum_sub_distrib, Finset.sum_comm]
    simp [Finset.sum_ite_eq]
  · rw [← hβ]
    simp only [sub_smul, Finset.sum_sub_distrib, Finset.sum_smul, ite_smul, zero_smul]
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq, smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]

theorem bridge2 {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n) (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hW : Module.finrank ℝ W = 2) (a : Fin n → EuclideanSpace ℝ (Fin d))
    (w : Fin 2 → EuclideanSpace ℝ (Fin d)) (hwW : ∀ i, w i ∈ W)
    (hLI : ∀ t : Fin (d - 2) → Fin n, Function.Injective t →
      LinearIndependent ℝ (Fin.append w (fun k => a (t k)))) : G2det W a := by
  classical
  intro J hJ x y hxW hyW hx hy
  by_contra hxy
  obtain ⟨Jp, hJJ, -, hJc⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ J)
    (show J.card ≤ d - 1 by omega) (show d - 1 ≤ (Finset.univ : Finset (Fin n)).card by simp; omega)
  obtain ⟨j0, hj0⟩ : Jp.Nonempty := Finset.card_pos.1 (by omega)
  set J' := Jp.erase j0 with hJ'
  have hJ'c : J'.card = d - 2 := by rw [Finset.card_erase_of_mem hj0, hJc]; omega
  set t : Fin (d - 2) → Fin n := fun k => J'.orderEmbOfFin hJ'c k with htdef
  have ht : Function.Injective t := (J'.orderEmbOfFin hJ'c).injective
  have hspan := (hLI t ht).span_eq_top_of_card_eq_finrank' (by simp; omega)
  have hsubJ : convexHull ℝ (a '' ↑J) ⊆ convexHull ℝ (a '' ↑Jp) :=
    convexHull_mono (Set.image_mono (Finset.coe_subset.2 hJJ))
  obtain ⟨α, hα0, hαJ, hα1, hαx⟩ := hull_rep a Jp x (hsubJ hx)
  obtain ⟨β, hβ0, hβJ, hβ1, hβy⟩ := hull_rep a Jp y (hsubJ hy)
  set D := Submodule.span ℝ (↑(J'.image (fun i => a i - a j0)) : Set (EuclideanSpace ℝ (Fin d)))
    with hD
  have hDfin : Module.finrank ℝ D ≤ d - 2 := by
    have h := finrank_span_finset_le_card (R := ℝ) (J'.image (fun i => a i - a j0))
    unfold Set.finrank at h
    exact h.trans (Finset.card_image_le.trans hJ'c.le)
  have hdec : ∀ γ : Fin n → ℝ, (∀ i, i ∉ Jp → γ i = 0) →
      ∑ i, γ i • (a i - a j0) ∈ D := by
    intro γ hγ
    refine Submodule.sum_mem _ (fun i _ => ?_)
    by_cases hi : i ∈ J'
    · exact Submodule.smul_mem _ _ (Submodule.subset_span
        (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hi)))
    · by_cases hi0 : i = j0
      · rw [hi0, sub_self, smul_zero]; exact Submodule.zero_mem _
      · have : i ∉ Jp := fun h => hi (Finset.mem_erase.2 ⟨hi0, h⟩)
        rw [hγ i this, zero_smul]; exact Submodule.zero_mem _
  have hsplit : ∀ γ : Fin n → ℝ,
      ∑ i, γ i • a i = ∑ i, γ i • (a i - a j0) + (∑ i, γ i) • a j0 := by
    intro γ
    simp [smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]
  have hj0D : a j0 ∈ D ⊔ W := by
    have h := hsplit α
    rw [hαx, hα1, one_smul] at h
    have : a j0 = -(∑ i, α i • (a i - a j0)) + x := by rw [h]; abel
    rw [this]
    exact Submodule.add_mem_sup (D.neg_mem (hdec α hαJ)) hxW
  have htop : D ⊔ W = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    induction j using Fin.addCases with
    | left l =>
      rw [Fin.append_left]; exact Submodule.mem_sup_right (hwW l)
    | right k =>
      rw [Fin.append_right]
      have hk : t k ∈ J' := Finset.orderEmbOfFin_mem J' hJ'c k
      have : a (t k) = (a (t k) - a j0) + a j0 := by abel
      rw [SetLike.mem_coe, this]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.subset_span
        (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hk)))) hj0D
  have hgr := Submodule.finrank_sup_add_finrank_inf_eq D W
  rw [htop, finrank_top, finrank_euclideanSpace_fin, hW] at hgr
  have h0 : Module.finrank ℝ ↥(D ⊓ W) = 0 := by omega
  rw [Submodule.finrank_eq_zero] at h0
  have hyx : y - x ∈ D ⊓ W := by
    refine ⟨?_, W.sub_mem hyW hxW⟩
    have h := hsplit (fun i => β i - α i)
    have hs0 : ∑ i, (β i - α i) = 0 := by rw [Finset.sum_sub_distrib, hβ1, hα1, sub_self]
    rw [hs0, zero_smul, add_zero] at h
    have hyx' : ∑ i, (β i - α i) • a i = y - x := by
      simp [sub_smul, Finset.sum_sub_distrib, hβy, hαx]
    rw [← hyx', h]
    exact hdec _ (fun i hi => by rw [hβJ i hi, hαJ i hi, sub_self])
  rw [h0] at hyx
  exact hxy (sub_eq_zero.1 ((Submodule.mem_bot ℝ).1 hyx)).symm

end FSFace


open MeasureTheory
open scoped RealInnerProductSpace ENNReal


namespace C5747Meas

lemma mem_hull_range_iff' {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} [Fintype ι]
    (p : ι → E) (y : E) :
    y ∈ convexHull ℝ (Set.range p) ↔
      ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ ∑ i, μ i = 1 ∧ ∑ i, μ i • p i = y := by
  classical
  constructor
  · intro hy
    have hsub : convexHull ℝ (Set.range p) ⊆
        {y | ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ ∑ i, μ i = 1 ∧ ∑ i, μ i • p i = y} := by
      apply convexHull_min
      · rintro _ ⟨j, rfl⟩
        refine ⟨Pi.single j 1, ?_, ?_, ?_⟩
        · intro i
          by_cases h : i = j
          · subst h; simp
          · simp [h]
        · simp
        · simp [Pi.single_apply]
      · rintro _ ⟨μ, hμ0, hμ1, rfl⟩ _ ⟨ν, hν0, hν1, rfl⟩ s t hs ht hst
        refine ⟨fun i => s * μ i + t * ν i, fun i => ?_, ?_, ?_⟩
        · have := hμ0 i; have := hν0 i; positivity
        · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hμ1, hν1, hst]
        · simp [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
    exact hsub hy
  · rintro ⟨μ, h0, h1, rfl⟩
    exact mem_convexHull_of_exists_fintype μ p h0 h1 (fun i => Set.mem_range_self i) rfl

/-- The graph of a continuously varying finite convex hull is closed. -/
lemma isClosed_hull {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : X → ι → E) (hF : Continuous F) :
    IsClosed {p : X × E | p.2 ∈ convexHull ℝ (Set.range (F p.1))} := by
  have : CompactSpace (stdSimplex ℝ ι) := isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ ι)
  have hcont : Continuous (fun q : (X × E) × stdSimplex ℝ ι => ∑ i, (q.2 : ι → ℝ) i • F q.1.1 i) :=
    continuous_finsetSum _ (fun i _ =>
      ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)).smul
        ((continuous_apply i).comp (hF.comp (continuous_fst.comp continuous_fst))))
  have hC : IsClosed {q : (X × E) × stdSimplex ℝ ι | ∑ i, (q.2 : ι → ℝ) i • F q.1.1 i = q.1.2} :=
    isClosed_eq hcont (continuous_snd.comp continuous_fst)
  have h := isClosedMap_fst_of_compactSpace _ hC
  convert h using 1
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_image, mem_hull_range_iff']
  constructor
  · rintro ⟨μ, h0, h1, h⟩; exact ⟨(p, ⟨μ, h0, h1⟩), h, rfl⟩
  · rintro ⟨⟨p', μ⟩, h, rfl⟩; exact ⟨μ, μ.2.1, μ.2.2, h⟩

lemma range_pair {E : Type*} (u v : E) : Set.range ![u, v] = {u, v} := by
  ext x
  simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h) <;> simp [← h]
  · rintro (h | h) <;> simp [h]

lemma isClosed_seg {X : Type*} [TopologicalSpace X] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f g : X → E) (hf : Continuous f) (hg : Continuous g) :
    IsClosed {p : X × E | p.2 ∈ segment ℝ (f p.1) (g p.1)} := by
  have h := isClosed_hull (fun x => ![f x, g x]) (by fun_prop)
  convert h using 1
  ext p; simp only [Set.mem_setOf_eq, range_pair, convexHull_pair]

/-- Images of `closed ∩ open` subsets of a σ-compact metric space are measurable. -/
lemma meas_image {Z P : Type*} [MetricSpace Z] [SigmaCompactSpace Z] [TopologicalSpace P]
    [T2Space P] [MeasurableSpace P] [OpensMeasurableSpace P] (f : Z → P) (hf : Continuous f)
    {C U : Set Z} (hC : IsClosed C) (hU : IsOpen U) : MeasurableSet (f '' (C ∩ U)) := by
  obtain ⟨F, hFc, -, hFU, -⟩ := hU.exists_iUnion_isClosed
  have hs : IsSigmaCompact (C ∩ U) := by
    rw [← hFU, Set.inter_iUnion]
    exact isSigmaCompact_iUnion _ (fun k =>
      IsSigmaCompact.of_isClosed_subset isSigmaCompact_univ (hC.inter (hFc k)) (Set.subset_univ _))
  obtain ⟨K, hK, hKU⟩ := hs.image hf
  rw [← hKU]
  exact MeasurableSet.iUnion (fun k => (hK k).isClosed.measurableSet)

/-- A `∀`-clause over a σ-compact fibre with closed hypothesis and closed conclusion is measurable. -/
lemma meas_forall {B Y : Type*} [MetricSpace B] [MetricSpace Y] [SigmaCompactSpace (B × Y)]
    [MeasurableSpace B] [OpensMeasurableSpace B] (C D : Set (B × Y)) (hC : IsClosed C)
    (hD : IsClosed D) : MeasurableSet {b | ∀ y, (b, y) ∈ C → (b, y) ∈ D} := by
  have h := meas_image Prod.fst continuous_fst hC hD.isOpen_compl
  convert h.compl using 1
  ext b
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, Set.mem_inter_iff, Prod.exists,
    exists_and_right, exists_eq_right, not_exists, not_and, not_not]

open FriendlyShadow.Gaussian

variable {d n : ℕ}

/-- `V_S(a) = conv(a_i : i ∈ S) ∩ W`. -/
def VS (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (S : Finset (Fin n))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin d)) :=
  convexHull ℝ (Set.range (fun i : S => a i)) ∩ (W : Set (EuclideanSpace ℝ (Fin d)))

/-- `S` pins the segment `[u, v]`: `V_S(a) ⊆ [u, v]` and the midpoint lies in `V_S(a)`. -/
def RS (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (S : Finset (Fin n))
    (b : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
    Prop :=
  VS W S b.1 ⊆ segment ℝ b.2.1 b.2.2 ∧ midpoint ℝ b.2.1 b.2.2 ∈ VS W S b.1

lemma isClosed_VS {X : Type*} [TopologicalSpace X] (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (S : Finset (Fin n)) (F : X → Fin n → EuclideanSpace ℝ (Fin d)) (hF : Continuous F)
    (g : X → EuclideanSpace ℝ (Fin d)) (hg : Continuous g) :
    IsClosed {x | g x ∈ VS W S (F x)} := by
  have h1 := (isClosed_hull (fun a : Fin n → EuclideanSpace ℝ (Fin d) => fun i : S => a i)
    (continuous_pi (fun i => continuous_apply _))).preimage (hF.prodMk hg)
  have h2 := (Submodule.closed_of_finiteDimensional W).preimage hg
  exact h1.inter h2

lemma isClosed_K {X : Type*} [TopologicalSpace X] (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (F : X → Fin n → EuclideanSpace ℝ (Fin d)) (hF : Continuous F)
    (g : X → EuclideanSpace ℝ (Fin d)) (hg : Continuous g) :
    IsClosed {x | g x ∈ polygon W (F x)} := by
  have h1 := (isClosed_hull (fun a : Fin n → EuclideanSpace ℝ (Fin d) => a) continuous_id).preimage
    (hF.prodMk hg)
  have h2 := (Submodule.closed_of_finiteDimensional W).preimage hg
  exact h1.inter h2

lemma isClosed_segm {X : Type*} [TopologicalSpace X] (f g h : X → EuclideanSpace ℝ (Fin d))
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    IsClosed {x | h x ∈ segment ℝ (f x) (g x)} :=
  (isClosed_seg f g hf hg).preimage (continuous_id.prodMk hh)

lemma mid_eq (u v : EuclideanSpace ℝ (Fin d)) : midpoint ℝ u v = (2 : ℝ)⁻¹ • (u + v) := by
  rw [midpoint_eq_smul_add, invOf_eq_inv]

lemma meas_RS (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (S : Finset (Fin n)) :
    MeasurableSet {b : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d) | RS W S b} := by
  have h1 := meas_forall (B := (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) (Y := EuclideanSpace ℝ (Fin d))
    {p | p.2 ∈ VS W S p.1.1} {p | p.2 ∈ segment ℝ p.1.2.1 p.1.2.2}
    (isClosed_VS W S _ (by fun_prop) _ (by fun_prop)) (isClosed_segm _ _ _ (by fun_prop) (by fun_prop) (by fun_prop))
  have h2 : IsClosed {b : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d) | midpoint ℝ b.2.1 b.2.2 ∈ VS W S b.1} := by
    simp only [mid_eq]
    exact isClosed_VS W S _ (by fun_prop) _ (by fun_prop)
  convert h1.inter h2.measurableSet using 1
  ext b
  simp only [RS, Set.mem_setOf_eq, Set.mem_inter_iff]
  rfl

lemma extreme_clause_iff (K B : Set (EuclideanSpace ℝ (Fin d))) :
    (∀ ⦃x⦄, x ∈ K → ∀ ⦃y⦄, y ∈ K → ∀ ⦃z⦄, z ∈ B → z ∈ openSegment ℝ x y → x ∈ B) ↔
      ∀ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × ℝ,
        (p.1 ∈ K ∧ p.2.1 ∈ K ∧ (1 - p.2.2) • p.1 + p.2.2 • p.2.1 ∈ B) →
          (p.2.2 ≤ 0 ∨ 1 ≤ p.2.2 ∨ p.1 ∈ B) := by
  constructor
  · rintro H ⟨x, y, t⟩ ⟨hx, hy, hz⟩
    by_contra hc
    simp only [not_or, not_le] at hc
    obtain ⟨h0, h1, hxB⟩ := hc
    exact hxB (H hx hy hz (by rw [openSegment_eq_image]; exact ⟨t, ⟨h0, h1⟩, rfl⟩))
  · intro H x hx y hy z hz hzs
    rw [openSegment_eq_image] at hzs
    obtain ⟨t, ⟨h0, h1⟩, rfl⟩ := hzs
    rcases H (x, y, t) ⟨hx, hy, hz⟩ with h | h | h
    · exact absurd h (not_le.mpr h0)
    · exact absurd h (not_le.mpr h1)
    · exact h

set_option maxHeartbeats 1000000 in
lemma meas_Adj (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    MeasurableSet {b : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d) | Hirsch.Adj (polygon W b.1) b.2.1 b.2.2} := by
  have h0 : MeasurableSet {b : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d) | b.2.1 ≠ b.2.2} :=
    (isClosed_eq (by fun_prop) (by fun_prop)).measurableSet.compl
  have h1 := meas_forall (B := (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) (Y := EuclideanSpace ℝ (Fin d))
    {p | p.2 ∈ segment ℝ p.1.2.1 p.1.2.2} {p | p.2 ∈ polygon W p.1.1}
    (isClosed_segm _ _ _ (by fun_prop) (by fun_prop) (by fun_prop))
    (isClosed_K W _ (by fun_prop) _ (by fun_prop))
  have hC : IsClosed {p : ((Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × ℝ) |
      p.2.1 ∈ polygon W p.1.1 ∧ p.2.2.1 ∈ polygon W p.1.1 ∧
      (1 - p.2.2.2) • p.2.1 + p.2.2.2 • p.2.2.1 ∈ segment ℝ p.1.2.1 p.1.2.2} :=
    (isClosed_K W _ (by fun_prop) _ (by fun_prop)).inter
      ((isClosed_K W _ (by fun_prop) _ (by fun_prop)).inter
        (isClosed_segm _ _ _ (by fun_prop) (by fun_prop) (by fun_prop)))
  have hD : IsClosed {p : ((Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × ℝ) |
      p.2.2.2 ≤ 0 ∨ 1 ≤ p.2.2.2 ∨ p.2.1 ∈ segment ℝ p.1.2.1 p.1.2.2} := by
    simp only [Set.setOf_or]
    exact (isClosed_le (by fun_prop) continuous_const).union ((isClosed_le continuous_const (by fun_prop)).union
      (isClosed_segm _ _ _ (by fun_prop) (by fun_prop) (by fun_prop)))
  have h2 := meas_forall _ _ hC hD
  convert h0.inter (h1.inter h2) using 1
  ext b
  simp only [Hirsch.Adj, isExtreme_iff, Set.mem_setOf_eq, Set.mem_inter_iff, extreme_clause_iff]
  rfl

end C5747Meas

namespace C5747Cnt

open FriendlyShadow.Gaussian C5747Meas

variable {d n : ℕ}

lemma seg_param {u v x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ segment ℝ u v) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ x = u + s • (v - u) := by
  rw [segment_eq_image'] at hx
  obtain ⟨s, ⟨h0, h1⟩, rfl⟩ := hx
  exact ⟨s, h0, h1, rfl⟩

lemma seg_ends {u v u' v' : EuclideanSpace ℝ (Fin d)} (hne : u ≠ v)
    (h : segment ℝ u v = segment ℝ u' v') : (u' = u ∧ v' = v) ∨ (u' = v ∧ v' = u) := by
  have hu' : u' ∈ segment ℝ u v := by rw [h]; exact left_mem_segment ℝ u' v'
  have hv' : v' ∈ segment ℝ u v := by rw [h]; exact right_mem_segment ℝ u' v'
  have hu : u ∈ segment ℝ u' v' := by rw [← h]; exact left_mem_segment ℝ u v
  have hv : v ∈ segment ℝ u' v' := by rw [← h]; exact right_mem_segment ℝ u v
  obtain ⟨s, hs0, hs1, hs⟩ := seg_param hu'
  obtain ⟨t, ht0, ht1, ht⟩ := seg_param hv'
  obtain ⟨p, hp0, hp1, hp⟩ := seg_param hu
  obtain ⟨q, hq0, hq1, hq⟩ := seg_param hv
  have e1 : v' - u' = (t - s) • (v - u) := by rw [ht, hs]; module
  have e2 : v - u = (q - p) • (v' - u') := by
    calc v - u = (u' + q • (v' - u')) - (u' + p • (v' - u')) := by rw [← hq, ← hp]
      _ = (q - p) • (v' - u') := by module
  have e3 : (1 - (q - p) * (t - s)) • (v - u) = 0 := by
    rw [sub_smul, one_smul, mul_smul, ← e1, ← e2, sub_self]
  have hvu : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have e4 : (q - p) * (t - s) = 1 := by
    have := (smul_eq_zero.mp e3).resolve_right hvu; linarith
  have h1 : (t - s) ^ 2 ≤ 1 := by nlinarith
  have h2 : (q - p) ^ 2 ≤ 1 := by nlinarith
  have h3 : (t - s) ^ 2 * (q - p) ^ 2 = 1 := by rw [← mul_pow, mul_comm, e4]; norm_num
  have h4 : 1 ≤ (t - s) ^ 2 := by nlinarith
  have h5 : (t - s - 1) * (t - s + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp h5 with h6 | h6
  · have hs' : s = 0 := by linarith
    have ht' : t = 1 := by linarith
    left; constructor
    · rw [hs, hs']; simp
    · rw [ht, ht']; simp
  · have hs' : s = 1 := by linarith
    have ht' : t = 0 := by linarith
    right; constructor
    · rw [hs, hs']; simp
    · rw [ht, ht']; simp

/-- Lexicographic order on coordinates, used to orient each edge. -/
def lexLt (u v : EuclideanSpace ℝ (Fin d)) : Prop :=
  toLex (WithLp.ofLp u) < toLex (WithLp.ofLp v)

lemma lex_total {u v : EuclideanSpace ℝ (Fin d)} (h : u ≠ v) : lexLt u v ∨ lexLt v u := by
  unfold lexLt
  rcases lt_trichotomy (toLex (WithLp.ofLp u)) (toLex (WithLp.ofLp v)) with h1 | h1 | h1
  · exact Or.inl h1
  · exfalso
    have h2 : WithLp.ofLp u = WithLp.ofLp v := toLex.injective h1
    have := congrArg (WithLp.toLp 2) h2
    exact h (by simpa using this)
  · exact Or.inr h1

lemma lex_asymm {u v : EuclideanSpace ℝ (Fin d)} (h : lexLt u v) : ¬ lexLt v u :=
  lt_asymm h

lemma meas_lex : MeasurableSet {b : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
    EuclideanSpace ℝ (Fin d) | lexLt b.2.1 b.2.2} := by
  have : {b : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d) | lexLt b.2.1 b.2.2} =
      ⋃ i : Fin d, ({b | ∀ j, j < i → (WithLp.ofLp b.2.1) j = (WithLp.ofLp b.2.2) j} ∩
        {b | (WithLp.ofLp b.2.1) i < (WithLp.ofLp b.2.2) i}) := by
    ext b
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    rfl
  rw [this]
  refine MeasurableSet.iUnion fun i => MeasurableSet.inter ?_ ?_
  · refine IsClosed.measurableSet ?_
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (by fun_prop) (by fun_prop)
  · exact (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet


lemma adj_swap {K : Set (EuclideanSpace ℝ (Fin d))} {u v : EuclideanSpace ℝ (Fin d)}
    (h : Hirsch.Adj K u v) : Hirsch.Adj K v u :=
  ⟨h.1.symm, by rw [segment_symm]; exact h.2⟩

end C5747Cnt

/-! O1a: measurability of the edge events `E_I` (Lusin–Souslin on oriented witnesses). -/
namespace FSMeasE

open FriendlyShadow.Gaussian C5747Meas C5747Cnt

variable {d n : ℕ}

/-- Oriented witnesses `(a, u, v)` of the event `E_I`. -/
def ES (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (I : Finset (Fin n)) :
    Set ((Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  {b | Hirsch.Adj (polygon W b.1) b.2.1 b.2.2 ∧
    (∀ x, x ∈ VS W I b.1 → x ∈ segment ℝ b.2.1 b.2.2) ∧
    (∀ x, x ∈ segment ℝ b.2.1 b.2.2 → x ∈ VS W I b.1) ∧ lexLt b.2.1 b.2.2}

lemma meas_ES (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (I : Finset (Fin n)) :
    MeasurableSet (ES W I) := by
  have h1 := meas_forall (B := (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d)) (Y := EuclideanSpace ℝ (Fin d))
    {p | p.2 ∈ VS W I p.1.1} {p | p.2 ∈ segment ℝ p.1.2.1 p.1.2.2}
    (isClosed_VS W I _ (by fun_prop) _ (by fun_prop))
    (isClosed_segm _ _ _ (by fun_prop) (by fun_prop) (by fun_prop))
  have h2 := meas_forall (B := (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d)) (Y := EuclideanSpace ℝ (Fin d))
    {p | p.2 ∈ segment ℝ p.1.2.1 p.1.2.2} {p | p.2 ∈ VS W I p.1.1}
    (isClosed_segm _ _ _ (by fun_prop) (by fun_prop) (by fun_prop))
    (isClosed_VS W I _ (by fun_prop) _ (by fun_prop))
  exact (meas_Adj W).inter (h1.inter (h2.inter meas_lex))

lemma injOn_ES (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (I : Finset (Fin n)) :
    Set.InjOn Prod.fst (ES W I) := by
  rintro ⟨a, u, v⟩ ⟨hA, h1, h2, hL⟩ ⟨a', u', v'⟩ ⟨hA', h1', h2', hL'⟩ hfst
  simp only at hfst
  subst hfst
  have hseg : segment ℝ u v = segment ℝ u' v' :=
    Set.Subset.antisymm (fun x hx => h1' x (h2 x hx)) (fun x hx => h1 x (h2' x hx))
  rcases seg_ends hA.1 hseg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact absurd hL' (lex_asymm hL)

theorem meas_edgeEvent (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (I : Finset (Fin n)) :
    MeasurableSet {a : Fin n → EuclideanSpace ℝ (Fin d) | edgeEvent W a I} := by
  have hV : ∀ a : Fin n → EuclideanSpace ℝ (Fin d),
      convexHull ℝ (a '' (I : Set (Fin n))) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) = VS W I a := by
    intro a
    unfold VS
    rw [Set.image_eq_range]
    try rfl
  have hset : {a : Fin n → EuclideanSpace ℝ (Fin d) | edgeEvent W a I} = Prod.fst '' ES W I := by
    ext a
    constructor
    · rintro ⟨u, v, hA, he⟩
      rw [hV] at he
      rcases lex_total hA.1 with hl | hl
      · refine ⟨(a, u, v), ⟨hA, fun x hx => ?_, fun x hx => ?_, hl⟩, rfl⟩
        · rw [← he]; exact hx
        · rw [he]; exact hx
      · refine ⟨(a, v, u), ⟨adj_swap hA, fun x hx => ?_, fun x hx => ?_, hl⟩, rfl⟩
        · rw [segment_symm, ← he]; exact hx
        · rw [he, segment_symm]; exact hx
    · rintro ⟨⟨a', u, v⟩, ⟨hA, h1, h2, -⟩, rfl⟩
      refine ⟨u, v, hA, ?_⟩
      rw [hV]
      exact Set.Subset.antisymm (fun x hx => h1 x hx) (fun x hx => h2 x hx)
  rw [hset]
  exact (meas_ES W I).image_of_continuousOn_injOn continuous_fst.continuousOn (injOn_ES W I)

end FSMeasE


/-! O1 reduction: lemma_25's inequality from two almost-sure statements
(A) edgeCount ≤ Σ_{|I|=d} 1[E_I] and (B) Σ_{|I|=d} 1[E_I]·edgeLen_I ≤ perimeter,
plus measurability of the events `E_I`. -/

namespace FSL25

open MeasureTheory FriendlyShadow.Gaussian
open scoped ENNReal

theorem sum_le_lintegral_sum {α ι : Type*} [MeasurableSpace α] (μ : Measure α) (s : Finset ι)
    (f : ι → α → ℝ≥0∞) : ∑ i ∈ s, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ∑ i ∈ s, f i a ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj]
    calc ∫⁻ a, f j a ∂μ + ∑ i ∈ s, ∫⁻ a, f i a ∂μ
        ≤ ∫⁻ a, f j a ∂μ + ∫⁻ a, ∑ i ∈ s, f i a ∂μ := by gcongr
      _ ≤ ∫⁻ a, (f j a + ∑ i ∈ s, f i a) ∂μ := le_lintegral_add _ _
      _ = ∫⁻ a, ∑ i ∈ insert j s, f i a ∂μ := by simp_rw [Finset.sum_insert hj]

theorem lemma25_of_ae {d n : ℕ} (hdn : d ≤ n) (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (P : Measure (Fin n → EuclideanSpace ℝ (Fin d))) (m : ℝ≥0∞)
    (hmeas : ∀ I : Finset (Fin n), MeasurableSet {a | edgeEvent W a I})
    (hA : ∀ᵐ a ∂P, (edgeCount (polygon W a) : ℝ≥0∞) ≤
      ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard d, {a | edgeEvent W a I}.indicator 1 a)
    (hB : ∀ᵐ a ∂P, ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
      {a | edgeEvent W a I}.indicator (fun a => edgeLen W a I) a ≤ perimeter (polygon W a))
    (hm : ∀ I : Finset (Fin n), I.card = d →
      ENNReal.ofReal (2 / (n.choose d : ℝ)) ≤ P {a | edgeEvent W a I} →
      m * P {a | edgeEvent W a I} ≤ ∫⁻ a in {a | edgeEvent W a I}, edgeLen W a I ∂P) :
    m * ∫⁻ a, (edgeCount (polygon W a) : ℝ≥0∞) ∂P ≤
      2 * m + ∫⁻ a, perimeter (polygon W a) ∂P := by
  set T := (Finset.univ : Finset (Fin n)).powersetCard d with hT
  have hC : (0 : ℝ) < (n.choose d : ℝ) := by exact_mod_cast Nat.choose_pos hdn
  calc m * ∫⁻ a, (edgeCount (polygon W a) : ℝ≥0∞) ∂P
      ≤ m * ∫⁻ a, ∑ I ∈ T, {a | edgeEvent W a I}.indicator 1 a ∂P :=
        mul_le_mul' le_rfl (lintegral_mono_ae hA)
    _ = ∑ I ∈ T, m * P {a | edgeEvent W a I} := by
        rw [lintegral_finsetSum _ (fun I _ => measurable_one.indicator (hmeas I)), Finset.mul_sum]
        refine Finset.sum_congr rfl (fun I _ => ?_)
        rw [lintegral_indicator_one (hmeas I)]
    _ ≤ ∑ I ∈ T, (m * ENNReal.ofReal (2 / (n.choose d : ℝ)) +
          ∫⁻ a in {a | edgeEvent W a I}, edgeLen W a I ∂P) := by
        refine Finset.sum_le_sum (fun I hI => ?_)
        by_cases h : ENNReal.ofReal (2 / (n.choose d : ℝ)) ≤ P {a | edgeEvent W a I}
        · exact le_add_left (hm I (Finset.mem_powersetCard.1 hI).2 h)
        · rw [not_le] at h
          exact le_add_right (mul_le_mul' le_rfl h.le)
    _ = (n.choose d : ℝ≥0∞) * (m * ENNReal.ofReal (2 / (n.choose d : ℝ))) +
          ∑ I ∈ T, ∫⁻ a in {a | edgeEvent W a I}, edgeLen W a I ∂P := by
        rw [Finset.sum_add_distrib, Finset.sum_const, hT, Finset.card_powersetCard,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ 2 * m + ∫⁻ a, perimeter (polygon W a) ∂P := by
        refine add_le_add (le_of_eq ?_) ?_
        · rw [mul_comm m, ← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hC.le,
            mul_div_cancel₀ _ hC.ne', ENNReal.ofReal_ofNat]
        · calc ∑ I ∈ T, ∫⁻ a in {a | edgeEvent W a I}, edgeLen W a I ∂P
              = ∑ I ∈ T, ∫⁻ a, {a | edgeEvent W a I}.indicator (fun a => edgeLen W a I) a ∂P := by
                refine Finset.sum_congr rfl (fun I _ => ?_)
                rw [lintegral_indicator (hmeas I)]
            _ ≤ ∫⁻ a, ∑ I ∈ T, {a | edgeEvent W a I}.indicator (fun a => edgeLen W a I) a ∂P :=
                sum_le_lintegral_sum P T _
            _ ≤ ∫⁻ a, perimeter (polygon W a) ∂P := lintegral_mono_ae hB

end FSL25


/-! O1 CLOSED: lemma_25's inequality (after GP, Face, Meas, L25). -/

namespace FSO1

open MeasureTheory FriendlyShadow.Gaussian
open scoped ENNReal

theorem gp_ae {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n + 1)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hW : Module.finrank ℝ W = 2)
    (μ : Fin (n + 1) → EuclideanSpace ℝ (Fin d) → ℝ) :
    ∀ᵐ a ∂rowLaw μ, FSFace.G1det a ∧ FSFace.G2det W a := by
  let b := Module.finBasisOfFinrankEq ℝ W hW
  have hwLI : LinearIndependent ℝ (fun i : Fin 2 => (b i : EuclideanSpace ℝ (Fin d))) :=
    b.linearIndependent.map' W.subtype W.ker_subtype
  filter_upwards [FSGP.g1_ae μ, FSGP.g2_ae (by omega) μ _ hwLI] with a h1 h2
  exact ⟨FSFace.bridge1 a h1, FSFace.bridge2 hd hdn W hW a _ (fun i => (b i).2) h2⟩

theorem lemma25_full {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hW : Module.finrank ℝ W = 2)
    (μ : Fin n → EuclideanSpace ℝ (Fin d) → ℝ) (m : ℝ≥0∞)
    (hm : ∀ I : Finset (Fin n), I.card = d →
      ENNReal.ofReal (2 / (n.choose d : ℝ)) ≤ rowLaw μ {a | edgeEvent W a I} →
      m * rowLaw μ {a | edgeEvent W a I} ≤
        ∫⁻ a in {a | edgeEvent W a I}, edgeLen W a I ∂(rowLaw μ)) :
    m * ∫⁻ a, (edgeCount (polygon W a) : ℝ≥0∞) ∂(rowLaw μ) ≤
      2 * m + ∫⁻ a, perimeter (polygon W a) ∂(rowLaw μ) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hgp := gp_ae hd hdn W hW μ
  exact FSL25.lemma25_of_ae hdn W (rowLaw μ) m (fun I => FSMeasE.meas_edgeEvent W I)
    (hgp.mono fun a ha => FSFace.hA_det W hW a ha.1 ha.2)
    (hgp.mono fun a ha => FSFace.hB_det W hW a ha.1 ha.2) hm

end FSO1

/-! C7a: on `E_I` (with G1/G2), every row off `I` lies strictly on one side of a hyperplane
`{φ = β}` through the rows of `I`. -/
namespace FSC7
open FSFace FriendlyShadow.Gaussian

/-- Rows off `I` are off any hyperplane through the `d` rows of `I` (from G1). -/
theorem off_H {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (hG1 : G1det a)
    (I : Finset (Fin n)) (hI : I.card = d) (φ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ) (hφ : φ ≠ 0)
    (β : ℝ) (hφI : ∀ i ∈ I, φ (a i) = β) : ∀ j, j ∉ I → φ (a j) ≠ β := by
  classical
  intro j hj hjβ
  apply hφ
  ext z
  obtain ⟨c, hcS, hc0, hcz⟩ := hG1 (insert j I) (by rw [Finset.card_insert_of_notMem hj, hI]) z
  have hall : ∀ i, c i * φ (a i) = c i * β := by
    intro i
    by_cases hiS : i ∈ insert j I
    · rcases Finset.mem_insert.1 hiS with h | h
      · rw [h, hjβ]
      · rw [hφI i h]
    · rw [hcS i hiS]; simp
  have : φ z = 0 := by
    rw [← hcz, map_sum]
    simp_rw [map_smul, smul_eq_mul, hall, ← Finset.sum_mul, hc0, zero_mul]
  simpa using this

/-- C7a: strict one-sidedness of the rows off `I` on the edge event. -/
theorem onesided {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hW : Module.finrank ℝ W = 2) (a : Fin n → EuclideanSpace ℝ (Fin d)) (hG1 : G1det a)
    (hG2 : G2det W a) (I : Finset (Fin n)) (hI : I.card = d) (hE : edgeEvent W a I)
    (φ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ) (β : ℝ) (hφI : ∀ i ∈ I, φ (a i) = β)
    (hoff : ∀ j, j ∉ I → φ (a j) ≠ β) :
    (∀ j, j ∉ I → β < φ (a j)) ∨ (∀ j, j ∉ I → φ (a j) < β) := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨j1, hj1, h1'⟩, ⟨j2, hj2, h2'⟩⟩ := hcon
  have h1 : φ (a j1) < β := lt_of_le_of_ne h1' (hoff j1 hj1)
  have h2 : β < φ (a j2) := lt_of_le_of_ne h2' (Ne.symm (hoff j2 hj2))
  have hj12 : j1 ≠ j2 := by rintro rfl; linarith
  obtain ⟨u, v, huv, hseg⟩ := hE
  have huI : u ∈ convexHull ℝ (a '' ↑I) ∩ (W : Set _) := hseg ▸ left_mem_segment ℝ u v
  have hvI : v ∈ convexHull ℝ (a '' ↑I) ∩ (W : Set _) := hseg ▸ right_mem_segment ℝ u v
  obtain ⟨α, hα0, hαI, hα1, hαu⟩ := hull_rep a I u huI.1
  obtain ⟨β', hβ0, hβI, hβ1, hβv⟩ := hull_rep a I v hvI.1
  have hpos := supp_cover W a hG2 I hI huv.1 huI.2 hvI.2 α β' hα0 hαI hα1 hαu hβ0 hβI hβ1 hβv
  obtain ⟨i0, hi0⟩ : I.Nonempty := by
    rw [← Finset.card_pos]
    by_contra h0
    have hI0 : I = ∅ := Finset.card_eq_zero.1 (by omega)
    have := huI.1
    rw [hI0, Finset.coe_empty, Set.image_empty, convexHull_empty] at this
    exact this
  obtain ⟨c, hcS, hc0, hcz⟩ := hG1 (insert j1 I) (by rw [Finset.card_insert_of_notMem hj1, hI])
    (a j2 - a i0)
  set e : Fin n → ℝ := fun i => (if i = j2 then 1 else 0) - (if i = i0 then 1 else 0) - c i with he
  have he0 : ∑ i, e i = 0 := by
    simp only [he, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, hc0]
    ring
  have hea : ∑ i, e i • a i = 0 := by
    simp only [he, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, hcz]
    abel
  have hcφ : ∑ i, c i * φ (a i) = c j1 * (φ (a j1) - β) := by
    have hall : ∀ i, c i * φ (a i) = c i * β + (if i = j1 then c j1 * (φ (a j1) - β) else 0) := by
      intro i
      by_cases hij : i = j1
      · subst hij; simp; ring
      · rw [if_neg hij]
        by_cases hiI : i ∈ I
        · rw [hφI i hiI]; ring
        · rw [hcS i (by simp [hij, hiI])]; ring
    simp_rw [hall, Finset.sum_add_distrib, ← Finset.sum_mul, hc0, zero_mul, zero_add,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hcj1 : c j1 < 0 := by
    have hφe : ∑ i, e i * φ (a i) = 0 := by
      have := congrArg φ hea
      rw [map_sum, map_zero] at this
      simpa [map_smul, smul_eq_mul] using this
    have hexp : ∑ i, e i * φ (a i) = φ (a j2) - φ (a i0) - ∑ i, c i * φ (a i) := by
      simp only [he, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hexp, hcφ, hφI i0 hi0] at hφe
    have hneg : φ (a j1) - β < 0 := by linarith
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hc hneg.le]
  have hj1i0 : j1 ≠ i0 := fun h => hj1 (h ▸ hi0)
  have hj2i0 : j2 ≠ i0 := fun h => hj2 (h ▸ hi0)
  have hej1 : e j1 = - c j1 := by simp [he, hj12, hj1i0]
  have hej2 : e j2 = 1 := by
    have : c j2 = 0 := hcS j2 (by simp [Ne.symm hj12, hj2])
    simp [he, hj2i0, this]
  have heoff : ∀ i, i ∉ I → 0 ≤ e i := by
    intro i hi
    by_cases hi1 : i = j1
    · rw [hi1, hej1]; linarith
    · by_cases hi2 : i = j2
      · rw [hi2, hej2]; norm_num
      · have hci : c i = 0 := hcS i (by simp [hi1, hi])
        have hii0 : i ≠ i0 := fun h => hi (h ▸ hi0)
        simp [he, hi2, hii0, hci]
  set wt : Fin n → ℝ := fun i => (α i + β' i) / 2 with hwt
  have hwt0 : ∀ i, 0 ≤ wt i := fun i => by have := hα0 i; have := hβ0 i; simp only [hwt]; positivity
  have hwtI : ∀ i ∈ I, 0 < wt i := fun i hi => by simp only [hwt]; linarith [hpos i hi]
  have hwtoff : ∀ i, i ∉ I → wt i = 0 := fun i hi => by simp [hwt, hαI i hi, hβI i hi]
  set cI : Fin n → ℝ := fun i => if i ∈ I then e i else 0 with hcI
  obtain ⟨ε0, hε0, hε0i⟩ := pert_eps wt cI hwt0 (fun i hi => by
    by_cases h : i ∈ I
    · exact hwtI i h
    · exact absurd (by simp [hcI, h]) hi)
  set w2 : Fin n → ℝ := fun i => wt i + (ε0 / 2) * e i with hw2
  have hw2I : ∀ i ∈ I, 0 < w2 i := by
    intro i hi
    have := hε0i i
    simp only [hcI, if_pos hi] at this
    have := hwtI i hi
    simp only [hw2]; nlinarith
  have hw2off : ∀ i, i ∉ I → 0 ≤ w2 i := by
    intro i hi
    simp only [hw2, hwtoff i hi, zero_add]
    exact mul_nonneg (by positivity) (heoff i hi)
  have hw20 : ∀ i, 0 ≤ w2 i := fun i => by
    by_cases h : i ∈ I
    · exact (hw2I i h).le
    · exact hw2off i h
  have hw21 : ∑ i, w2 i = 1 := by
    simp only [hw2, Finset.sum_add_distrib, ← Finset.mul_sum, he0, mul_zero, add_zero, hwt,
      ← Finset.sum_div, hα1, hβ1]
    norm_num
  have hw2m : ∑ i, w2 i • a i = midpoint ℝ u v := by
    simp only [hw2, add_smul, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum, hea,
      smul_zero, add_zero]
    exact mid_rep a u v α β' hαu hβv
  have hcard := key_card W hW a hG1 huv w2 hw20 hw21 hw2m
  have hsub : insert j1 (insert j2 I) ⊆ Finset.univ.filter (fun i => 0 < w2 i) := by
    intro i hi
    simp only [Finset.mem_insert] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hi with rfl | rfl | hi
    · simp only [hw2, hwtoff _ hj1, zero_add, hej1]
      exact mul_pos (by positivity) (by linarith)
    · simp only [hw2, hwtoff _ hj2, zero_add, hej2, mul_one]; positivity
    · exact hw2I i hi
  have hc2 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [hj12, hj1]),
    Finset.card_insert_of_notMem hj2, hI] at hc2
  omega

end FSC7

/-! C7b: deterministic converse — a nondegenerate section of a supporting face is an edge. -/
namespace FSC7
open FSFace FriendlyShadow.Gaussian

theorem hull_le {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ) (β : ℝ) (h : ∀ j, φ (a j) ≤ β) :
    ∀ x ∈ convexHull ℝ (Set.range a), φ x ≤ β := by
  intro x hx
  have hsub : convexHull ℝ (Set.range a) ⊆ {x | φ x ≤ β} :=
    convexHull_min (by rintro _ ⟨j, rfl⟩; exact h j) (convex_halfSpace_le φ.isLinear β)
  exact hsub hx

theorem hull_eq {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (I : Finset (Fin n))
    (φ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ) (β : ℝ) (hφI : ∀ i ∈ I, φ (a i) = β) :
    ∀ x ∈ convexHull ℝ (a '' ↑I), φ x = β := by
  intro x hx
  have hsub : convexHull ℝ (a '' ↑I) ⊆ {x | φ x = β} :=
    convexHull_min (by rintro _ ⟨j, hj, rfl⟩; exact hφI j hj) (convex_hyperplane φ.isLinear β)
  exact hsub hx

theorem face_sub {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (I : Finset (Fin n))
    (φ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ) (β : ℝ) (hφI : ∀ i ∈ I, φ (a i) = β)
    (hside : ∀ j, j ∉ I → φ (a j) < β) :
    ∀ x ∈ convexHull ℝ (Set.range a), φ x = β → x ∈ convexHull ℝ (a '' ↑I) := by
  classical
  intro x hx hxβ
  have hrange : convexHull ℝ (Set.range a) =
      convexHull ℝ (a '' ↑(Finset.univ : Finset (Fin n))) := by
    rw [Finset.coe_univ, Set.image_univ]
  obtain ⟨lam, hl0, -, hl1, hlx⟩ := hull_rep a Finset.univ x (hrange ▸ hx)
  have hle : ∀ j, φ (a j) ≤ β := fun j => by
    by_cases hj : j ∈ I
    · exact (hφI j hj).le
    · exact (hside j hj).le
  have hsum : ∑ j, lam j * (β - φ (a j)) = 0 := by
    have : φ x = ∑ j, lam j * φ (a j) := by
      rw [← hlx, map_sum]; simp [map_smul, smul_eq_mul]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hl1, one_mul, ← this, hxβ,
      sub_self]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => mul_nonneg (hl0 j) (sub_nonneg.2 (hle j)))).1 hsum
  refine hlx ▸ hull_of_rep a I lam hl0 (fun j hj => ?_) hl1
  have := hz j (Finset.mem_univ j)
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · have := hside j hj; linarith

/-- C7b: if the rows off `I` lie strictly below a hyperplane `{φ = β}` through the rows of `I`
and `conv(a_I) ∩ W` is a nondegenerate segment, then `E_I` holds. -/
theorem exposed_edge {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (I : Finset (Fin n))
    (φ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ) (β : ℝ) (hφI : ∀ i ∈ I, φ (a i) = β)
    (hside : ∀ j, j ∉ I → φ (a j) < β) (u v : EuclideanSpace ℝ (Fin d)) (huv : u ≠ v)
    (hseg : convexHull ℝ (a '' ↑I) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) = segment ℝ u v) :
    edgeEvent W a I := by
  have hle : ∀ j, φ (a j) ≤ β := fun j => by
    by_cases hj : j ∈ I
    · exact (hφI j hj).le
    · exact (hside j hj).le
  have hHle := hull_le a φ β hle
  have hsegP : segment ℝ u v ⊆ polygon W a := by
    rw [← hseg]
    rintro x ⟨hx, hxW⟩
    exact ⟨convexHull_mono (Set.image_subset_range _ _) hx, hxW⟩
  refine ⟨u, v, ⟨huv, hsegP, ?_⟩, hseg⟩
  intro x1 hx1 x2 hx2 x hx hxo
  rw [← hseg] at hx
  have hxβ := hull_eq a I φ β hφI x hx.1
  obtain ⟨p, q, hp, hq, hpq, hpqx⟩ := hxo
  have h1 := hHle x1 hx1.1
  have h2 := hHle x2 hx2.1
  have hlin : p * φ x1 + q * φ x2 = β := by
    rw [← hxβ, ← hpqx, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hpqβ := congrArg (fun t => t * β) hpq
  simp only [one_mul, add_mul] at hpqβ
  have e1 : φ x1 = β := by
    by_contra hne
    have hlt : φ x1 < β := lt_of_le_of_ne h1 hne
    nlinarith [mul_pos hp (sub_pos.2 hlt), mul_nonneg hq.le (sub_nonneg.2 h2)]
  rw [← hseg]
  exact Set.mem_inter (face_sub a I φ β hφI hside x1 hx1.1 e1) hx1.2

/-- C7b, either side. -/
theorem exposed_edge' {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (I : Finset (Fin n))
    (φ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ) (β : ℝ) (hφI : ∀ i ∈ I, φ (a i) = β)
    (hside : (∀ j, j ∉ I → β < φ (a j)) ∨ (∀ j, j ∉ I → φ (a j) < β))
    (u v : EuclideanSpace ℝ (Fin d)) (huv : u ≠ v)
    (hseg : convexHull ℝ (a '' ↑I) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) = segment ℝ u v) :
    edgeEvent W a I := by
  rcases hside with h | h
  · exact exposed_edge W a I (-φ) (-β) (fun i hi => by simp [hφI i hi])
      (fun j hj => by simpa using h j hj) u v huv hseg
  · exact exposed_edge W a I φ β hφI h u v huv hseg

end FSC7


-- ===== DETAE.lean =====

set_option autoImplicit false



/-! O1c/O1b general position: almost surely (rows with densities)
(G1) any d+1 rows affinely span ℝᵈ, (G2) W together with any d-2 rows spans ℝᵈ. -/


open MeasureTheory


namespace FSDetAE

open FriendlyShadow.Gaussian FSCV

/-- C6c: almost surely the rows `t k` of `a` have an invertible graph matrix (no vertical hyperplane). -/
theorem det_ae {m n : ℕ} (μ : Fin (n + 1) → EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (t : Fin (m + 1) → Fin (n + 1)) (ht : Function.Injective t) :
    ∀ᵐ a ∂rowLaw μ, (gmat (fun k j => a (t k) (Fin.castSucc j))).det ≠ 0 := by
  have hw : LinearIndependent ℝ ![EuclideanSpace.single (Fin.last m) (1 : ℝ)] := by
    rw [linearIndependent_unique_iff]
    simp
  have h := FSGP.gen_li μ ![EuclideanSpace.single (Fin.last m) (1 : ℝ)] hw
    (fun a => a (t 0)) (continuous_apply _) m (fun k => t k.succ)
    (ht.comp (Fin.succ_injective _)) (by omega)
    (fun k a x => Function.update_of_ne (fun h => Fin.succ_ne_zero k (ht h).symm) _ _)
  filter_upwards [h] with a ha
  exact det_ne_of_li (fun k => a (t k)) ha

end FSDetAE


-- ===== SPLIT.lean =====

open MeasureTheory

namespace FSSplit


theorem lintegral_pi_prod_gen {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α] [Inhabited α]
    (μ : Measure α) [SigmaFinite μ] (g : ι → α → ENNReal) (hg : ∀ i, Measurable (g i)) :
    ∫⁻ x : ι → α, ∏ i, g i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, g i t ∂μ := by
  have hF : Measurable fun x : ι → α => ∏ i, g i (x i) :=
    Finset.measurable_prod _ (fun i _ => (hg i).comp (measurable_pi_apply i))
  have key : ∀ s : Finset ι, ∀ x : ι → α,
      (∫⋯∫⁻_s, (fun x : ι → α => ∏ i, g i (x i)) ∂(fun _ => μ)) x =
        ∏ i, (if i ∈ s then ∫⁻ t, g i t ∂μ else g i (x i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x; simp [lmarginal_empty]
    | @insert i s hi ih =>
      intro x
      rw [lmarginal_insert _ hF hi]
      simp_rw [ih]
      have h1 : ∀ t : α, (∏ k, (if k ∈ s then ∫⁻ t, g k t ∂μ else g k (Function.update x i t k))) =
          g i t * ∏ k ∈ Finset.univ.erase i, (if k ∈ s then ∫⁻ t, g k t ∂μ else g k (x k)) := by
        intro t
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
        simp only [if_neg hi, Function.update_self]
        congr 1
        refine Finset.prod_congr rfl fun k hk => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      simp_rw [h1]
      rw [lintegral_mul_const _ (hg i), ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      simp only [Finset.mem_insert, true_or, if_true]
      congr 1
      refine Finset.prod_congr rfl fun k hk => ?_
      simp [Finset.ne_of_mem_erase hk]
  rw [lintegral_eq_lmarginal_univ (fun _ => (default : α)), key]
  simp

theorem pi_withDensity_gen {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α] [Inhabited α]
    (μ : Measure α) [SigmaFinite μ] (f : ι → α → ENNReal)
    (hf : ∀ i, Measurable (f i)) [∀ i, SigmaFinite (μ.withDensity (f i))] :
    Measure.pi (fun i => μ.withDensity (f i)) =
      (Measure.pi fun _ => μ).withDensity (fun x => ∏ i, f i (x i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hind : ∀ x : ι → α, (Set.univ.pi s).indicator (fun x => ∏ i, f i (x i)) x =
      ∏ i, (s i).indicator (f i) (x i) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  simp_rw [hind]
  rw [lintegral_pi_prod_gen μ _ (fun i => (hf i).indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), lintegral_indicator (hs i)]

open FriendlyShadow.Gaussian

/-- Reassemble a configuration from the rows outside `I` and the rows of `I` (indexed by `Fin d`). -/
def join {n d : ℕ} {E : Type*} (I : Finset (Fin n)) (e : Fin d ≃ I) (b : {i // i ∉ I} → E)
    (y : Fin d → E) : Fin n → E :=
  fun i => if h : i ∈ I then y (e.symm ⟨i, h⟩) else b ⟨i, h⟩

lemma join_apply_e {n d : ℕ} {E : Type*} (I : Finset (Fin n)) (e : Fin d ≃ I)
    (b : {i // i ∉ I} → E) (y : Fin d → E) (k : Fin d) : join I e b y (e k) = y k := by
  simp [join]

/-- Step A+B of the core assembly: Fubini over the rows outside `I`, the rows of `I`
reindexed by `Fin d` with their product density. -/
theorem split {d n : ℕ} (μ : Fin n → EuclideanSpace ℝ (Fin d) → ℝ) (hm : ∀ i, Measurable (μ i))
    (I : Finset (Fin n)) (e : Fin d ≃ I)
    (F : (Fin n → EuclideanSpace ℝ (Fin d)) → ENNReal) (hF : Measurable F) :
    ∫⁻ a, F a ∂(rowLaw μ) =
      ∫⁻ b, (∫⁻ y : Fin d → EuclideanSpace ℝ (Fin d),
        (∏ k, ENNReal.ofReal (μ (e k) (y k))) * F (join I e b y))
        ∂(Measure.pi fun i : {i // i ∉ I} => densityMeasure (μ i)) := by
  set P : Fin n → Measure (EuclideanSpace ℝ (Fin d)) := fun i => densityMeasure (μ i) with hP
  haveI : ∀ i, SigmaFinite (P i) := fun i => by
    simp only [hP, densityMeasure]; infer_instance
  have hmp := measurePreserving_piEquivPiSubtypeProd P (· ∈ I)
  set eq := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => EuclideanSpace ℝ (Fin d))
    (· ∈ I) with heq
  have h1 : ∫⁻ a, F a ∂(rowLaw μ) = ∫⁻ z, F (eq.symm z)
      ∂((Measure.pi fun i : {i // i ∈ I} => P i).prod
        (Measure.pi fun i : {i // i ∉ I} => P i)) := by
    have h := hmp.lintegral_comp_emb eq.measurableEmbedding (fun z => F (eq.symm z))
    simp only [MeasurableEquiv.symm_apply_apply] at h
    show ∫⁻ a, F a ∂(Measure.pi P) = _
    convert h
  have hFm : Measurable fun z => F (eq.symm z) := hF.comp eq.symm.measurable
  rw [h1, lintegral_prod _ hFm.aemeasurable, lintegral_lintegral_swap hFm.aemeasurable]
  refine lintegral_congr fun b => ?_
  haveI : Inhabited (EuclideanSpace ℝ (Fin d)) := ⟨0⟩
  have hpc := measurePreserving_piCongrLeft (fun i : {i // i ∈ I} => P i) e
  rw [← hpc.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  have hpw : (Measure.pi fun k : Fin d => P (e k)) =
      (volume : Measure (Fin d → EuclideanSpace ℝ (Fin d))).withDensity
        (fun y => ∏ k, ENNReal.ofReal (μ (e k) (y k))) := by
    rw [MeasureTheory.volume_pi]
    have hpk : ∀ k, P (e k) = volume.withDensity (fun x => ENNReal.ofReal (μ (e k) x)) :=
      fun k => rfl
    simp_rw [hpk]
    haveI : ∀ k : Fin d, SigmaFinite ((volume : Measure (EuclideanSpace ℝ (Fin d))).withDensity
        (fun x => ENNReal.ofReal (μ (e k) x))) := fun k => by infer_instance
    exact pi_withDensity_gen volume (fun k x => ENNReal.ofReal (μ (e k) x))
      (fun k => ENNReal.measurable_ofReal.comp (hm _))
  have hjoin : ∀ y : Fin d → EuclideanSpace ℝ (Fin d),
      eq.symm (MeasurableEquiv.piCongrLeft (fun _ => EuclideanSpace ℝ (Fin d)) e y, b) =
        join I e b y := by
    intro y; funext i
    by_cases h : i ∈ I
    · have hi : (⟨i, h⟩ : {i // i ∈ I}) = e (e.symm ⟨i, h⟩) := (e.apply_symm_apply _).symm
      simp only [heq, MeasurableEquiv.piEquivPiSubtypeProd, join, h, dif_pos]
      simp only [MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk, Equiv.piEquivPiSubtypeProd_symm_apply, h, dif_pos]
      simp [MeasurableEquiv.piCongrLeft]
      conv_lhs => rw [hi]
      exact Equiv.piCongrLeft_apply_apply _ _ _ _
    · simp [heq, MeasurableEquiv.piEquivPiSubtypeProd, join, h]
  simp_rw [hjoin]
  have hmeas : Measurable (fun y : Fin d → EuclideanSpace ℝ (Fin d) =>
      ∏ k, ENNReal.ofReal (μ (e k) (y k))) :=
    Finset.measurable_prod _ fun k _ => ENNReal.measurable_ofReal.comp
      ((hm _).comp (measurable_pi_apply k))
  have hjm : Measurable (fun y : Fin d → EuclideanSpace ℝ (Fin d) => F (join I e b y)) := by
    refine hF.comp (measurable_pi_lambda _ fun i => ?_)
    by_cases h : i ∈ I
    · simp only [join, h, dif_pos]; exact measurable_pi_apply _
    · simp only [join, h, dif_neg, not_false_eq_true]; exact measurable_const
  rw [hpw, lintegral_withDensity_eq_lintegral_mul _ hmeas hjm]
  rfl

end FSSplit


-- ===== L21.lean =====

open MeasureTheory

set_option autoImplicit false

namespace FSL21
open FriendlyShadow.Gaussian

lemma L_nonneg {d : ℕ} (hd : 3 ≤ d) (μ : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ)
    (hL : LogLipschitz μ L) : 0 ≤ L := by
  obtain ⟨hpos, hlip⟩ := hL
  set x : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single ⟨0, by omega⟩ 1 with hxdef
  have hx : ‖x - 0‖ = 1 := by simp [hxdef]
  have h1 := hlip x 0
  have h2 := hlip 0 x
  rw [hx] at h1
  rw [norm_sub_rev, hx] at h2
  have hpx := hpos x
  have h3 : μ x ≤ Real.exp (L * 1) * (Real.exp (L * 1) * μ x) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le)
  rw [← mul_assoc, ← Real.exp_add] at h3
  by_contra hneg
  push Not at hneg
  have h4 : Real.exp (L * 1 + L * 1) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
  rw [Real.exp_zero] at h4
  have := mul_lt_mul_of_pos_right h4 hpx
  linarith

end FSL21

open MeasureTheory FriendlyShadow.Gaussian RealInnerProductSpace ENNReal in
theorem FSL21_solution {d : ℕ} (hd : 3 ≤ d) (μ : EuclideanSpace ℝ (Fin d) → ℝ) (hμ : IsDensity μ)
    (y : EuclideanSpace ℝ (Fin d)) (hy : HasMean μ y) (L : ℝ) (hL : LogLipschitz μ L)
    (R : ℝ) (hR : CutoffRadiusLE μ y (1 / 2) R) :
    (d : ℝ) / 3 ≤ L * R := by
  classical
  have hL0 := FSL21.L_nonneg hd μ L hL
  obtain ⟨hμ0, hμint, hμ1⟩ := hμ
  obtain ⟨hpos, hlip⟩ := hL
  have hfint : Integrable (fun u => μ (y + u)) := hμint.comp_add_left y
  have hf1 : ∫ u, μ (y + u) = 1 := by
    rw [integral_add_left_eq_self (fun x => μ x) y]; exact hμ1
  set Bl : Set (EuclideanSpace ℝ (Fin d)) := Metric.ball 0 R with hBl
  have hBlm : MeasurableSet Bl := measurableSet_ball
  -- mass of the ball ≥ 1/2
  set S : Set (EuclideanSpace ℝ (Fin d)) := {x | R ≤ ‖x - y‖} with hSdef
  have hSm : MeasurableSet S :=
    measurableSet_le measurable_const (continuous_norm.comp (continuous_id.sub continuous_const)).measurable
  have hSint : ∫ x in S, μ x ≤ 1 / 2 := by
    have h := hR
    unfold CutoffRadiusLE densityMeasure at h
    rw [withDensity_apply _ hSm, ← ofReal_integral_eq_lintegral_ofReal hμint.integrableOn
      (Filter.Eventually.of_forall (fun x => hμ0 x))] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp h
  have hpt : ∀ u, S.indicator μ (y + u) = Blᶜ.indicator (fun u => μ (y + u)) u := by
    intro u
    have e : (y + u ∈ S) ↔ (u ∈ Blᶜ) := by
      simp only [hSdef, hBl, Set.mem_setOf_eq, add_sub_cancel_left, Set.mem_compl_iff,
        Metric.mem_ball, dist_zero_right, not_lt]
    by_cases h : u ∈ Blᶜ
    · rw [Set.indicator_of_mem (e.mpr h), Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem (fun h' => h (e.mp h')), Set.indicator_of_notMem h]
  have hcomp : ∫ u, Blᶜ.indicator (fun u => μ (y + u)) u ≤ 1 / 2 := by
    rw [← integral_indicator hSm] at hSint
    rw [← integral_add_left_eq_self (S.indicator μ) y] at hSint
    simpa only [hpt] using hSint
  have hB : 1 / 2 ≤ ∫ u, Bl.indicator (fun u => μ (y + u)) u := by
    have hsum : (∫ u, Bl.indicator (fun u => μ (y + u)) u) +
        ∫ u, Blᶜ.indicator (fun u => μ (y + u)) u = 1 := by
      rw [← integral_add (hfint.indicator hBlm) (hfint.indicator hBlm.compl)]
      simp only [← Pi.add_apply (Bl.indicator _), Set.indicator_self_add_compl]
      exact hf1
    linarith
  -- the scaled integral
  set g : EuclideanSpace ℝ (Fin d) → ℝ := (Metric.ball 0 (3 * R)).indicator (fun u => μ (y + u))
    with hg
  have hgint : Integrable g := hfint.indicator measurableSet_ball
  have hg1 : ∫ v, g v ≤ 1 := by
    rw [← hf1]
    refine integral_mono hgint hfint ?_
    exact Set.indicator_le_self' (fun v _ => hμ0 _)
  have hA : (3 : ℝ) ^ d * ∫ u, g ((3 : ℝ) • u) ≤ 1 := by
    rw [Measure.integral_comp_smul_of_nonneg volume g (3 : ℝ) (hR := by norm_num), finrank_euclideanSpace_fin, smul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    exact hg1
  have hAint : Integrable (fun u => g ((3 : ℝ) • u)) := hgint.comp_smul (by norm_num)
  have hAB : Real.exp (-(2 * L * R)) * ∫ u, Bl.indicator (fun u => μ (y + u)) u ≤
      ∫ u, g ((3 : ℝ) • u) := by
    rw [← integral_const_mul]
    refine integral_mono ((hfint.indicator hBlm).const_mul _) hAint (fun u => ?_)
    by_cases hu : u ∈ Bl
    · have hu' : ‖u‖ < R := by simpa [hBl] using hu
      have h3u : (3 : ℝ) • u ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (3 * R) := by
        simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
        rw [abs_of_pos (by norm_num : (0:ℝ) < 3)]; linarith
      simp only [hg]
      rw [Set.indicator_of_mem hu, Set.indicator_of_mem h3u]
      have hl := hlip (y + u) (y + (3 : ℝ) • u)
      have e : (y + u) - (y + (3 : ℝ) • u) = (-2 : ℝ) • u := by module
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_neg (by norm_num : (-2:ℝ) < 0)] at hl
      have hexp : Real.exp (L * (-(-2) * ‖u‖)) ≤ Real.exp (2 * L * R) := by
        apply Real.exp_le_exp.mpr
        nlinarith [norm_nonneg u]
      have hp3 := hpos (y + (3 : ℝ) • u)
      have h5 : μ (y + u) ≤ Real.exp (2 * L * R) * μ (y + (3 : ℝ) • u) :=
        hl.trans (mul_le_mul_of_nonneg_right hexp hp3.le)
      have h6 : Real.exp (-(2 * L * R)) * Real.exp (2 * L * R) = 1 := by
        rw [← Real.exp_add]; simp
      calc Real.exp (-(2 * L * R)) * μ (y + u)
          ≤ Real.exp (-(2 * L * R)) * (Real.exp (2 * L * R) * μ (y + (3 : ℝ) • u)) :=
            mul_le_mul_of_nonneg_left h5 (Real.exp_pos _).le
        _ = μ (y + (3 : ℝ) • u) := by rw [← mul_assoc, h6, one_mul]
    · rw [Set.indicator_of_notMem hu, mul_zero]
      exact Set.indicator_nonneg (fun v _ => hμ0 _) _
  -- combine: 3^d ≤ 2 exp(2LR)
  set X := Real.exp (2 * L * R) with hX
  have hXpos : 0 < X := Real.exp_pos _
  have hkey : (3 : ℝ) ^ d * (X⁻¹ * (1 / 2)) ≤ 1 := by
    have h1 : X⁻¹ * (1 / 2) ≤ ∫ u, g ((3 : ℝ) • u) := by
      rw [hX, ← Real.exp_neg]
      exact (mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le).trans hAB
    exact (mul_le_mul_of_nonneg_left h1 (by positivity)).trans hA
  have h3X : (3 : ℝ) ^ d ≤ 2 * X := by
    have e : (3 : ℝ) ^ d = (3 : ℝ) ^ d * (X⁻¹ * (1 / 2)) * (2 * X) := by
      field_simp
    rw [e]
    calc (3 : ℝ) ^ d * (X⁻¹ * (1 / 2)) * (2 * X) ≤ 1 * (2 * X) :=
          mul_le_mul_of_nonneg_right hkey (by positivity)
      _ = 2 * X := one_mul _
  by_contra hlt
  push Not at hlt
  set E := Real.exp (2 / 3) with hE
  have hXE : X < E ^ d := by
    rw [hX, hE, ← Real.exp_nat_mul]
    apply Real.exp_lt_exp.mpr
    linarith
  have hE2 : E < 2 := by
    rw [hE, ← Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.log_two_gt_d9
    linarith
  have hE0 : 0 < E := Real.exp_pos _
  have h6 : (27 / 8 : ℝ) ≤ (3 / 2) ^ d := by
    calc (27 / 8 : ℝ) = (3 / 2) ^ 3 := by norm_num
      _ ≤ (3 / 2) ^ d := pow_le_pow_right₀ (by norm_num) hd
  have h5 : (27 / 8 : ℝ) * E ^ d ≤ (3 : ℝ) ^ d := by
    calc (27 / 8 : ℝ) * E ^ d ≤ (3 / 2) ^ d * E ^ d :=
          mul_le_mul_of_nonneg_right h6 (pow_nonneg hE0.le _)
      _ = (3 / 2 * E) ^ d := (mul_pow _ _ _).symm
      _ ≤ 3 ^ d := pow_le_pow_left₀ (by positivity) (by linarith) d
  have hEd : 0 < E ^ d := pow_pos hE0 d
  linarith


-- ===== ../../probe/b53119b3_lib/L29.lean =====

set_option autoImplicit false

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace FSL29
open FriendlyShadow.Gaussian

variable {d n : ℕ}

theorem dens_prob {μ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsDensity μ) :
    IsProbabilityMeasure (densityMeasure μ) := by
  constructor
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal h.2.1 (ae_of_all _ h.1), h.2.2, ENNReal.ofReal_one]

/-- One row far from its center: probability at most `cutoffLevel`. -/
theorem bad_row_le (μ : Fin n → EuclideanSpace ℝ (Fin d) → ℝ) (hμ : ∀ i, IsDensity (μ i))
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (p R : ℝ)
    (hR : ∀ i, CutoffRadiusLE (μ i) (abar i) p R) (i : Fin n) :
    rowLaw μ {a | R ≤ ‖a i - abar i‖} ≤ ENNReal.ofReal p := by
  haveI : ∀ i, IsProbabilityMeasure (densityMeasure (μ i)) := fun i => dens_prob (hμ i)
  have hS : MeasurableSet {x : EuclideanSpace ℝ (Fin d) | R ≤ ‖x - abar i‖} :=
    measurableSet_le measurable_const ((measurable_id.sub_const _).norm)
  have h1 : {a : Fin n → EuclideanSpace ℝ (Fin d) | R ≤ ‖a i - abar i‖} =
      Function.eval i ⁻¹' {x | R ≤ ‖x - abar i‖} := rfl
  rw [h1, rowLaw, (measurePreserving_eval (fun i => densityMeasure (μ i)) i).measure_preimage
    hS.nullMeasurableSet]
  exact hR i

/-- The union over `I` of the far events has probability at most `1/C(n,d)`. -/
theorem bad_le (hd : 3 ≤ d) (hdn : d ≤ n) (μ : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (hμ : ∀ i, IsDensity (μ i)) (abar : Fin n → EuclideanSpace ℝ (Fin d)) (R : ℝ)
    (hR : ∀ i, CutoffRadiusLE (μ i) (abar i) (cutoffLevel n d) R)
    (I : Finset (Fin n)) (hI : I.card = d) :
    rowLaw μ (⋃ i ∈ I, {a | R ≤ ‖a i - abar i‖}) ≤ ENNReal.ofReal (1 / (n.choose d : ℝ)) := by
  calc rowLaw μ (⋃ i ∈ I, {a | R ≤ ‖a i - abar i‖})
      ≤ ∑ i ∈ I, rowLaw μ {a | R ≤ ‖a i - abar i‖} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ I, ENNReal.ofReal (cutoffLevel n d) :=
        Finset.sum_le_sum fun i _ => bad_row_le μ hμ abar _ R hR i
    _ = ENNReal.ofReal (1 / (n.choose d : ℝ)) := by
        rw [Finset.sum_const, hI, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg d)]
        congr 1
        have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
        have hc0 : (0 : ℝ) < (n.choose d : ℝ) := by exact_mod_cast Nat.choose_pos hdn
        unfold cutoffLevel
        field_simp

/-- Off the far events the bounded-diameter event holds. -/
theorem bdd_of_near (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (habar : ∀ i, ‖abar i‖ ≤ 1) (R : ℝ)
    (I : Finset (Fin n)) (a : Fin n → EuclideanSpace ℝ (Fin d))
    (ha : ∀ i ∈ I, ‖a i - abar i‖ < R) : boundedDiamEvent W a I R := by
  intro i hi j hj
  refine (Submodule.norm_starProjection_apply_le _ _).trans ?_
  have e : a i - a j = (a i - abar i) - (a j - abar j) + (abar i - abar j) := by abel
  rw [e]
  have h1 := norm_add_le ((a i - abar i) - (a j - abar j)) (abar i - abar j)
  have h2 := norm_sub_le (a i - abar i) (a j - abar j)
  have h3 := norm_sub_le (abar i) (abar j)
  have := ha i hi; have := ha j hj; have := habar i; have := habar j
  linarith

/-- `Pr[E_I] ≤ 2 Pr[E_I ∩ D]` for `I ∈ B`. -/
theorem prob_le_two (hd : 3 ≤ d) (hdn : d ≤ n)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (μ : Fin n → EuclideanSpace ℝ (Fin d) → ℝ) (hμ : ∀ i, IsDensity (μ i))
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (habar : ∀ i, ‖abar i‖ ≤ 1) (R : ℝ)
    (hR : ∀ i, CutoffRadiusLE (μ i) (abar i) (cutoffLevel n d) R)
    (I : Finset (Fin n)) (hI : I.card = d)
    (hB : ENNReal.ofReal (2 / (n.choose d : ℝ)) ≤ rowLaw μ {a | edgeEvent W a I}) :
    rowLaw μ {a | edgeEvent W a I} ≤
      rowLaw μ {a | edgeEvent W a I ∧ boundedDiamEvent W a I R} * 2 := by
  haveI : ∀ i, IsProbabilityMeasure (densityMeasure (μ i)) := fun i => dens_prob (hμ i)
  haveI : IsProbabilityMeasure (rowLaw μ) := by unfold rowLaw; infer_instance
  set p := rowLaw μ {a | edgeEvent W a I}
  set q := rowLaw μ {a | edgeEvent W a I ∧ boundedDiamEvent W a I R}
  have hsub : {a | edgeEvent W a I} ⊆ {a | edgeEvent W a I ∧ boundedDiamEvent W a I R} ∪
      ⋃ i ∈ I, {a | R ≤ ‖a i - abar i‖} := by
    intro a ha
    by_cases h : ∀ i ∈ I, ‖a i - abar i‖ < R
    · exact Or.inl ⟨ha, bdd_of_near W abar habar R I a h⟩
    · push_neg at h
      obtain ⟨i, hi, hle⟩ := h
      exact Or.inr (Set.mem_biUnion hi hle)
  have hpq : p ≤ q + ENNReal.ofReal (1 / (n.choose d : ℝ)) :=
    (measure_mono hsub).trans ((measure_union_le _ _).trans
      (add_le_add le_rfl (bad_le hd hdn μ hμ abar R hR I hI)))
  have hhalf : ENNReal.ofReal (1 / (n.choose d : ℝ)) ≤ p / 2 := by
    have e : ENNReal.ofReal (1 / (n.choose d : ℝ)) = ENNReal.ofReal (2 / (n.choose d : ℝ)) / 2 := by
      rw [ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_inv_of_pos (by norm_num),
        ← ENNReal.ofReal_mul (by norm_num)]
      congr 1; ring
    rw [e]; exact ENNReal.div_le_div_right hB 2
  have hp_top : p / 2 ≠ ∞ := ENNReal.div_ne_top (measure_ne_top _ _) two_ne_zero
  have h2 : p / 2 + p / 2 ≤ q + p / 2 := by
    rw [ENNReal.add_halves]; exact hpq.trans (add_le_add le_rfl hhalf)
  have h3 : p / 2 ≤ q := ENNReal.le_of_add_le_add_right hp_top h2
  exact (ENNReal.div_le_iff_le_mul (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)).1 h3

end FSL29

open FriendlyShadow.Gaussian in
open scoped RealInnerProductSpace ENNReal in
theorem FSL29_solution {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hW : Module.finrank ℝ W = 2)
    (μ : Fin n → EuclideanSpace ℝ (Fin d) → ℝ) (hμ : ∀ i, IsDensity (μ i))
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (hmean : ∀ i, HasMean (μ i) (abar i))
    (habar : ∀ i, ‖abar i‖ ≤ 1) (R : ℝ)
    (hR : ∀ i, CutoffRadiusLE (μ i) (abar i) (cutoffLevel n d) R)
    (I : Finset (Fin n)) (hI : I.card = d)
    (hB : ENNReal.ofReal (2 / (n.choose d : ℝ)) ≤ rowLaw μ {a | edgeEvent W a I}) :
    (∫⁻ a in {a | edgeEvent W a I ∧ boundedDiamEvent W a I R}, edgeLen W a I ∂(rowLaw μ)) *
        rowLaw μ {a | edgeEvent W a I} ≤
      2 * (∫⁻ a in {a | edgeEvent W a I}, edgeLen W a I ∂(rowLaw μ)) *
        rowLaw μ {a | edgeEvent W a I ∧ boundedDiamEvent W a I R} := by
  have hp := FSL29.prob_le_two hd hdn W μ hμ abar habar R hR I hI hB
  have hint : (∫⁻ a in {a | edgeEvent W a I ∧ boundedDiamEvent W a I R}, edgeLen W a I ∂(rowLaw μ)) ≤
      ∫⁻ a in {a | edgeEvent W a I}, edgeLen W a I ∂(rowLaw μ) :=
    lintegral_mono_set (fun a ha => ha.1)
  calc _ ≤ (∫⁻ a in {a | edgeEvent W a I}, edgeLen W a I ∂(rowLaw μ)) *
        (rowLaw μ {a | edgeEvent W a I ∧ boundedDiamEvent W a I R} * 2) := mul_le_mul' hint hp
    _ = _ := by ring


-- ===== LLINE.lean =====
section LLINEsec
open MeasureTheory Filter Topology

namespace FSLL
open FriendlyShadow.Gaussian

/-- A log-Lipschitz function is continuous. -/
theorem cont {d : ℕ} {μ : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ} (h : LogLipschitz μ L) :
    Continuous μ := by
  rw [continuous_iff_continuousAt]
  intro y
  have hup : Tendsto (fun x => Real.exp (L * ‖x - y‖) * μ y) (𝓝 y) (𝓝 (μ y)) := by
    have hc : Continuous (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (L * ‖x - y‖) * μ y) := by
      fun_prop
    simpa using hc.tendsto y
  have hlo : Tendsto (fun x => Real.exp (-(L * ‖y - x‖)) * μ y) (𝓝 y) (𝓝 (μ y)) := by
    have hc : Continuous
        (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (-(L * ‖y - x‖)) * μ y) := by
      fun_prop
    simpa using hc.tendsto y
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hup (fun x => ?_) (fun x => h.2 x y)
  have h1 := h.2 y x
  calc Real.exp (-(L * ‖y - x‖)) * μ y
      ≤ Real.exp (-(L * ‖y - x‖)) * (Real.exp (L * ‖y - x‖) * μ x) := by
        gcongr
    _ = μ x := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- Every line restriction of a log-Lipschitz probability density has finite mass. -/
theorem line_lint_lt_top {d : ℕ} {μ : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ}
    (hD : IsDensity μ) (hL : LogLipschitz μ L) (v w : EuclideanSpace ℝ (Fin d)) (hw : w ≠ 0) :
    ∫⁻ γ : ℝ, ENNReal.ofReal (μ (v + γ • w)) < ⊤ := by
  have hc := cont hL
  set B := Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 with hB
  set K := Real.exp |L| with hK
  set ι : EuclideanSpace ℝ (Fin d) → ENNReal := B.indicator (fun _ => (1 : ENNReal)) with hι
  have hιm : Measurable ι := measurable_const.indicator measurableSet_closedBall
  have hpt : ∀ γ : ℝ, ∀ u, ι u * ENNReal.ofReal (μ (v + γ • w)) ≤
      ENNReal.ofReal K * (ι u * ENNReal.ofReal (μ (v + γ • w + u))) := by
    intro γ u
    by_cases hu : u ∈ B
    · simp only [hι, Set.indicator_of_mem hu, one_mul]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      apply ENNReal.ofReal_le_ofReal
      have h1 := hL.2 (v + γ • w) (v + γ • w + u)
      have hn : ‖v + γ • w - (v + γ • w + u)‖ ≤ 1 := by
        have : v + γ • w - (v + γ • w + u) = -u := by abel
        rw [this, norm_neg]; simpa [hB] using hu
      have hn0 := norm_nonneg (v + γ • w - (v + γ • w + u))
      have hexp : Real.exp (L * ‖v + γ • w - (v + γ • w + u)‖) ≤ K := by
        apply Real.exp_le_exp.2
        have := le_abs_self L
        have := abs_nonneg L
        nlinarith
      calc μ (v + γ • w) ≤ _ := h1
        _ ≤ K * μ (v + γ • w + u) := mul_le_mul_of_nonneg_right hexp (hL.1 _).le
    · simp [hι, Set.indicator_of_notMem hu]
  -- the diameter bound for a slab
  have hslab : ∀ y : EuclideanSpace ℝ (Fin d),
      ∫⁻ γ : ℝ, ι (y - (v + γ • w)) ≤ ENNReal.ofReal (2 / ‖w‖) := by
    intro y
    have hw0 : 0 < ‖w‖ := norm_pos_iff.2 hw
    set S : Set ℝ := (fun γ : ℝ => y - (v + γ • w)) ⁻¹' B with hS
    have hSm : MeasurableSet S :=
      measurableSet_closedBall.preimage (by fun_prop : Continuous fun γ : ℝ => y - (v + γ • w)).measurable
    have heq : (fun γ : ℝ => ι (y - (v + γ • w))) = S.indicator (fun _ => (1 : ENNReal)) := by
      funext γ
      by_cases hγ : γ ∈ S
      · rw [Set.indicator_of_mem hγ]; simp only [hι]; exact Set.indicator_of_mem (s := B) hγ _
      · rw [Set.indicator_of_notMem hγ]; simp only [hι]
        exact Set.indicator_of_notMem (s := B) hγ _
    rw [heq, lintegral_indicator_const hSm, one_mul]
    refine (Real.volume_le_diam S).trans (Metric.ediam_le fun a ha b hb => ?_)
    rw [edist_dist, Real.dist_eq]
    apply ENNReal.ofReal_le_ofReal
    have ha' : ‖y - (v + a • w)‖ ≤ 1 := by simpa [hS, hB] using ha
    have hb' : ‖y - (v + b • w)‖ ≤ 1 := by simpa [hS, hB] using hb
    have hdiff : (b - a) • w = (y - (v + a • w)) - (y - (v + b • w)) := by
      rw [sub_smul]; abel
    have hn : |a - b| * ‖w‖ ≤ 2 := by
      have := norm_sub_le (y - (v + a • w)) (y - (v + b • w))
      rw [← hdiff, norm_smul, Real.norm_eq_abs, abs_sub_comm] at this
      linarith
    rw [le_div_iff₀ hw0]; exact hn
  have hfm : ∀ γ : ℝ, Measurable fun u => ι u * ENNReal.ofReal (μ (v + γ • w + u)) := by
    intro γ
    exact hιm.mul (ENNReal.measurable_ofReal.comp (hc.comp (by fun_prop)).measurable)
  have hjoint : Measurable (Function.uncurry fun (u : EuclideanSpace ℝ (Fin d)) (γ : ℝ) =>
      ι u * ENNReal.ofReal (μ (v + γ • w + u))) := by
    exact (hιm.comp measurable_fst).mul
      (ENNReal.measurable_ofReal.comp (hc.comp (by fun_prop)).measurable)
  have hjoint2 : Measurable (Function.uncurry fun (y : EuclideanSpace ℝ (Fin d)) (γ : ℝ) =>
      ι (y - (v + γ • w)) * ENNReal.ofReal (μ y)) := by
    exact (hιm.comp (by fun_prop : Continuous fun p : EuclideanSpace ℝ (Fin d) × ℝ =>
      p.1 - (v + p.2 • w)).measurable).mul
      (ENNReal.measurable_ofReal.comp (hc.measurable.comp measurable_fst))
  have hmain : volume B * ∫⁻ γ : ℝ, ENNReal.ofReal (μ (v + γ • w)) ≤
      ENNReal.ofReal K * (ENNReal.ofReal (2 / ‖w‖) * ∫⁻ y, ENNReal.ofReal (μ y)) := by
    calc volume B * ∫⁻ γ : ℝ, ENNReal.ofReal (μ (v + γ • w))
        = ∫⁻ u, ι u * ∫⁻ γ : ℝ, ENNReal.ofReal (μ (v + γ • w)) := by
          rw [lintegral_mul_const _ hιm, hι, lintegral_indicator_const measurableSet_closedBall,
            one_mul]
      _ = ∫⁻ u, ∫⁻ γ : ℝ, ι u * ENNReal.ofReal (μ (v + γ • w)) := by
          refine lintegral_congr fun u => ?_
          have hιfin : ι u ≠ ⊤ := by by_cases hu : u ∈ B <;> simp [hι, hu]
          rw [lintegral_const_mul' _ _ hιfin]
      _ ≤ ∫⁻ u, ∫⁻ γ : ℝ, ENNReal.ofReal K * (ι u * ENNReal.ofReal (μ (v + γ • w + u))) :=
          lintegral_mono fun u => lintegral_mono fun γ => hpt γ u
      _ = ENNReal.ofReal K * ∫⁻ γ : ℝ, ∫⁻ u, ι u * ENNReal.ofReal (μ (v + γ • w + u)) := by
          simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          rw [lintegral_lintegral_swap hjoint.aemeasurable]
      _ = ENNReal.ofReal K * ∫⁻ γ : ℝ, ∫⁻ y, ι (y - (v + γ • w)) * ENNReal.ofReal (μ y) := by
          congr 1
          refine lintegral_congr fun γ => ?_
          rw [← lintegral_add_right_eq_self (μ := volume)
            (fun y => ι (y - (v + γ • w)) * ENNReal.ofReal (μ y)) (v + γ • w)]
          simp only [add_sub_cancel_right]
          refine lintegral_congr fun u => ?_
          rw [add_comm u]
      _ = ENNReal.ofReal K * ∫⁻ y, ENNReal.ofReal (μ y) * ∫⁻ γ : ℝ, ι (y - (v + γ • w)) := by
          congr 1
          rw [← lintegral_lintegral_swap hjoint2.aemeasurable]
          refine lintegral_congr fun y => ?_
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact lintegral_congr fun γ => mul_comm _ _
      _ ≤ ENNReal.ofReal K * ∫⁻ y, ENNReal.ofReal (μ y) * ENNReal.ofReal (2 / ‖w‖) := by
          gcongr with y
          exact hslab y
      _ = ENNReal.ofReal K * (ENNReal.ofReal (2 / ‖w‖) * ∫⁻ y, ENNReal.ofReal (μ y)) := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm (∫⁻ y, _)]
  have hfin : ENNReal.ofReal K * (ENNReal.ofReal (2 / ‖w‖) * ∫⁻ y, ENNReal.ofReal (μ y)) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hD.2.1.lintegral_lt_top)
  have hBpos : volume B ≠ 0 := (Metric.measure_closedBall_pos volume 0 one_pos).ne'
  by_contra hne
  rw [not_lt, top_le_iff] at hne
  rw [hne, ENNReal.mul_top hBpos] at hmain
  exact absurd (lt_of_le_of_lt hmain hfin) (lt_irrefl _)

theorem line_integrable {d : ℕ} {μ : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ}
    (hD : IsDensity μ) (hL : LogLipschitz μ L) (v w : EuclideanSpace ℝ (Fin d)) (hw : w ≠ 0) :
    Integrable (fun γ : ℝ => μ (v + γ • w)) := by
  refine ⟨((cont hL).comp (by fun_prop)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun γ => (hL.1 _).le)]
  exact line_lint_lt_top hD hL v w hw

end FSLL
end LLINEsec


-- ===== C8 tail (relay 11) =====

namespace FSC8
open FSC6 FSFrame FSC6E FSC6R FSDir FSC7C FSFace FSC7 FSSplit FriendlyShadow.Gaussian Module
open scoped RealInnerProductSpace

/-- The functional `p ↦ p_last - Σ cᵢ pᵢ`; it is constant `t` on the graph hyperplane `H_{c,t}`. -/
noncomputable def phi {k : ℕ} (c : Fin (k + 2) → ℝ) :
    EuclideanSpace ℝ (Fin (k + 3)) →ₗ[ℝ] ℝ where
  toFun p := p (Fin.last (k + 2)) - ∑ i, p (Fin.castSucc i) * c i
  map_add' p q := by
    simp only [PiLp.add_apply, add_mul, Finset.sum_add_distrib]; ring
  map_smul' a p := by
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum]; ring

lemma phi_Pt {k : ℕ} (c : Fin (k + 2) → ℝ) (t : ℝ) (x : Fin (k + 2) → ℝ) :
    phi c (Pt c t x) = t := by
  simp [phi, Pt]

lemma phi_ne {k : ℕ} (c : Fin (k + 2) → ℝ) : phi c ≠ 0 := by
  intro h
  have := LinearMap.congr_fun h (EuclideanSpace.single (Fin.last (k + 2)) (1 : ℝ))
  simp [phi, Fin.castSucc_ne_last] at this

lemma li_append_one {V : Type*} [AddCommGroup V] [Module ℝ V] {m : ℕ} (w : V) (f : Fin m → V)
    (hli : LinearIndependent ℝ (Fin.append ![w] f)) :
    LinearIndependent ℝ f ∧ w ∉ Submodule.span ℝ (Set.range f) := by
  have hcomp := hli.comp (Fin.natAdd 1) (Fin.natAdd_injective m 1)
  have hf : (Fin.append ![w] f) ∘ Fin.natAdd 1 = f := by
    funext j; simp [Fin.append_right]
  rw [hf] at hcomp
  refine ⟨hcomp, ?_⟩
  have hx : (Fin.castAdd m (0 : Fin 1)) ∉ Set.range (Fin.natAdd 1 : Fin m → Fin (1 + m)) := by
    rintro ⟨j, hj⟩
    have := congrArg Fin.val hj
    simp at this
  have h1 := hli.notMem_span_image hx
  have h2 : Fin.append ![w] f '' Set.range (Fin.natAdd 1) = Set.range f := by
    rw [← Set.range_comp, hf]
  rw [h2] at h1
  simpa [Fin.append_left] using h1

/-- `hK` from general position: if `w₁ ∈ W` and the differences of the graph points are
linearly independent together with `w₁`, the hyperplane direction meets `W` in a line. -/
theorem hK_of_li {k : ℕ} (c : Fin (k + 2) → ℝ) (t : ℝ)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin (k + 3)))) (hW : finrank ℝ W = 2)
    (w1 : EuclideanSpace ℝ (Fin (k + 3))) (hw1 : w1 ∈ W) (y : Fin (k + 3) → Fin (k + 2) → ℝ)
    (hli : LinearIndependent ℝ
      (Fin.append ![w1] (fun j : Fin (k + 2) => Pt c t (y j.succ) - Pt c t (y 0)))) :
    finrank ℝ ↥(LinearMap.range (Lc c) ⊓ W) = 1 := by
  set R := LinearMap.range (Lc c) with hR
  obtain ⟨hli2, hnot⟩ := li_append_one _ _ hli
  have hdiff : ∀ j : Fin (k + 2), Pt c t (y j.succ) - Pt c t (y 0) = Lc c (y j.succ - y 0) := by
    intro j; rw [Pt_eq c t (y j.succ), Pt_eq c t (y 0), map_sub]; abel
  have hle : Submodule.span ℝ (Set.range fun j : Fin (k + 2) => Pt c t (y j.succ) - Pt c t (y 0))
      ≤ R := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show Pt c t (y j.succ) - Pt c t (y 0) ∈ R
    rw [hdiff]; exact LinearMap.mem_range_self _ _
  have hR2 : finrank ℝ R = k + 2 := by
    rw [hR, LinearMap.finrank_range_of_inj (Lc_injective c), Module.finrank_fin_fun]
  have hS2 : finrank ℝ (Submodule.span ℝ
      (Set.range fun j : Fin (k + 2) => Pt c t (y j.succ) - Pt c t (y 0))) = k + 2 := by
    rw [finrank_span_eq_card hli2, Fintype.card_fin]
  have hSeq := Submodule.eq_of_le_of_finrank_eq hle (by rw [hS2, hR2])
  have hw1R : w1 ∉ R := by rw [← hSeq]; exact hnot
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq R W
  have hsup : finrank ℝ ↥(R ⊔ W) ≤ k + 3 := by
    have := Submodule.finrank_le (R ⊔ W)
    simpa [finrank_euclideanSpace] using this
  have hinf : finrank ℝ ↥(R ⊓ W) ≤ 2 := by
    rw [← hW]; exact Submodule.finrank_mono inf_le_right
  have hne : finrank ℝ ↥(R ⊓ W) ≠ 2 := by
    intro h2
    have := Submodule.eq_of_le_of_finrank_eq (inf_le_right : R ⊓ W ≤ W) (by rw [h2, hW])
    exact hw1R ((this ▸ inf_le_left : W ≤ R) hw1)
  omega

section frame_pt
variable {k n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin (k + 3))))
  (o ω : EuclideanSpace ℝ (Fin (k + 3)))
  (ι : EuclideanSpace ℝ (Fin (k + 1)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k + 3)))
  (I : Finset (Fin n)) (e : Fin (k + 3) ≃ I) (b : {i // i ∉ I} → EuclideanSpace ℝ (Fin (k + 3)))
  (u : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1))) (h : Fin (k + 3) → ℝ)

lemma join_in {i : Fin n} (hi : i ∈ I) :
    join I e b (fun j => o + ι (u j) + h j • ω) i = o + ι (u (e.symm ⟨i, hi⟩)) +
      h (e.symm ⟨i, hi⟩) • ω := by
  simp [join, hi]

lemma join_img :
    join I e b (fun j => o + ι (u j) + h j • ω) '' (I : Set (Fin n)) =
      Set.range fun j => o + ι (u j) + h j • ω := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨e.symm ⟨i, hi⟩, (join_in o ω ι I e b u h hi).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨e j, (e j).2, join_apply_e I e b _ j⟩

lemma join_out {i : Fin n} (hi : i ∉ I) :
    join I e b (fun j => o + ι (u j) + h j • ω) i = b ⟨i, hi⟩ := by
  simp [join, hi]

/-- C8b (left): on the event, the slice is one-sided, has bounded shape and contains `-u 0`. -/
theorem lhs_pt (hW : finrank ℝ W = 2) (hoW : o ∈ W) (hωW : ω ∈ W)
    (hω : ‖ω‖ = 1) (hιω : ∀ x, ⟪ι x, ω⟫ = 0) (hWx : ∀ x (t : ℝ), o + ι x + t • ω ∈ W → x = 0)
    (c : Fin (k + 2) → ℝ) (t : ℝ) (hon : ∀ x (s : ℝ), phi c (o + ι x + s • ω) = t)
    (hI : I.card = k + 3) (R : ℝ)
    (hG1 : G1det (join I e b (fun j => o + ι (u j) + h j • ω)))
    (hG2 : G2det W (join I e b (fun j => o + ι (u j) + h j • ω)))
    (hE : edgeEvent W (join I e b (fun j => o + ι (u j) + h j • ω)) I)
    (hD : boundedDiamEvent W (join I e b (fun j => o + ι (u j) + h j • ω)) I R)
    (hdet : ∑ i, h i * hcof u i ≠ 0) :
    ((∀ j (hj : j ∉ I), t < phi c (b ⟨j, hj⟩)) ∨ (∀ j (hj : j ∉ I), phi c (b ⟨j, hj⟩) < t)) ∧
      (∀ i j, ‖(u i - u 0) - (u j - u 0)‖ ≤ 2 + 2 * R) ∧
      -u 0 ∈ convexHull ℝ (Set.range fun i => u i - u 0) := by
  set a := join I e b (fun j => o + ι (u j) + h j • ω) with ha
  have hφI : ∀ i ∈ I, phi c (a i) = t := by
    intro i hi; rw [ha, join_in o ω ι I e b u h hi]; exact hon _ _
  have hoff := off_H a hG1 I hI (phi c) (phi_ne c) t hφI
  refine ⟨?_, ?_, ?_⟩
  · rcases onesided W hW a hG1 hG2 I hI hE (phi c) t hφI hoff with h1 | h1
    · left; intro j hj; have := h1 j hj; rwa [ha, join_out o ω ι I e b u h hj] at this
    · right; intro j hj; have := h1 j hj; rwa [ha, join_out o ω ι I e b u h hj] at this
  · intro i j
    have hdir : lineDir W a I = ℝ ∙ ω := by
      unfold lineDir
      rw [ha, join_img o ω ι I e b u h]
      exact dir_inf_W W o ω ι hoW hωW hWx u h hdet
    have h1 := hD (e i) (e i).2 (e j) (e j).2
    simp only [hdir] at h1
    have hae : ∀ l, a (e l) = o + ι (u l) + h l • ω := fun l => by
      rw [ha]; exact join_apply_e I e b _ l
    rw [hae, hae] at h1
    have h2 : (o + ι (u i) + h i • ω) - (o + ι (u j) + h j • ω) =
        ι (u i - u j) + (h i - h j) • ω := by
      rw [map_sub, sub_smul]; abel
    rw [h2, proj_norm ω ι hιω] at h1
    rwa [sub_sub_sub_cancel_right]
  · obtain ⟨p, q, _, hseg⟩ := hE
    refine slice_mem_hull W o ω ι hoW hωW hω hιω hWx u h ?_
    rw [← join_img o ω ι I e b u h, ← ha, hseg]
    exact ⟨p, left_mem_segment ℝ p q⟩

/-- C8b (right): a one-sided slice with positive chord length is the edge event, and its
edge length is `chordLen · |Σ z h|`. -/
theorem rhs_pt (hoW : o ∈ W) (hωW : ω ∈ W)
    (hω : ‖ω‖ = 1) (hιω : ∀ x, ⟪ι x, ω⟫ = 0) (hWx : ∀ x (t : ℝ), o + ι x + t • ω ∈ W → x = 0)
    (c : Fin (k + 2) → ℝ) (t : ℝ) (hon : ∀ x (s : ℝ), phi c (o + ι x + s • ω) = t)
    (hO : (∀ j (hj : j ∉ I), t < phi c (b ⟨j, hj⟩)) ∨ (∀ j (hj : j ∉ I), phi c (b ⟨j, hj⟩) < t))
    (hC : hcof u ≠ 0) (hq : -u 0 ∈ convexHull ℝ (Set.range fun i => u i - u 0))
    (hpos : 0 < chordLen (fun i => u i - u 0) (-u 0) * |∑ i, zc u i * h i|) :
    edgeEvent W (join I e b (fun j => o + ι (u j) + h j • ω)) I ∧
      edgeLen W (join I e b (fun j => o + ι (u j) + h j • ω)) I =
        ENNReal.ofReal (chordLen (fun i => u i - u 0) (-u 0) * |∑ i, zc u i * h i|) := by
  set a := join I e b (fun j => o + ι (u j) + h j • ω) with ha
  have hφI : ∀ i ∈ I, phi c (a i) = t := by
    intro i hi; rw [ha, join_in o ω ι I e b u h hi]; exact hon _ _
  have hz : IsKernelComb (fun i => u i - u 0) (zc u) := kernel_comb u hC
  have hrank := rank_of_hcof u hC
  have hdiam := slice_diam W o ω ι hoW hωW hω hιω hWx u h (zc u) hz hrank hq
  have himg : a '' (I : Set (Fin n)) = Set.range fun j => o + ι (u j) + h j • ω := by
    rw [ha]; exact join_img o ω ι I e b u h
  refine ⟨?_, ?_⟩
  · obtain ⟨p1, p2, hne, hseg⟩ :=
      slice_seg W o ω ι hoW hωW hω hιω hWx u h (by rw [hdiam]; exact hpos)
    have hside : (∀ j, j ∉ I → t < phi c (a j)) ∨ (∀ j, j ∉ I → phi c (a j) < t) := by
      rcases hO with h1 | h1
      · left; intro j hj; rw [ha, join_out o ω ι I e b u h hj]; exact h1 j hj
      · right; intro j hj; rw [ha, join_out o ω ι I e b u h hj]; exact h1 j hj
    exact exposed_edge' W a I (phi c) t hφI hside p1 p2 hne (by rw [himg]; exact hseg)
  · unfold edgeLen
    rw [himg, ediam_eq, hdiam]
    exact (isBounded_convexHull.2 (Set.finite_range _).isBounded).subset Set.inter_subset_left

end frame_pt

section slice_level
variable {k : ℕ}

/-- The rows after `shift_shape`: `u = (x, x + s'₀, …)`. -/
def Ucons (x : EuclideanSpace ℝ (Fin (k + 1))) (s' : Fin (k + 2) → EuclideanSpace ℝ (Fin (k + 1))) :
    Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1)) :=
  Fin.cons x (fun j => x + s' j)

/-- The shape `(0, s'₀, …)`. -/
def S0 (s' : Fin (k + 2) → EuclideanSpace ℝ (Fin (k + 1))) :
    Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1)) :=
  Fin.cons 0 s'

lemma S0_zero (s' : Fin (k + 2) → EuclideanSpace ℝ (Fin (k + 1))) : S0 s' 0 = 0 := by
  simp [S0]

lemma Ucons_eq (x : EuclideanSpace ℝ (Fin (k + 1))) (s' : Fin (k + 2) → EuclideanSpace ℝ (Fin (k + 1)))
    (j : Fin (k + 3)) : Ucons x s' j = 0 - -x + S0 s' j := by
  refine Fin.cases ?_ (fun j => ?_) j <;> simp [Ucons, S0]

lemma Ucons_zero (x : EuclideanSpace ℝ (Fin (k + 1))) (s' : Fin (k + 2) → EuclideanSpace ℝ (Fin (k + 1))) :
    Ucons x s' 0 = x := by
  simp [Ucons]

lemma Ucons_fun (x : EuclideanSpace ℝ (Fin (k + 1))) (s' : Fin (k + 2) → EuclideanSpace ℝ (Fin (k + 1))) :
    Ucons x s' = fun j => x + S0 s' j := by
  funext j; rw [Ucons_eq]; simp

lemma Ucons_sub (x : EuclideanSpace ℝ (Fin (k + 1))) (s' : Fin (k + 2) → EuclideanSpace ℝ (Fin (k + 1))) :
    (fun i => Ucons x s' i - Ucons x s' 0) = S0 s' := by
  funext i; rw [Ucons_eq, Ucons_eq, S0_zero]; simp

lemma hcof_U (x : EuclideanSpace ℝ (Fin (k + 1))) (s' : Fin (k + 2) → EuclideanSpace ℝ (Fin (k + 1))) :
    hcof (Ucons x s') = hcof (S0 s') := by
  rw [Ucons_fun, hcof_translate]

lemma zc_U (x : EuclideanSpace ℝ (Fin (k + 1))) (s' : Fin (k + 2) → EuclideanSpace ℝ (Fin (k + 1))) :
    zc (Ucons x s') = zc (S0 s') := by
  unfold zc; rw [hcof_U]

lemma frame_norm (ω : EuclideanSpace ℝ (Fin (k + 3)))
    (ι : EuclideanSpace ℝ (Fin (k + 1)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k + 3)))
    (hω : ‖ω‖ = 1) (hιω : ∀ x, ⟪ι x, ω⟫ = 0) (o : EuclideanSpace ℝ (Fin (k + 3)))
    (u u' : EuclideanSpace ℝ (Fin (k + 1))) (h h' : ℝ) :
    ‖(o + ι u + h • ω) - (o + ι u' + h' • ω)‖ = Real.sqrt (‖u - u'‖ ^ 2 + (h - h') ^ 2) := by
  have h2 : (o + ι u + h • ω) - (o + ι u' + h' • ω) = ι (u - u') + (h - h') • ω := by
    rw [map_sub, sub_smul]; abel
  rw [h2, ← Real.sqrt_sq (norm_nonneg _), norm_add_sq_real, inner_smul_right, hιω,
    LinearIsometry.norm_map, norm_smul, hω, Real.norm_eq_abs, mul_one, sq_abs]
  ring_nf

/-- The slice densities `mubar i x h = μᵢ(o + ι x + h ω)` satisfy the hypotheses of `FSSlice.slice`. -/
lemma mubar_facts (ω : EuclideanSpace ℝ (Fin (k + 3)))
    (ι : EuclideanSpace ℝ (Fin (k + 1)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k + 3)))
    (hω : ‖ω‖ = 1) (hιω : ∀ x, ⟪ι x, ω⟫ = 0) (o : EuclideanSpace ℝ (Fin (k + 3)))
    (ν : EuclideanSpace ℝ (Fin (k + 3)) → ℝ) (L τ : ℝ) (hD : IsDensity ν) (hLL : LogLipschitz ν L)
    (hLV : LineVarianceGE ν τ) (x : EuclideanSpace ℝ (Fin (k + 1))) :
    (∀ h : ℝ, 0 < ν (o + ι x + h • ω)) ∧
    (∀ (x' : EuclideanSpace ℝ (Fin (k + 1))) (h h' : ℝ), ν (o + ι x + h • ω) ≤
      Real.exp (L * Real.sqrt (‖x - x'‖ ^ 2 + (h - h') ^ 2)) * ν (o + ι x' + h' • ω)) ∧
    Measurable (fun h : ℝ => ν (o + ι x + h • ω)) ∧
    Integrable (fun h : ℝ => ν (o + ι x + h • ω)) ∧
    (Integrable (fun γ : ℝ => γ ^ 2 * ν (o + ι x + γ • ω)) →
      τ ^ 2 * (∫ γ : ℝ, ν (o + ι x + γ • ω)) ^ 2 ≤
        (∫ γ : ℝ, γ ^ 2 * ν (o + ι x + γ • ω)) * (∫ γ : ℝ, ν (o + ι x + γ • ω)) -
          (∫ γ : ℝ, γ * ν (o + ι x + γ • ω)) ^ 2) := by
  have hω0 : ω ≠ 0 := by intro h0; rw [h0, norm_zero] at hω; exact zero_ne_one hω
  have hint := FSLL.line_integrable hD hLL (o + ι x) ω hω0
  refine ⟨fun h => hLL.1 _, fun x' h h' => ?_, ?_, hint, fun h2 => ?_⟩
  · have := hLL.2 (o + ι x + h • ω) (o + ι x' + h' • ω)
    rwa [frame_norm ω ι hω hιω] at this
  · exact (FSLL.cont hLL).measurable.comp (by fun_prop)
  · refine hLV (o + ι x) ω hω hint h2 ?_
    rw [integral_pos_iff_support_of_nonneg (fun γ => (hLL.1 _).le) hint]
    have : Function.support (fun γ : ℝ => ν (o + ι x + γ • ω)) = Set.univ :=
      Set.eq_univ_of_forall fun γ => (hLL.1 _).ne'
    rw [this]; simp

end slice_level

lemma mlm {a b : ENNReal} (h : a ≤ b) (c : ENNReal) : c * a ≤ c * b := by gcongr

lemma chordLen_nonneg {V : Type*} [AddCommGroup V] [Module ℝ V] {d : ℕ} (s : Fin d → V) (q : V) :
    0 ≤ chordLen s q := by
  refine Real.sSup_nonneg fun x hx => ?_
  obtain ⟨l, -, l', -, rfl⟩ := hx
  exact Finset.sum_nonneg fun i _ => abs_nonneg _

/-- C8 per-shape comparison: for a fixed hyperplane frame, one-sided outside rows and a fixed
shape `s'`, the left (event) integral is at most the right (edge length) integral. -/
theorem slice_cmp {k n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin (k + 3)))) (hW : finrank ℝ W = 2)
    (o ω : EuclideanSpace ℝ (Fin (k + 3)))
    (ι : EuclideanSpace ℝ (Fin (k + 1)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k + 3)))
    (hoW : o ∈ W) (hωW : ω ∈ W) (hω : ‖ω‖ = 1) (hιω : ∀ x, ⟪ι x, ω⟫ = 0)
    (hWx : ∀ x (t : ℝ), o + ι x + t • ω ∈ W → x = 0)
    (c : Fin (k + 2) → ℝ) (t : ℝ) (hon : ∀ x (s : ℝ), phi c (o + ι x + s • ω) = t)
    (I : Finset (Fin n)) (hI : I.card = k + 3) (e : Fin (k + 3) ≃ I)
    (b : {i // i ∉ I} → EuclideanSpace ℝ (Fin (k + 3)))
    (μ : Fin n → EuclideanSpace ℝ (Fin (k + 3)) → ℝ) (hμ : ∀ i, IsDensity (μ i))
    (L τ R : ℝ) (hL : 0 < L) (hτ : 0 < τ) (hR : 0 ≤ R)
    (hLL : ∀ i, LogLipschitz (μ i) L) (hLV : ∀ i, LineVarianceGE (μ i) τ)
    (hLR : ((k + 3 : ℕ) : ℝ) / 3 ≤ L * R)
    (g M : (Fin n → EuclideanSpace ℝ (Fin (k + 3))) → ENNReal)
    (hg : ∀ a, g a ≠ 0 → edgeEvent W a I ∧ boundedDiamEvent W a I R ∧ G1det a ∧ G2det W a)
    (hg' : ∀ a, g a ≤ ENNReal.ofReal (Real.exp (-2) / (((k + 3 : ℕ) : ℝ) * L * (1 + R)) *
      (τ / (2 * Real.sqrt ((k + 3 : ℕ) : ℝ)))))
    (hM : ∀ a, edgeEvent W a I → edgeLen W a I ≤ M a)
    (s' : Fin (k + 2) → EuclideanSpace ℝ (Fin (k + 1))) :
    ∫⁻ x, ∫⁻ hh : Fin (k + 3) → ℝ,
      ENNReal.ofReal |∑ i, hh i * hcof (Ucons x s') i| *
        ((∏ j, ENNReal.ofReal (μ (e j) (o + ι (Ucons x s' j) + hh j • ω))) *
          g (join I e b (fun j => o + ι (Ucons x s' j) + hh j • ω))) ≤
    ∫⁻ x, ∫⁻ hh : Fin (k + 3) → ℝ,
      ENNReal.ofReal |∑ i, hh i * hcof (Ucons x s') i| *
        ((∏ j, ENNReal.ofReal (μ (e j) (o + ι (Ucons x s' j) + hh j • ω))) *
          M (join I e b (fun j => o + ι (Ucons x s' j) + hh j • ω))) := by
  classical
  set S := S0 s' with hS
  set C := convexHull ℝ (Set.range S) with hCdef
  set mubar : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1)) → ℝ → ℝ :=
    fun i y hh => μ (e i) (o + ι y + hh • ω) with hmub
  set c' := Real.exp (-2) / (((k + 3 : ℕ) : ℝ) * L * (1 + R)) *
      (τ / (2 * Real.sqrt ((k + 3 : ℕ) : ℝ))) with hc'
  set O := (∀ j (hj : j ∉ I), t < phi c (b ⟨j, hj⟩)) ∨ (∀ j (hj : j ∉ I), phi c (b ⟨j, hj⟩) < t)
    with hO
  have hnz : ∀ x (hh : Fin (k + 3) → ℝ), ∑ i, hh i * hcof (Ucons x s') i ≠ 0 →
      g (join I e b (fun j => o + ι (Ucons x s' j) + hh j • ω)) ≠ 0 →
      O ∧ (∀ i j, ‖S i - S j‖ ≤ 2 + 2 * R) ∧ hcof S ≠ 0 ∧ -x ∈ C := by
    intro x hh hw hgz
    obtain ⟨hE, hD, hG1, hG2⟩ := hg _ hgz
    obtain ⟨h1, h2, h3⟩ := lhs_pt W o ω ι I e b (Ucons x s') hh hW hoW hωW hω hιω hWx c t hon hI R
      hG1 hG2 hE hD hw
    have hsub : ∀ i, Ucons x s' i - Ucons x s' 0 = S i := fun i => congrFun (Ucons_sub x s') i
    refine ⟨h1, fun i j => ?_, ?_, ?_⟩
    · have := h2 i j; rwa [hsub, hsub] at this
    · intro h0; apply hw; rw [hcof_U, ← hS, h0]; simp
    · rw [Ucons_sub, Ucons_zero] at h3; exact h3
  by_cases hmain : O ∧ (∀ i j, ‖S i - S j‖ ≤ 2 + 2 * R) ∧ hcof S ≠ 0
  swap
  · have h0 : ∀ x (hh : Fin (k + 3) → ℝ), ENNReal.ofReal |∑ i, hh i * hcof (Ucons x s') i| *
        ((∏ j, ENNReal.ofReal (μ (e j) (o + ι (Ucons x s' j) + hh j • ω))) *
          g (join I e b (fun j => o + ι (Ucons x s' j) + hh j • ω))) = 0 := by
      intro x hh
      by_cases hw : ∑ i, hh i * hcof (Ucons x s') i = 0
      · rw [hw]; simp
      by_cases hgz : g (join I e b (fun j => o + ι (Ucons x s' j) + hh j • ω)) = 0
      · rw [hgz]; simp
      obtain ⟨h1, h2, h3, -⟩ := hnz x hh hw hgz
      exact absurd ⟨h1, h2, h3⟩ hmain
    simp only [h0, lintegral_zero]
    exact bot_le
  obtain ⟨hO', hdm, hC⟩ := hmain
  set κ := ∑ j, |hcof S j| with hκ
  set z := zc S with hz
  have hwt : ∀ x (hh : Fin (k + 3) → ℝ), ENNReal.ofReal |∑ i, hh i * hcof (Ucons x s') i| =
      ENNReal.ofReal κ * ENNReal.ofReal |∑ i, z i * hh i| := by
    intro x hh
    rw [abs_sum_eq, zc_U, hcof_U, ← hS,
      ENNReal.ofReal_mul (Finset.sum_nonneg fun j _ => abs_nonneg _)]
  have hprod : ∀ x (hh : Fin (k + 3) → ℝ),
      ∏ j, ENNReal.ofReal (μ (e j) (o + ι (Ucons x s' j) + hh j • ω)) =
        ENNReal.ofReal (∏ j, mubar j (0 - -x + S j) (hh j)) := by
    intro x hh
    rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => ((hLL _).1 _).le)]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Ucons_eq]
  have hCm : MeasurableSet C := by
    rw [hCdef]; exact (Set.Finite.isCompact_convexHull ℝ (Set.finite_range S)).isClosed.measurableSet
  have hneg : ∀ F : EuclideanSpace ℝ (Fin (k + 1)) → ENNReal, ∫⁻ x, F (-x) = ∫⁻ q, F q :=
    fun F => (Measure.measurePreserving_neg volume).lintegral_comp_emb
      (MeasurableEquiv.neg _).measurableEmbedding F
  have hcne : ENNReal.ofReal c' * ENNReal.ofReal κ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  -- left side
  have hL1 : ∀ x (hh : Fin (k + 3) → ℝ), ENNReal.ofReal |∑ i, hh i * hcof (Ucons x s') i| *
      ((∏ j, ENNReal.ofReal (μ (e j) (o + ι (Ucons x s' j) + hh j • ω))) *
        g (join I e b (fun j => o + ι (Ucons x s' j) + hh j • ω))) ≤
      ENNReal.ofReal c' * ENNReal.ofReal κ * C.indicator (fun q => ENNReal.ofReal
        (|∑ i, z i * hh i| * ∏ i, mubar i (0 - q + S i) (hh i))) (-x) := by
    intro x hh
    by_cases hw : ∑ i, hh i * hcof (Ucons x s') i = 0
    · rw [hw]; simp
    by_cases hgz : g (join I e b (fun j => o + ι (Ucons x s' j) + hh j • ω)) = 0
    · rw [hgz]; simp
    obtain ⟨-, -, -, hx⟩ := hnz x hh hw hgz
    rw [Set.indicator_of_mem hx, hwt, hprod, ENNReal.ofReal_mul (abs_nonneg _)]
    calc ENNReal.ofReal κ * ENNReal.ofReal |∑ i, z i * hh i| *
          (ENNReal.ofReal (∏ j, mubar j (0 - -x + S j) (hh j)) *
            g (join I e b (fun j => o + ι (Ucons x s' j) + hh j • ω)))
        = ENNReal.ofReal κ * ENNReal.ofReal |∑ i, z i * hh i| *
          ENNReal.ofReal (∏ j, mubar j (0 - -x + S j) (hh j)) *
            g (join I e b (fun j => o + ι (Ucons x s' j) + hh j • ω)) := by ring
      _ ≤ ENNReal.ofReal κ * ENNReal.ofReal |∑ i, z i * hh i| *
          ENNReal.ofReal (∏ j, mubar j (0 - -x + S j) (hh j)) * ENNReal.ofReal c' :=
          FSC8.mlm (hg' _) _
      _ = _ := by ring
  -- right side
  have hR1 : ∀ x (hh : Fin (k + 3) → ℝ), ENNReal.ofReal κ * C.indicator (fun q =>
      ENNReal.ofReal (chordLen S q) * ENNReal.ofReal ((∑ i, z i * hh i) ^ 2 *
        ∏ i, mubar i (0 - q + S i) (hh i))) (-x) ≤
      ENNReal.ofReal |∑ i, hh i * hcof (Ucons x s') i| *
        ((∏ j, ENNReal.ofReal (μ (e j) (o + ι (Ucons x s' j) + hh j • ω))) *
          M (join I e b (fun j => o + ι (Ucons x s' j) + hh j • ω))) := by
    intro x hh
    by_cases hx : -x ∈ C
    swap
    · rw [Set.indicator_of_notMem hx, mul_zero]; exact bot_le
    rw [Set.indicator_of_mem hx]
    have hch : 0 ≤ chordLen S (-x) := chordLen_nonneg _ _
    by_cases hp : 0 < chordLen S (-x) * |∑ i, z i * hh i|
    swap
    · have h0 : chordLen S (-x) * |∑ i, z i * hh i| = 0 :=
        le_antisymm (not_lt.1 hp) (mul_nonneg hch (abs_nonneg _))
      rcases mul_eq_zero.1 h0 with h0 | h0
      · rw [h0]; simp
      · rw [abs_eq_zero] at h0; rw [h0]; simp
    have hq' : -(Ucons x s' 0) ∈ convexHull ℝ (Set.range fun i => Ucons x s' i - Ucons x s' 0) := by
      rw [Ucons_sub, Ucons_zero]; exact hx
    have hC' : hcof (Ucons x s') ≠ 0 := by rw [hcof_U]; exact hC
    have hp' : 0 < chordLen (fun i => Ucons x s' i - Ucons x s' 0) (-(Ucons x s' 0)) *
        |∑ i, zc (Ucons x s') i * hh i| := by
      rw [Ucons_sub, Ucons_zero, zc_U]; exact hp
    obtain ⟨hE, hlen⟩ := rhs_pt W o ω ι I e b (Ucons x s') hh hoW hωW hω hιω hWx c t hon hO' hC'
      hq' hp'
    have hMle := hM _ hE
    rw [hlen, Ucons_sub, Ucons_zero, zc_U] at hMle
    rw [hwt, hprod]
    have e1 : ENNReal.ofReal κ * (ENNReal.ofReal (chordLen S (-x)) *
        ENNReal.ofReal ((∑ i, z i * hh i) ^ 2 * ∏ i, mubar i (0 - -x + S i) (hh i))) =
        ENNReal.ofReal κ * ENNReal.ofReal |∑ i, z i * hh i| *
          (ENNReal.ofReal (∏ j, mubar j (0 - -x + S j) (hh j)) *
            ENNReal.ofReal (chordLen S (-x) * |∑ i, z i * hh i|)) := by
      rw [ENNReal.ofReal_mul (sq_nonneg _), ← sq_abs, sq,
        ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_mul hch]
      ring
    rw [e1]
    exact FSC8.mlm (FSC8.mlm hMle _) _
  -- integrate the left side
  have hLint : ∫⁻ x, ∫⁻ hh : Fin (k + 3) → ℝ,
      ENNReal.ofReal |∑ i, hh i * hcof (Ucons x s') i| *
        ((∏ j, ENNReal.ofReal (μ (e j) (o + ι (Ucons x s' j) + hh j • ω))) *
          g (join I e b (fun j => o + ι (Ucons x s' j) + hh j • ω))) ≤
      ENNReal.ofReal c' * ENNReal.ofReal κ *
        ∫⁻ q in C, heightMarginal mubar S z (0 - q) := by
    calc _ ≤ ∫⁻ x, ∫⁻ hh : Fin (k + 3) → ℝ, ENNReal.ofReal c' * ENNReal.ofReal κ *
          C.indicator (fun q => ENNReal.ofReal
            (|∑ i, z i * hh i| * ∏ i, mubar i (0 - q + S i) (hh i))) (-x) :=
          lintegral_mono fun x => lintegral_mono fun hh => hL1 x hh
      _ = ∫⁻ x, ENNReal.ofReal c' * ENNReal.ofReal κ *
          C.indicator (fun q => heightMarginal mubar S z (0 - q)) (-x) := by
          refine lintegral_congr fun x => ?_
          rw [lintegral_const_mul' _ _ hcne]
          congr 1
          by_cases hx : -x ∈ C
          · simp only [Set.indicator_of_mem hx]; rfl
          · simp only [Set.indicator_of_notMem hx, lintegral_zero]
      _ = ENNReal.ofReal c' * ENNReal.ofReal κ *
          ∫⁻ q, C.indicator (fun q => heightMarginal mubar S z (0 - q)) q := by
          rw [lintegral_const_mul' _ _ hcne,
            hneg (fun q => C.indicator (fun q => heightMarginal mubar S z (0 - q)) q)]
      _ = _ := by rw [lintegral_indicator hCm]
  have hRint : ENNReal.ofReal κ * ∫⁻ q in C, ENNReal.ofReal (chordLen S q) *
        ∫⁻ hh : Fin (k + 3) → ℝ, ENNReal.ofReal ((∑ i, z i * hh i) ^ 2 *
          ∏ i, mubar i (0 - q + S i) (hh i)) ≤
      ∫⁻ x, ∫⁻ hh : Fin (k + 3) → ℝ,
      ENNReal.ofReal |∑ i, hh i * hcof (Ucons x s') i| *
        ((∏ j, ENNReal.ofReal (μ (e j) (o + ι (Ucons x s' j) + hh j • ω))) *
          M (join I e b (fun j => o + ι (Ucons x s' j) + hh j • ω))) := by
    calc _ = ENNReal.ofReal κ * ∫⁻ q, C.indicator (fun q => ENNReal.ofReal (chordLen S q) *
          ∫⁻ hh : Fin (k + 3) → ℝ, ENNReal.ofReal ((∑ i, z i * hh i) ^ 2 *
            ∏ i, mubar i (0 - q + S i) (hh i))) q := by rw [lintegral_indicator hCm]
      _ = ENNReal.ofReal κ * ∫⁻ x, C.indicator (fun q => ENNReal.ofReal (chordLen S q) *
          ∫⁻ hh : Fin (k + 3) → ℝ, ENNReal.ofReal ((∑ i, z i * hh i) ^ 2 *
            ∏ i, mubar i (0 - q + S i) (hh i))) (-x) := by rw [hneg]
      _ = ∫⁻ x, ∫⁻ hh : Fin (k + 3) → ℝ, ENNReal.ofReal κ * C.indicator (fun q =>
          ENNReal.ofReal (chordLen S q) * ENNReal.ofReal ((∑ i, z i * hh i) ^ 2 *
            ∏ i, mubar i (0 - q + S i) (hh i))) (-x) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun x => ?_
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          by_cases hx : -x ∈ C
          · simp only [Set.indicator_of_mem hx]
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          · simp only [Set.indicator_of_notMem hx, lintegral_zero]
      _ ≤ _ := lintegral_mono fun x => lintegral_mono fun hh => hR1 x hh
  -- the slice inequality
  have hrank : Module.finrank ℝ (Submodule.span ℝ (Set.range S)) = k + 3 - 2 := by
    have := rank_of_hcof S hC
    have hS' : (fun i => S i - S 0) = S := by
      funext i; rw [hS, S0_zero, sub_zero]
    rw [hS'] at this; rw [this]; omega
  have hzk : IsKernelComb S z := by
    have := kernel_comb S hC
    have hS' : (fun i => S i - S 0) = S := by
      funext i; rw [hS, S0_zero, sub_zero]
    simp only [hS, S0_zero, sub_zero] at this
    exact this
  have hsl := FSSlice.slice (d := k + 3) (by omega) S (by rw [hS, S0_zero]) hrank L R hL hR hdm hLR
    z hzk mubar
    (fun i x hh => (mubar_facts ω ι hω hιω o (μ (e i)) L τ (hμ _) (hLL _) (hLV _) x).1 hh)
    (fun i x x' hh hh' => (mubar_facts ω ι hω hιω o (μ (e i)) L τ (hμ _) (hLL _) (hLV _) x).2.1
      x' hh hh')
    (fun i x => (mubar_facts ω ι hω hιω o (μ (e i)) L τ (hμ _) (hLL _) (hLV _) x).2.2.1)
    (fun i x => (mubar_facts ω ι hω hιω o (μ (e i)) L τ (hμ _) (hLL _) (hLV _) x).2.2.2.1)
    τ hτ.le
    (fun i x => (mubar_facts ω ι hω hιω o (μ (e i)) L τ (hμ _) (hLL _) (hLV _) x).2.2.2.2) 0
  calc _ ≤ ENNReal.ofReal c' * ENNReal.ofReal κ *
        ∫⁻ q in C, heightMarginal mubar S z (0 - q) := hLint
    _ = ENNReal.ofReal κ * (ENNReal.ofReal c' *
        ∫⁻ q in C, heightMarginal mubar S z (0 - q)) := by ring
    _ ≤ ENNReal.ofReal κ * ∫⁻ q in C, ENNReal.ofReal (chordLen S q) *
        ∫⁻ hh : Fin (k + 3) → ℝ, ENNReal.ofReal ((∑ i, z i * hh i) ^ 2 *
          ∏ i, mubar i (0 - q + S i) (hh i)) := FSC8.mlm hsl _
    _ ≤ _ := hRint

lemma measurable_join {n d : ℕ} {E : Type*} [MeasurableSpace E] (I : Finset (Fin n)) (e : Fin d ≃ I)
    (b : {i // i ∉ I} → E) : Measurable (fun y : Fin d → E => join I e b y) := by
  refine measurable_pi_lambda _ fun i => ?_
  unfold join
  by_cases hi : i ∈ I
  · simp only [dif_pos hi]; exact measurable_pi_apply _
  · simp only [dif_neg hi]; exact measurable_const

lemma continuous_hcof {k : ℕ} (i : Fin (k + 3)) :
    Continuous fun u : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1)) => hcof u i := by
  unfold hcof cof
  refine continuous_const.mul (Continuous.matrix_det ?_)
  refine Continuous.matrix_submatrix ?_ _ _
  refine continuous_pi fun r => continuous_pi fun l => ?_
  simp only [FSC6.gmat, Matrix.of_apply]
  refine Fin.lastCases ?_ (fun l => ?_) l
  · simp only [Fin.snoc_last]; exact continuous_const
  · simp only [Fin.snoc_castSucc]
    refine Fin.lastCases ?_ (fun m => ?_) l
    · simp only [Fin.snoc_last]; exact continuous_const
    · simp only [Fin.snoc_castSucc]
      exact (continuous_apply m).comp ((PiLp.continuous_ofLp 2 _).comp (continuous_apply r))

/-- C8 per-hyperplane comparison (fixed outside rows `b` and graph hyperplane `(c, t)`). -/
theorem vlev {k n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin (k + 3)))) (hW : finrank ℝ W = 2)
    (I : Finset (Fin n)) (hI : I.card = k + 3) (e : Fin (k + 3) ≃ I)
    (b : {i // i ∉ I} → EuclideanSpace ℝ (Fin (k + 3)))
    (μ : Fin n → EuclideanSpace ℝ (Fin (k + 3)) → ℝ) (hμ : ∀ i, IsDensity (μ i))
    (L τ R : ℝ) (hL : 0 < L) (hτ : 0 < τ) (hR : 0 ≤ R)
    (hLL : ∀ i, LogLipschitz (μ i) L) (hLV : ∀ i, LineVarianceGE (μ i) τ)
    (hLR : ((k + 3 : ℕ) : ℝ) / 3 ≤ L * R)
    (g M : (Fin n → EuclideanSpace ℝ (Fin (k + 3))) → ENNReal)
    (hgm : Measurable g) (hMm : Measurable M)
    (hg : ∀ a, g a ≠ 0 → edgeEvent W a I ∧ boundedDiamEvent W a I R ∧ G1det a ∧ G2det W a)
    (hg' : ∀ a, g a ≤ ENNReal.ofReal (Real.exp (-2) / (((k + 3 : ℕ) : ℝ) * L * (1 + R)) *
      (τ / (2 * Real.sqrt ((k + 3 : ℕ) : ℝ)))))
    (hM : ∀ a, edgeEvent W a I → edgeLen W a I ≤ M a)
    (w1 : EuclideanSpace ℝ (Fin (k + 3))) (hw1 : w1 ∈ W)
    (hgli : ∀ a, g a ≠ 0 → LinearIndependent ℝ
      (Fin.append ![w1] (fun j : Fin (k + 2) => a (e j.succ) - a (e 0))))
    (c : Fin (k + 2) → ℝ) (t : ℝ) :
    ∫⁻ Y : Fin (k + 3) → Fin (k + 2) → ℝ, ENNReal.ofReal |(FSC6.gmat Y).det| *
        ((∏ j, ENNReal.ofReal (μ (e j) (Pt c t (Y j)))) * g (join I e b (fun j => Pt c t (Y j)))) ≤
      ∫⁻ Y : Fin (k + 3) → Fin (k + 2) → ℝ, ENNReal.ofReal |(FSC6.gmat Y).det| *
        ((∏ j, ENNReal.ofReal (μ (e j) (Pt c t (Y j)))) * M (join I e b (fun j => Pt c t (Y j)))) := by
  classical
  have hμm : ∀ i, Measurable (μ i) := fun i => (FSLL.cont (hLL i)).measurable
  have hGm : ∀ F : (Fin n → EuclideanSpace ℝ (Fin (k + 3))) → ENNReal, Measurable F →
      Measurable fun rows : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 3)) =>
        (∏ j, ENNReal.ofReal (μ (e j) (rows j))) * F (join I e b rows) := by
    intro F hF
    refine Measurable.mul ?_ (hF.comp (measurable_join I e b))
    exact Finset.measurable_prod _ fun j _ =>
      ENNReal.measurable_ofReal.comp ((hμm _).comp (measurable_pi_apply j))
  by_cases hK : finrank ℝ ↥(LinearMap.range (Lc c) ⊓ W) = 1
  swap
  · have h0 : ∀ Y : Fin (k + 3) → Fin (k + 2) → ℝ, ENNReal.ofReal |(FSC6.gmat Y).det| *
        ((∏ j, ENNReal.ofReal (μ (e j) (Pt c t (Y j)))) *
          g (join I e b (fun j => Pt c t (Y j)))) = 0 := by
      intro Y
      by_cases hgz : g (join I e b (fun j => Pt c t (Y j))) = 0
      · rw [hgz]; simp
      exfalso; apply hK
      have hli := hgli _ hgz
      simp only [join_apply_e] at hli
      exact hK_of_li c t W hW w1 hw1 Y hli
    simp only [h0, lintegral_zero]; exact bot_le
  obtain ⟨o, ω, ι, K, -, -, hoW, hωW, hω, hιω, hWx, hPt, hint⟩ := FSPerV.per_v' c t W hW hK
  have hon : ∀ x (s : ℝ), phi c (o + ι x + s • ω) = t := by
    intro x s; obtain ⟨y, hy⟩ := hPt x s; rw [← hy, phi_Pt]
  rw [hint _ (hGm g hgm), hint _ (hGm M hMm)]
  refine mlm ?_ K
  have hPc : Continuous fun p : (Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1))) × (Fin (k + 3) → ℝ) =>
      (fun j => o + ι (p.1 j) + p.2 j • ω) := by
    refine continuous_pi fun j => ?_
    exact (continuous_const.add (ι.continuous.comp ((continuous_apply j).comp continuous_fst))).add
      (((continuous_apply j).comp continuous_snd).smul continuous_const)
  have hwc : Continuous fun p : (Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1))) × (Fin (k + 3) → ℝ) =>
      ENNReal.ofReal |∑ i, p.2 i * hcof p.1 i| := by
    refine ENNReal.continuous_ofReal.comp (continuous_abs.comp ?_)
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp continuous_snd).mul ((continuous_hcof i).comp continuous_fst)
  have hFm : ∀ F : (Fin n → EuclideanSpace ℝ (Fin (k + 3))) → ENNReal, Measurable F →
      Measurable fun p : (Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1))) × (Fin (k + 3) → ℝ) =>
        ENNReal.ofReal |∑ i, p.2 i * hcof p.1 i| *
          ((∏ j, ENNReal.ofReal (μ (e j) (o + ι (p.1 j) + p.2 j • ω))) *
            F (join I e b (fun j => o + ι (p.1 j) + p.2 j • ω))) :=
    fun F hF => hwc.measurable.mul ((hGm F hF).comp hPc.measurable)
  have hUm : Measurable fun p : EuclideanSpace ℝ (Fin (k + 1)) × (Fin (k + 2) → EuclideanSpace ℝ (Fin (k + 1))) =>
      (Fin.cons p.1 (fun j => p.1 + p.2 j) : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1))) := by
    refine measurable_pi_lambda _ fun j => ?_
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using measurable_fst
    · simp only [Fin.cons_succ]
      exact measurable_fst.add ((measurable_pi_apply j).comp measurable_snd)
  have step : ∀ F : (Fin n → EuclideanSpace ℝ (Fin (k + 3))) → ENNReal, Measurable F →
      ∫⁻ u : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 1)), ∫⁻ hh : Fin (k + 3) → ℝ,
        ENNReal.ofReal |∑ i, hh i * hcof u i| *
          ((∏ j, ENNReal.ofReal (μ (e j) (o + ι (u j) + hh j • ω))) *
            F (join I e b (fun j => o + ι (u j) + hh j • ω))) =
      ∫⁻ s' : Fin (k + 2) → EuclideanSpace ℝ (Fin (k + 1)), ∫⁻ x, ∫⁻ hh : Fin (k + 3) → ℝ,
        ENNReal.ofReal |∑ i, hh i * hcof (Ucons x s') i| *
          ((∏ j, ENNReal.ofReal (μ (e j) (o + ι (Ucons x s' j) + hh j • ω))) *
            F (join I e b (fun j => o + ι (Ucons x s' j) + hh j • ω))) := by
    intro F hF
    have hm1 := Measurable.lintegral_prod_right' (ν := (volume : Measure (Fin (k + 3) → ℝ))) (hFm F hF)
    rw [shift_shape _ hm1]
    refine lintegral_lintegral_swap ?_
    exact (hm1.comp hUm).aemeasurable
  rw [step g hgm, step M hMm]
  exact lintegral_mono fun s' => slice_cmp W hW o ω ι hoW hωW hω hιω hWx c t hon I hI e b μ hμ
    L τ R hL hτ hR hLL hLV hLR g M hg hg' hM s'

open FSL29 in
/-- `Pr[E_I] ≤ 2 Pr[E_I ∩ near]` (the proof of `FSL29.prob_le_two` with its measurable near-event). -/
theorem prob_le_two' {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (μ : Fin n → EuclideanSpace ℝ (Fin d) → ℝ) (hμ : ∀ i, IsDensity (μ i))
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (habar : ∀ i, ‖abar i‖ ≤ 1) (R : ℝ)
    (hR : ∀ i, CutoffRadiusLE (μ i) (abar i) (cutoffLevel n d) R)
    (I : Finset (Fin n)) (hI : I.card = d)
    (hB : ENNReal.ofReal (2 / (n.choose d : ℝ)) ≤ rowLaw μ {a | edgeEvent W a I}) :
    rowLaw μ {a | edgeEvent W a I} ≤
      rowLaw μ {a | edgeEvent W a I ∧ ∀ i ∈ I, ‖a i - abar i‖ < R} * 2 := by
  haveI : ∀ i, IsProbabilityMeasure (densityMeasure (μ i)) := fun i => dens_prob (hμ i)
  haveI : IsProbabilityMeasure (rowLaw μ) := by unfold rowLaw; infer_instance
  set p := rowLaw μ {a | edgeEvent W a I}
  set q := rowLaw μ {a | edgeEvent W a I ∧ ∀ i ∈ I, ‖a i - abar i‖ < R}
  have hsub : {a | edgeEvent W a I} ⊆ {a | edgeEvent W a I ∧ ∀ i ∈ I, ‖a i - abar i‖ < R} ∪
      ⋃ i ∈ I, {a | R ≤ ‖a i - abar i‖} := by
    intro a ha
    by_cases h : ∀ i ∈ I, ‖a i - abar i‖ < R
    · exact Or.inl ⟨ha, h⟩
    · push_neg at h
      obtain ⟨i, hi, hle⟩ := h
      exact Or.inr (Set.mem_biUnion hi hle)
  have hpq : p ≤ q + ENNReal.ofReal (1 / (n.choose d : ℝ)) :=
    (measure_mono hsub).trans ((measure_union_le _ _).trans
      (add_le_add le_rfl (bad_le hd hdn μ hμ abar R hR I hI)))
  have hhalf : ENNReal.ofReal (1 / (n.choose d : ℝ)) ≤ p / 2 := by
    have e : ENNReal.ofReal (1 / (n.choose d : ℝ)) = ENNReal.ofReal (2 / (n.choose d : ℝ)) / 2 := by
      rw [ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_inv_of_pos (by norm_num),
        ← ENNReal.ofReal_mul (by norm_num)]
      congr 1; ring
    rw [e]; exact ENNReal.div_le_div_right hB 2
  have hp_top : p / 2 ≠ ∞ := ENNReal.div_ne_top (measure_ne_top _ _) two_ne_zero
  have h2 : p / 2 + p / 2 ≤ q + p / 2 := by
    rw [ENNReal.add_halves]; exact hpq.trans (add_le_add le_rfl hhalf)
  have h3 : p / 2 ≤ q := ENNReal.le_of_add_le_add_right hp_top h2
  exact (ENNReal.div_le_iff_le_mul (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)).1 h3


lemma rows_cont {k : ℕ} : Continuous fun p : (Fin (k + 3) → Fin (k + 2) → ℝ) × (Fin (k + 3) → ℝ) =>
    (fun j => WithLp.toLp 2 (Fin.snoc (p.1 j) (p.2 j) : Fin (k + 3) → ℝ) :
      Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 3))) := by
  refine continuous_pi fun j => (PiLp.continuous_toLp 2 _).comp (continuous_pi fun l => ?_)
  refine Fin.lastCases ?_ (fun l => ?_) l
  · simp only [Fin.snoc_last]; exact (continuous_apply j).comp continuous_snd
  · simp only [Fin.snoc_castSucc]
    exact (continuous_apply l).comp ((continuous_apply j).comp continuous_fst)

lemma det_rows_cont {k : ℕ} : Continuous fun y : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 3)) =>
    (FSCV.gmat (fun r j => y r (Fin.castSucc j))).det := by
  refine Continuous.matrix_det (FSCV.gmat_continuous.comp ?_)
  refine continuous_pi fun r => continuous_pi fun j => ?_
  exact (continuous_apply _).comp ((PiLp.continuous_ofLp 2 _).comp (continuous_apply r))

/-- C8 chain: graph coordinates followed by the graph change of variables. -/
theorem chain {k : ℕ} (G : (Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 3))) → ENNReal)
    (hG : Measurable G)
    (h0 : ∀ y, (FSCV.gmat (fun r j => y r (Fin.castSucc j))).det = 0 → G y = 0) :
    ∫⁻ y, G y = ∫⁻ v : Fin (k + 3) → ℝ, ∫⁻ Y : Fin (k + 3) → Fin (k + 2) → ℝ,
      ENNReal.ofReal |(FSC6.gmat Y).det| * G (fun j => Pt (Fin.init v) (v (Fin.last _)) (Y j)) := by
  rw [FSGraph.graph_coords G hG]
  have hY : ∀ (Y : Fin (k + 3) → Fin (k + 2) → ℝ) (w : Fin (k + 3) → ℝ),
      (fun r j => WithLp.toLp 2 (Fin.snoc (Y r) (w r) : Fin (k + 3) → ℝ) (Fin.castSucc j) :
        Fin (k + 3) → Fin (k + 2) → ℝ) = Y := by
    intro Y w; funext r j; simp
  rw [FSCV.cv_graph (fun Y w => G (fun j => WithLp.toLp 2 (Fin.snoc (Y j) (w j) : Fin (k + 3) → ℝ)))
    (hG.comp rows_cont.measurable) (fun Y w hd => h0 _ (by rw [hY]; exact hd))]
  refine lintegral_congr fun v => lintegral_congr fun Y => ?_
  have hrow : (fun j => WithLp.toLp 2 (Fin.snoc (Y j) ((FSCV.gmat Y).mulVec v j) : Fin (k + 3) → ℝ)) =
      fun j => Pt (Fin.init v) (v (Fin.last _)) (Y j) := by
    funext j
    have hv : (FSCV.gmat Y).mulVec v j = ∑ i, Y j i * Fin.init v i + v (Fin.last _) := by
      conv_lhs => rw [← Fin.snoc_init_self v]
      exact FSCV.gmat_mulVec Y _ _ j
    rw [hv]; rfl
  simp only [hrow]
  rfl

/-- C8 core inequality: `c' · Pr[E ∩ near] ≤ E[len · 1_E]`. -/
theorem core_ineq {k n : ℕ} (hn : k + 3 ≤ n) (W : Submodule ℝ (EuclideanSpace ℝ (Fin (k + 3))))
    (hW : finrank ℝ W = 2)
    (μ : Fin n → EuclideanSpace ℝ (Fin (k + 3)) → ℝ) (hμ : ∀ i, IsDensity (μ i))
    (abar : Fin n → EuclideanSpace ℝ (Fin (k + 3))) (habar : ∀ i, ‖abar i‖ ≤ 1)
    (L τ R : ℝ) (hL : 0 < L) (hτ : 0 < τ) (hR : 0 ≤ R)
    (hLL : ∀ i, LogLipschitz (μ i) L) (hLV : ∀ i, LineVarianceGE (μ i) τ)
    (hLR : ((k + 3 : ℕ) : ℝ) / 3 ≤ L * R)
    (I : Finset (Fin n)) (hI : I.card = k + 3)
    (hlen : Measurable fun a => edgeLen W a I) :
    ENNReal.ofReal (Real.exp (-2) / (((k + 3 : ℕ) : ℝ) * L * (1 + R)) *
      (τ / (2 * Real.sqrt ((k + 3 : ℕ) : ℝ)))) *
        rowLaw μ {a | edgeEvent W a I ∧ ∀ i ∈ I, ‖a i - abar i‖ < R} ≤
      ∫⁻ a in {a | edgeEvent W a I}, edgeLen W a I ∂(rowLaw μ) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set c' := Real.exp (-2) / (((k + 3 : ℕ) : ℝ) * L * (1 + R)) *
      (τ / (2 * Real.sqrt ((k + 3 : ℕ) : ℝ))) with hc'
  have hμm : ∀ i, Measurable (μ i) := fun i => (FSLL.cont (hLL i)).measurable
  set e : Fin (k + 3) ≃ I := (I.orderIsoOfFin hI).toEquiv with he
  obtain ⟨w1, hw1W, hw1⟩ : ∃ w ∈ W, w ≠ 0 := by
    have : W ≠ ⊥ := by intro h; rw [h, finrank_bot] at hW; exact absurd hW (by norm_num)
    exact Submodule.exists_mem_ne_zero_of_ne_bot this
  set vl : EuclideanSpace ℝ (Fin (k + 3)) := EuclideanSpace.single (Fin.last (k + 2)) (1 : ℝ)
  have hvl : vl ≠ 0 := by
    intro h; have := congrArg (fun x : EuclideanSpace ℝ (Fin (k + 3)) => x (Fin.last (k + 2))) h
    simp [vl] at this
  have hs : Function.Injective (fun j : Fin (k + 2) => (e j.succ : Fin (m + 1))) :=
    fun i j h => Fin.succ_injective _ (e.injective (Subtype.ext h))
  have hupd : ∀ (j : Fin (k + 2)) (a : Fin (m + 1) → EuclideanSpace ℝ (Fin (k + 3))) x,
      Function.update a (e j.succ : Fin (m + 1)) x (e 0) = a (e 0) := by
    intro j a x
    refine Function.update_of_ne ?_ _ _
    intro h
    exact Fin.succ_ne_zero j (e.injective (Subtype.ext h)).symm
  have hli1 := FSGP.gen_li μ ![vl] (linearIndependent_unique_iff.2 (by simpa using hvl))
    (fun a => a (e 0)) (continuous_apply _) (k + 2) (fun j => (e j.succ : Fin (m + 1))) hs
    (by omega) hupd
  have hli2 := FSGP.gen_li μ ![w1] (linearIndependent_unique_iff.2 (by simpa using hw1))
    (fun a => a (e 0)) (continuous_apply _) (k + 2) (fun j => (e j.succ : Fin (m + 1))) hs
    (by omega) hupd
  have hgp := FSO1.gp_ae (d := k + 3) (by omega) (by omega) W hW μ
  set GP : Set (Fin (m + 1) → EuclideanSpace ℝ (Fin (k + 3))) := {a | (G1det a ∧ G2det W a) ∧
    LinearIndependent ℝ (Fin.append ![vl] (fun j : Fin (k + 2) => a (e j.succ) - a (e 0))) ∧
    LinearIndependent ℝ (Fin.append ![w1] (fun j : Fin (k + 2) => a (e j.succ) - a (e 0)))}
    with hGP
  have hGPae : ∀ᵐ a ∂rowLaw μ, a ∈ GP := by
    filter_upwards [hgp, hli1, hli2] with a h1 h2 h3
    exact ⟨h1, h2, h3⟩
  set T := (toMeasurable (rowLaw μ) GPᶜ)ᶜ with hT
  have hTm : MeasurableSet T := (measurableSet_toMeasurable _ _).compl
  have hTGP : T ⊆ GP := by
    intro a ha; by_contra h; exact ha (subset_toMeasurable _ _ h)
  have hT0 : rowLaw μ Tᶜ = 0 := by
    rw [hT, compl_compl, measure_toMeasurable]; exact ae_iff.1 hGPae
  set E := {a : Fin (m + 1) → EuclideanSpace ℝ (Fin (k + 3)) | edgeEvent W a I} with hE
  have hEm : MeasurableSet E := FSMeasE.meas_edgeEvent W I
  set Nr := {a : Fin (m + 1) → EuclideanSpace ℝ (Fin (k + 3)) | ∀ i ∈ I, ‖a i - abar i‖ < R}
    with hNr
  have hNrm : MeasurableSet Nr := by
    have : Nr = ⋂ i ∈ I, {a : Fin (m + 1) → EuclideanSpace ℝ (Fin (k + 3)) | ‖a i - abar i‖ < R} := by
      ext a; simp [hNr]
    rw [this]
    exact Finset.measurableSet_biInter I fun i _ =>
      measurableSet_lt ((measurable_pi_apply i).sub_const _).norm measurable_const
  set S := E ∩ Nr ∩ T with hS
  have hSm : MeasurableSet S := (hEm.inter hNrm).inter hTm
  set g := S.indicator (fun _ => ENNReal.ofReal c') with hgdef
  set M := E.indicator (fun a => edgeLen W a I) with hMdef
  have hgm : Measurable g := measurable_const.indicator hSm
  have hMm : Measurable M := hlen.indicator hEm
  -- left and right as integrals
  have hLeft : ENNReal.ofReal c' * rowLaw μ {a | edgeEvent W a I ∧ ∀ i ∈ I, ‖a i - abar i‖ < R} =
      ∫⁻ a, g a ∂rowLaw μ := by
    rw [hgdef, lintegral_indicator_const hSm]
    congr 1
    refine le_antisymm ?_ (measure_mono fun a ha => ⟨ha.1.1, ha.1.2⟩)
    calc rowLaw μ {a | edgeEvent W a I ∧ ∀ i ∈ I, ‖a i - abar i‖ < R}
        ≤ rowLaw μ (S ∪ Tᶜ) := measure_mono fun a ha => by
          by_cases h : a ∈ T
          · exact Or.inl ⟨⟨ha.1, ha.2⟩, h⟩
          · exact Or.inr h
      _ ≤ rowLaw μ S + rowLaw μ Tᶜ := measure_union_le _ _
      _ = rowLaw μ S := by rw [hT0, add_zero]
  have hRight : ∫⁻ a in {a | edgeEvent W a I}, edgeLen W a I ∂(rowLaw μ) = ∫⁻ a, M a ∂rowLaw μ := by
    rw [hMdef, lintegral_indicator hEm]
  rw [hLeft, hRight]
  -- facts about g
  have hgS : ∀ a, g a ≠ 0 → a ∈ S := by
    intro a ha; by_contra h; exact ha (Set.indicator_of_notMem h _)
  have hg : ∀ a, g a ≠ 0 → edgeEvent W a I ∧ boundedDiamEvent W a I R ∧ G1det a ∧ G2det W a := by
    intro a ha
    obtain ⟨⟨hE1, hN1⟩, hT1⟩ := hgS a ha
    exact ⟨hE1, FSL29.bdd_of_near W abar habar R I a hN1, (hTGP hT1).1.1, (hTGP hT1).1.2⟩
  have hg' : ∀ a, g a ≤ ENNReal.ofReal c' := by
    intro a; rw [hgdef]; unfold Set.indicator; split_ifs <;> simp
  have hM : ∀ a, edgeEvent W a I → edgeLen W a I ≤ M a := by
    intro a ha; rw [hMdef, Set.indicator_of_mem (show a ∈ E from ha)]
  have hgli : ∀ a, g a ≠ 0 → LinearIndependent ℝ
      (Fin.append ![w1] (fun j : Fin (k + 2) => a (e j.succ) - a (e 0))) :=
    fun a ha => (hTGP (hgS a ha).2).2.2
  have hgdet : ∀ b y, g (join I e b y) ≠ 0 →
      (FSCV.gmat (fun r j => y r (Fin.castSucc j))).det ≠ 0 := by
    intro b y hy
    have h1 := (hTGP (hgS _ hy).2).2.1
    simp only [join_apply_e] at h1
    exact FSCV.det_ne_of_li y h1
  -- the chain
  rw [FSSplit.split μ hμm I e g hgm, FSSplit.split μ hμm I e M hMm]
  refine lintegral_mono fun b => ?_
  have hGm : ∀ F : (Fin (m + 1) → EuclideanSpace ℝ (Fin (k + 3))) → ENNReal, Measurable F →
      Measurable fun rows : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 3)) =>
        (∏ j, ENNReal.ofReal (μ (e j) (rows j))) * F (join I e b rows) := by
    intro F hF
    refine Measurable.mul ?_ (hF.comp (measurable_join I e b))
    exact Finset.measurable_prod _ fun j _ =>
      ENNReal.measurable_ofReal.comp ((hμm _).comp (measurable_pi_apply j))
  set D0 := {y : Fin (k + 3) → EuclideanSpace ℝ (Fin (k + 3)) |
    (FSCV.gmat (fun r j => y r (Fin.castSucc j))).det ≠ 0} with hD0
  have hD0m : MeasurableSet D0 :=
    (measurableSet_singleton (0 : ℝ)).compl.preimage det_rows_cont.measurable
  have hchain1 := chain (fun rows => (∏ j, ENNReal.ofReal (μ (e j) (rows j))) * g (join I e b rows))
    (hGm g hgm) (fun y hy => by
      by_cases hgz : g (join I e b y) = 0
      · rw [hgz, mul_zero]
      · exact absurd hy (hgdet b y hgz))
  have hchain2 := chain (D0.indicator fun rows =>
      (∏ j, ENNReal.ofReal (μ (e j) (rows j))) * M (join I e b rows))
    ((hGm M hMm).indicator hD0m) (fun y hy => Set.indicator_of_notMem (by simpa [hD0] using hy) _)
  calc ∫⁻ y, (∏ j, ENNReal.ofReal (μ (e j) (y j))) * g (join I e b y) = _ := hchain1
    _ ≤ ∫⁻ v : Fin (k + 3) → ℝ, ∫⁻ Y : Fin (k + 3) → Fin (k + 2) → ℝ,
        ENNReal.ofReal |(FSC6.gmat Y).det| *
          ((∏ j, ENNReal.ofReal (μ (e j) (Pt (Fin.init v) (v (Fin.last _)) (Y j)))) *
            M (join I e b (fun j => Pt (Fin.init v) (v (Fin.last _)) (Y j)))) :=
        lintegral_mono fun v => vlev W hW I hI e b μ hμ L τ R hL hτ hR hLL hLV hLR g M hgm hMm
          hg hg' hM w1 hw1W hgli (Fin.init v) (v (Fin.last _))
    _ = ∫⁻ v : Fin (k + 3) → ℝ, ∫⁻ Y : Fin (k + 3) → Fin (k + 2) → ℝ,
        ENNReal.ofReal |(FSC6.gmat Y).det| * D0.indicator (fun rows =>
          (∏ j, ENNReal.ofReal (μ (e j) (rows j))) * M (join I e b rows))
          (fun j => Pt (Fin.init v) (v (Fin.last _)) (Y j)) := by
        refine lintegral_congr fun v => lintegral_congr fun Y => ?_
        have hYY : (fun r j => Pt (Fin.init v) (v (Fin.last _)) (Y r) (Fin.castSucc j) :
            Fin (k + 3) → Fin (k + 2) → ℝ) = Y := by
          funext r j; simp [Pt]
        by_cases hd : (FSC6.gmat Y).det = 0
        · rw [hd]; simp
        · rw [Set.indicator_of_mem]
          show (FSCV.gmat (fun r j => Pt (Fin.init v) (v (Fin.last _)) (Y r) (Fin.castSucc j))).det ≠ 0
          rw [hYY]; exact hd
    _ = ∫⁻ y, D0.indicator (fun rows =>
          (∏ j, ENNReal.ofReal (μ (e j) (rows j))) * M (join I e b rows)) y := hchain2.symm
    _ ≤ ∫⁻ y, (∏ j, ENNReal.ofReal (μ (e j) (y j))) * M (join I e b y) :=
        lintegral_mono fun y => Set.indicator_le_self _ _ y

/-- edge_length_bound (eq. (18)), given measurability of the edge length. -/
theorem elb_of_meas {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hW : Module.finrank ℝ W = 2)
    (μ : Fin n → EuclideanSpace ℝ (Fin d) → ℝ) (hμ : ∀ i, IsDensity (μ i))
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (hmean : ∀ i, HasMean (μ i) (abar i))
    (habar : ∀ i, ‖abar i‖ ≤ 1) (L τ R : ℝ) (hL : 0 < L) (hτ : 0 < τ) (hR : 0 ≤ R)
    (hLL : ∀ i, LogLipschitz (μ i) L) (hLV : ∀ i, LineVarianceGE (μ i) τ)
    (hCR : ∀ i, CutoffRadiusLE (μ i) (abar i) (cutoffLevel n d) R)
    (I : Finset (Fin n)) (hI : I.card = d)
    (hB : ENNReal.ofReal (2 / (n.choose d : ℝ)) ≤ rowLaw μ {a | edgeEvent W a I})
    (hlen : Measurable fun a => edgeLen W a I) :
    ENNReal.ofReal ((1 / 2) * (Real.exp (-2) / ((d : ℝ) * L * (1 + R))) *
        (τ / (2 * Real.sqrt d))) * rowLaw μ {a | edgeEvent W a I} ≤
      ∫⁻ a in {a | edgeEvent W a I}, edgeLen W a I ∂(rowLaw μ) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 3 := ⟨d - 3, by omega⟩
  have hn0 : 0 < n := by omega
  have hlev : cutoffLevel n (k + 3) ≤ 1 / 2 := by
    unfold cutoffLevel
    have hc : (1 : ℝ) ≤ (n.choose (k + 3) : ℝ) := by exact_mod_cast Nat.choose_pos hdn
    have hk : (3 : ℝ) ≤ ((k + 3 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ k + 3)
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hLR : ((k + 3 : ℕ) : ℝ) / 3 ≤ L * R := by
    let i0 : Fin n := ⟨0, hn0⟩
    have hcut : CutoffRadiusLE (μ i0) (abar i0) (1 / 2) R :=
      le_trans (hCR i0) (ENNReal.ofReal_le_ofReal hlev)
    exact FSL21_solution (by omega) (μ i0) (hμ i0) (abar i0) (hmean i0) L (hLL i0) R hcut
  have h2 := prob_le_two' (by omega) hdn W μ hμ abar habar R hCR I hI hB
  have hc := core_ineq hdn W hW μ hμ abar habar L τ R hL hτ hR hLL hLV hLR I hI hlen
  have hH : 0 ≤ (1 / 2) * (Real.exp (-2) / (((k + 3 : ℕ) : ℝ) * L * (1 + R))) *
      (τ / (2 * Real.sqrt ((k + 3 : ℕ) : ℝ))) := by positivity
  calc ENNReal.ofReal ((1 / 2) * (Real.exp (-2) / (((k + 3 : ℕ) : ℝ) * L * (1 + R))) *
        (τ / (2 * Real.sqrt ((k + 3 : ℕ) : ℝ)))) * rowLaw μ {a | edgeEvent W a I}
      ≤ ENNReal.ofReal ((1 / 2) * (Real.exp (-2) / (((k + 3 : ℕ) : ℝ) * L * (1 + R))) *
        (τ / (2 * Real.sqrt ((k + 3 : ℕ) : ℝ)))) *
          (rowLaw μ {a | edgeEvent W a I ∧ ∀ i ∈ I, ‖a i - abar i‖ < R} * 2) := mlm h2 _
    _ = ENNReal.ofReal ((1 / 2) * (Real.exp (-2) / (((k + 3 : ℕ) : ℝ) * L * (1 + R))) *
        (τ / (2 * Real.sqrt ((k + 3 : ℕ) : ℝ))) * 2) *
          rowLaw μ {a | edgeEvent W a I ∧ ∀ i ∈ I, ‖a i - abar i‖ < R} := by
        rw [ENNReal.ofReal_mul hH, ENNReal.ofReal_ofNat]; ring
    _ = ENNReal.ofReal (Real.exp (-2) / (((k + 3 : ℕ) : ℝ) * L * (1 + R)) *
        (τ / (2 * Real.sqrt ((k + 3 : ℕ) : ℝ)))) *
          rowLaw μ {a | edgeEvent W a I ∧ ∀ i ∈ I, ‖a i - abar i‖ < R} := by
        congr 2; ring
    _ ≤ _ := hc

end FSC8

-- ===== edgeLen measurability (relay 12) =====
namespace FSELM
open FriendlyShadow.Gaussian MeasureTheory
open scoped ENNReal

/-- barycentric combination of the rows indexed by `I`. -/
noncomputable def comb {d n : ℕ} (I : Finset (Fin n)) (a : Fin n → EuclideanSpace ℝ (Fin d))
    (l : I → ℝ) : EuclideanSpace ℝ (Fin d) := ∑ j, l j • a j

lemma comb_cont {d n : ℕ} (I : Finset (Fin n)) :
    Continuous fun q : (Fin n → EuclideanSpace ℝ (Fin d)) × (I → ℝ) => comb I q.1 q.2 := by
  unfold comb
  refine continuous_finset_sum _ fun j _ => ?_
  exact ((continuous_apply j).comp continuous_snd).smul ((continuous_apply (j : Fin n)).comp continuous_fst)

lemma mem_K {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (I : Finset (Fin n)) (x : EuclideanSpace ℝ (Fin d)) :
    x ∈ convexHull ℝ (a '' (I : Set (Fin n))) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) ↔
      ∃ l : stdSimplex ℝ I, comb I a l = x ∧ x ∈ W := by
  have himg : a '' (I : Set (Fin n)) = Set.range (fun j : I => a j) := by
    ext y; constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨j, rfl⟩; exact ⟨j, j.2, rfl⟩
  rw [himg, Set.mem_inter_iff, C5747Meas.mem_hull_range_iff']
  constructor
  · rintro ⟨⟨l, h0, h1, h⟩, hW⟩; exact ⟨⟨l, h0, h1⟩, h, hW⟩
  · rintro ⟨l, h, hW⟩; exact ⟨⟨l.1, l.2.1, l.2.2, h⟩, hW⟩

/-- the closed set of `a` admitting two hull points in `W` at distance at least `y'`. -/
lemma isClosed_A {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (I : Finset (Fin n)) (y' : ℝ≥0∞) :
    IsClosed {a : Fin n → EuclideanSpace ℝ (Fin d) | ∃ p : stdSimplex ℝ I × stdSimplex ℝ I,
      comb I a p.1 ∈ W ∧ comb I a p.2 ∈ W ∧ y' ≤ edist (comb I a p.1) (comb I a p.2)} := by
  have hWc : IsClosed (W : Set (EuclideanSpace ℝ (Fin d))) := W.closed_of_finiteDimensional
  have c1 : Continuous fun q : (Fin n → EuclideanSpace ℝ (Fin d)) × (stdSimplex ℝ I × stdSimplex ℝ I) =>
      comb I q.1 q.2.1 :=
    (comb_cont I).comp (continuous_fst.prodMk (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)))
  have c2 : Continuous fun q : (Fin n → EuclideanSpace ℝ (Fin d)) × (stdSimplex ℝ I × stdSimplex ℝ I) =>
      comb I q.1 q.2.2 :=
    (comb_cont I).comp (continuous_fst.prodMk (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))
  have hC : IsClosed {q : (Fin n → EuclideanSpace ℝ (Fin d)) × (stdSimplex ℝ I × stdSimplex ℝ I) |
      comb I q.1 q.2.1 ∈ W ∧ comb I q.1 q.2.2 ∈ W ∧ y' ≤ edist (comb I q.1 q.2.1) (comb I q.1 q.2.2)} :=
    (hWc.preimage c1).inter ((hWc.preimage c2).inter (isClosed_le continuous_const (c1.edist c2)))
  have := isClosedMap_fst_of_compactSpace _ hC
  convert this using 1
  ext a; constructor
  · rintro ⟨p, h⟩; exact ⟨(a, p), h, rfl⟩
  · rintro ⟨⟨a', p⟩, h, rfl⟩; exact ⟨p, h⟩

theorem meas_edgeLen {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (I : Finset (Fin n)) :
    Measurable fun a : Fin n → EuclideanSpace ℝ (Fin d) => edgeLen W a I := by
  have hset : ∀ y : ℝ≥0∞, {a : Fin n → EuclideanSpace ℝ (Fin d) | y ≤ edgeLen W a I} =
      ⋂ y' ∈ Set.Iio y, {a : Fin n → EuclideanSpace ℝ (Fin d) | ∃ p : stdSimplex ℝ I × stdSimplex ℝ I,
        comb I a p.1 ∈ W ∧ comb I a p.2 ∈ W ∧ y' ≤ edist (comb I a p.1) (comb I a p.2)} := by
    intro y
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_Iio]
    constructor
    · intro hy y' hy'
      by_contra hne
      push_neg at hne
      have : edgeLen W a I ≤ y' := by
        unfold edgeLen
        refine Metric.ediam_le fun x hx z hz => ?_
        obtain ⟨l, hl, hxW⟩ := (mem_K W a I x).1 hx
        obtain ⟨l', hl', hzW⟩ := (mem_K W a I z).1 hz
        subst hl hl'
        exact (hne (l, l') hxW hzW).le
      exact absurd (hy.trans this) (not_le.2 hy')
    · intro h
      refine le_of_forall_lt_imp_le_of_dense fun y' hy' => ?_
      obtain ⟨p, h1, h2, h3⟩ := h y' hy'
      refine h3.trans ?_
      unfold edgeLen
      exact Metric.edist_le_ediam_of_mem ((mem_K W a I _).2 ⟨p.1, rfl, h1⟩)
        ((mem_K W a I _).2 ⟨p.2, rfl, h2⟩)
  have husc : UpperSemicontinuous fun a : Fin n → EuclideanSpace ℝ (Fin d) => edgeLen W a I := by
    rw [upperSemicontinuous_iff_isClosed_preimage]
    intro y
    have : (fun a : Fin n → EuclideanSpace ℝ (Fin d) => edgeLen W a I) ⁻¹' Set.Ici y =
        {a | y ≤ edgeLen W a I} := rfl
    rw [this, hset y]
    exact isClosed_biInter fun y' _ => isClosed_A W I y'
  exact husc.measurable

end FSELM

-- ===== Meas2 extension: C5747Geom + rest of C5747Cnt (relay 12) =====
section MeasExt
open MeasureTheory
open scoped RealInnerProductSpace ENNReal
namespace C5747Geom

lemma mem_hull_range_iff {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (p : ι → E) (y : E) :
    y ∈ convexHull ℝ (Set.range p) ↔
      ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ ∑ i, μ i = 1 ∧ ∑ i, μ i • p i = y := by
  constructor
  · intro hy
    have hsub : convexHull ℝ (Set.range p) ⊆
        {y | ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ ∑ i, μ i = 1 ∧ ∑ i, μ i • p i = y} := by
      apply convexHull_min
      · rintro _ ⟨j, rfl⟩
        refine ⟨Pi.single j 1, ?_, ?_, ?_⟩
        · intro i
          by_cases h : i = j
          · subst h; simp
          · simp [h]
        · simp
        · simp [Pi.single_apply]
      · rintro _ ⟨μ, hμ0, hμ1, rfl⟩ _ ⟨ν, hν0, hν1, rfl⟩ s t hs ht hst
        refine ⟨fun i => s * μ i + t * ν i, fun i => ?_, ?_, ?_⟩
        · have := hμ0 i; have := hν0 i; positivity
        · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hμ1, hν1, hst]
        · simp [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
    exact hsub hy
  · rintro ⟨μ, h0, h1, rfl⟩
    exact mem_convexHull_of_exists_fintype μ p h0 h1 (fun i => Set.mem_range_self i) rfl

/-- Core: a positive convex representation of a point of an extreme set `e` forces the whole
sub-hull (intersected with `W`) into `e`. -/
lemma core_sub {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {K e : Set E} (he : IsExtreme ℝ K e) (W : Submodule ℝ E) (p : ι → E)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (hme : ∑ i, w i • p i ∈ e)
    (hK : convexHull ℝ (Set.range p) ∩ (W : Set E) ⊆ K) (hmW : ∑ i, w i • p i ∈ W) :
    convexHull ℝ (Set.range p) ∩ (W : Set E) ⊆ e := by
  rintro y ⟨hy, hyW⟩
  by_cases hym : y = ∑ i, w i • p i
  · rw [hym]; exact hme
  obtain ⟨μ, hμ0, hμ1, hμy⟩ := (mem_hull_range_iff p y).1 hy
  have hne : (Finset.univ : Finset ι).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [h] at hw1
  set ε := Finset.univ.inf' hne w with hεdef
  have hε : 0 < ε := (Finset.lt_inf'_iff hne).2 (fun i _ => hw i)
  have hεw : ∀ i, ε ≤ w i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  have hμ1' : ∀ i, μ i ≤ 1 := fun i => by
    calc μ i ≤ ∑ j, μ j := Finset.single_le_sum (fun j _ => hμ0 j) (Finset.mem_univ i)
    _ = 1 := hμ1
  set z := ∑ i, ((1 + ε) * w i - ε * μ i) • p i with hzdef
  have hz : z ∈ convexHull ℝ (Set.range p) := by
    refine (mem_hull_range_iff p z).2 ⟨_, fun i => ?_, ?_, rfl⟩
    · nlinarith [hεw i, hμ1' i, hμ0 i, hw i]
    · rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hw1, hμ1]; ring
  have hzeq : z = (1 + ε) • (∑ i, w i • p i) - ε • y := by
    rw [hzdef, ← hμy]
    simp [sub_smul, mul_smul, Finset.smul_sum, Finset.sum_sub_distrib]
  have hzW : z ∈ W := by
    rw [hzeq]; exact W.sub_mem (W.smul_mem _ hmW) (W.smul_mem _ hyW)
  have h1 : (1 + ε) ≠ 0 := by positivity
  have hmseg : (∑ i, w i • p i) ∈ openSegment ℝ z y := by
    refine ⟨1 / (1 + ε), ε / (1 + ε), by positivity, by positivity, by field_simp, ?_⟩
    rw [hzeq, smul_sub, smul_smul, smul_smul, one_div, inv_mul_cancel₀ h1, one_smul,
      div_eq_inv_mul]
    abel
  exact he.right_mem_of_mem_openSegment (hK ⟨hz, hzW⟩) (hK ⟨hy, hyW⟩) hme hmseg

lemma midpoint_mem_openSegment' {E : Type*} [AddCommGroup E] [Module ℝ E] (u v : E) :
    midpoint ℝ u v ∈ openSegment ℝ u v := by
  refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
  rw [midpoint_eq_smul_add, smul_add, invOf_eq_inv, one_div]

/-- An edge whose midpoint lies in an extreme segment lies in it. -/
lemma seg_sub_of_mid {E : Type*} [AddCommGroup E] [Module ℝ E] {K : Set E} {u v u' v' : E}
    (h : Hirsch.Adj K u v) (h' : Hirsch.Adj K u' v')
    (hm : midpoint ℝ u v ∈ segment ℝ u' v') : segment ℝ u v ⊆ segment ℝ u' v' := by
  have hu : u ∈ K := h.2.1 (left_mem_segment ℝ u v)
  have hv : v ∈ K := h.2.1 (right_mem_segment ℝ u v)
  have hu' := h'.2.left_mem_of_mem_openSegment hu hv hm (midpoint_mem_openSegment' u v)
  have hv' := h'.2.right_mem_of_mem_openSegment hu hv hm (midpoint_mem_openSegment' u v)
  exact (convex_segment u' v').segment_subset hu' hv'

lemma seg_eq_of_common {E : Type*} [AddCommGroup E] [Module ℝ E] {K C : Set E} {u v u' v' : E}
    (h : Hirsch.Adj K u v) (h' : Hirsch.Adj K u' v')
    (hC : C ⊆ segment ℝ u v) (hC' : C ⊆ segment ℝ u' v')
    (hm : midpoint ℝ u v ∈ C) (hm' : midpoint ℝ u' v' ∈ C) :
    segment ℝ u v = segment ℝ u' v' :=
  le_antisymm (seg_sub_of_mid h h' (hC' hm)) (seg_sub_of_mid h' h (hC hm'))

open FriendlyShadow.Gaussian

variable {d n : ℕ}

/-- The witness predicate: the edge `e` with endpoints `u v` is pinned by the point set `t`. -/
def Pin (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (a : Fin n → EuclideanSpace ℝ (Fin d))
    (e : Set (EuclideanSpace ℝ (Fin d))) (t : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ u v, Hirsch.Adj (polygon W a) u v ∧ e = segment ℝ u v ∧
    convexHull ℝ (t : Set _) ∩ (W : Set _) ⊆ e ∧
    midpoint ℝ u v ∈ convexHull ℝ (t : Set _) ∩ (W : Set _)

lemma pin_inj (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (a : Fin n → EuclideanSpace ℝ (Fin d))
    {e₁ e₂ : Set (EuclideanSpace ℝ (Fin d))} {t : Finset (EuclideanSpace ℝ (Fin d))}
    (h₁ : Pin W a e₁ t) (h₂ : Pin W a e₂ t) : e₁ = e₂ := by
  obtain ⟨u, v, hA, rfl, hC, hm⟩ := h₁
  obtain ⟨u', v', hA', rfl, hC', hm'⟩ := h₂
  exact seg_eq_of_common hA hA' hC hC' hm hm'

set_option maxHeartbeats 1000000 in
lemma pin_exists (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) {e : Set (EuclideanSpace ℝ (Fin d))}
    (he : e ∈ edges (polygon W a)) :
    ∃ t : Finset (EuclideanSpace ℝ (Fin d)), t ⊆ Finset.univ.image a ∧ t.card ≤ d + 1 ∧
      Pin W a e t := by
  classical
  obtain ⟨u, v, hA, rfl⟩ := he
  have hu : u ∈ polygon W a := hA.2.1 (left_mem_segment ℝ u v)
  have hv : v ∈ polygon W a := hA.2.1 (right_mem_segment ℝ u v)
  have hmK : midpoint ℝ u v ∈ polygon W a :=
    (convex_convexHull ℝ _).inter W.convex |>.segment_subset hu hv
      (by rw [segment_eq_image_lineMap]; exact ⟨1/2, by norm_num, by
        rw [midpoint, AffineMap.lineMap_apply, AffineMap.lineMap_apply]; norm_num⟩)
  obtain ⟨ι, _, z, w, hz, hzi, hw0, hw1, hwm⟩ := eq_pos_convex_span_of_mem_convexHull hmK.1
  refine ⟨Finset.univ.image z, ?_, ?_, u, v, hA, rfl, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨j, hj⟩ := hz ⟨i, rfl⟩
    exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, hj⟩
  · calc (Finset.univ.image z).card ≤ Fintype.card ι := Finset.card_image_le.trans (by simp)
      _ ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range z)) + 1 := hzi.card_le_finrank_succ
      _ ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) + 1 :=
          Nat.add_le_add_right (Submodule.finrank_le _) 1
      _ = d + 1 := by simp
  · have hco : ((Finset.univ.image z : Finset _) : Set (EuclideanSpace ℝ (Fin d))) = Set.range z := by
      simp
    rw [hco]
    refine core_sub hA.2 W z w hw0 hw1 ?_ ?_ ?_
    · rw [hwm]
      rw [segment_eq_image_lineMap]
      exact ⟨1/2, by norm_num, by
        rw [midpoint, AffineMap.lineMap_apply, AffineMap.lineMap_apply]; norm_num⟩
    · rintro x ⟨hx, hxW⟩
      exact ⟨convexHull_mono hz hx, hxW⟩
    · rw [hwm]; exact hmK.2
  · have hco : ((Finset.univ.image z : Finset _) : Set (EuclideanSpace ℝ (Fin d))) = Set.range z := by
      simp
    rw [hco]
    refine ⟨?_, hmK.2⟩
    rw [← hwm]
    exact mem_convexHull_of_exists_fintype w z (fun i => (hw0 i).le) hw1
      (fun i => Set.mem_range_self i) rfl

lemma card_small_subsets {α : Type*} [DecidableEq α] (U : Finset α) (D : ℕ) :
    (U.powerset.filter (fun t => t.card ≤ D)).card ≤ (D + 1) * (U.card + 1) ^ D := by
  have hsub : U.powerset.filter (fun t => t.card ≤ D) ⊆
      (Finset.range (D + 1)).biUnion (fun k => U.powersetCard k) := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_powerset] at ht
    rw [Finset.mem_biUnion]
    exact ⟨t.card, Finset.mem_range.2 (Nat.lt_succ_of_le ht.2),
      Finset.mem_powersetCard.2 ⟨ht.1, rfl⟩⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.range (D + 1), (U.powersetCard k).card := Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range (D + 1), (U.card + 1) ^ D := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.card_powersetCard]
        calc U.card.choose k ≤ U.card ^ k := Nat.choose_le_pow _ _
          _ ≤ (U.card + 1) ^ k := Nat.pow_le_pow_left (Nat.le_succ _) _
          _ ≤ (U.card + 1) ^ D :=
              Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
    _ = (D + 1) * (U.card + 1) ^ D := by simp

set_option maxHeartbeats 1000000 in
/-- Deterministic edge bound. -/
theorem edgeCount_le (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) :
    edgeCount (polygon W a) ≤ (d + 2) * (n + 1) ^ (d + 1) := by
  classical
  set U : Finset (EuclideanSpace ℝ (Fin d)) := Finset.univ.image a
  set T : Finset (Finset (EuclideanSpace ℝ (Fin d))) := U.powerset.filter (fun t => t.card ≤ d + 1)
  let f : Set (EuclideanSpace ℝ (Fin d)) → Finset (EuclideanSpace ℝ (Fin d)) := fun e =>
    if h : ∃ t : Finset (EuclideanSpace ℝ (Fin d)), t ⊆ U ∧ t.card ≤ d + 1 ∧ Pin W a e t
    then h.choose else ∅
  have hf : ∀ e ∈ edges (polygon W a), f e ⊆ U ∧ (f e).card ≤ d + 1 ∧ Pin W a e (f e) := by
    intro e he
    have h : ∃ t : Finset (EuclideanSpace ℝ (Fin d)), t ⊆ U ∧ t.card ≤ d + 1 ∧ Pin W a e t :=
      pin_exists W a he
    have hfe : f e = h.choose := dif_pos h
    rw [hfe]
    exact h.choose_spec
  have h1 : edgeCount (polygon W a) ≤ (T : Set (Finset (EuclideanSpace ℝ (Fin d)))).ncard := by
    unfold edgeCount
    refine Set.ncard_le_ncard_of_injOn f ?_ ?_ (Finset.finite_toSet T)
    · intro e he
      obtain ⟨h1, h2, -⟩ := hf e he
      simp [T, Finset.mem_powerset, h1, h2]
    · intro e₁ he₁ e₂ he₂ heq
      have p1 := (hf e₁ he₁).2.2
      have p2 := (hf e₂ he₂).2.2
      rw [heq] at p1
      exact pin_inj W a p1 p2
  rw [Set.ncard_coe_finset] at h1
  have hU : U.card ≤ n := Finset.card_image_le.trans (by simp)
  calc edgeCount (polygon W a) ≤ T.card := h1
    _ ≤ (d + 1 + 1) * (U.card + 1) ^ (d + 1) := card_small_subsets U (d + 1)
    _ ≤ (d + 2) * (n + 1) ^ (d + 1) :=
        Nat.mul_le_mul (le_refl _) (Nat.pow_le_pow_left (Nat.succ_le_succ hU) _)

end C5747Geom

namespace C5747Cnt2

open FriendlyShadow.Gaussian C5747Meas C5747Geom C5747Cnt

variable {d n : ℕ}

noncomputable def rk (S : Finset (Fin n)) : ℕ := (Fintype.equivFin (Finset (Fin n)) S : ℕ)

lemma rk_inj {S S' : Finset (Fin n)} (h : rk S = rk S') : S = S' :=
  (Fintype.equivFin (Finset (Fin n))).injective (Fin.ext h)

/-- Oriented edges `(a, u, v)` minimally pinned by `S`. -/
def BS (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (S : Finset (Fin n)) :
    Set ((Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  {b | Hirsch.Adj (polygon W b.1) b.2.1 b.2.2 ∧ RS W S b ∧
    (∀ S' : Finset (Fin n), rk S' < rk S → ¬ RS W S' b) ∧ lexLt b.2.1 b.2.2}

lemma meas_BS (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (S : Finset (Fin n)) :
    MeasurableSet (BS W S) := by
  classical
  have hmin : MeasurableSet {b : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d) | ∀ S' : Finset (Fin n), rk S' < rk S → ¬ RS W S' b} := by
    have : {b : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
        EuclideanSpace ℝ (Fin d) | ∀ S' : Finset (Fin n), rk S' < rk S → ¬ RS W S' b} =
        ⋂ S' ∈ (Finset.univ.filter (fun S' : Finset (Fin n) => rk S' < rk S)),
          {b | RS W S' b}ᶜ := by
      ext b; simp
    rw [this]
    exact Finset.measurableSet_biInter _ (fun S' _ => (meas_RS W S').compl)
  exact (meas_Adj W).inter ((meas_RS W S).inter (hmin.inter meas_lex))

lemma injOn_BS (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (S : Finset (Fin n)) :
    Set.InjOn Prod.fst (BS W S) := by
  rintro ⟨a, u, v⟩ ⟨hA, hR, -, hL⟩ ⟨a', u', v'⟩ ⟨hA', hR', -, hL'⟩ hfst
  simp only at hfst
  subst hfst
  have hseg := seg_eq_of_common hA hA' hR.1 hR'.1 hR.2 hR'.2
  rcases seg_ends hA.1 hseg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact absurd hL' (lex_asymm hL)

lemma meas_G (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (S : Finset (Fin n)) :
    MeasurableSet (Prod.fst '' BS W S) :=
  (meas_BS W S).image_of_continuousOn_injOn continuous_fst.continuousOn (injOn_BS W S)

lemma RS_swap (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (S : Finset (Fin n))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (u v : EuclideanSpace ℝ (Fin d)) :
    RS W S (a, u, v) ↔ RS W S (a, v, u) := by
  simp only [RS, segment_symm ℝ u v, midpoint_comm u v]

open Classical in
lemma edgeCount_eq (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (a : Fin n → EuclideanSpace ℝ (Fin d)) :
    edgeCount (polygon W a) =
      (Finset.univ.filter (fun S : Finset (Fin n) => a ∈ Prod.fst '' BS W S)).card := by
  obtain ⟨F, hF⟩ : ∃ F : Finset (Finset (Fin n)),
      F = Finset.univ.filter (fun S : Finset (Fin n) => a ∈ Prod.fst '' BS W S) := ⟨_, rfl⟩
  rw [← hF]
  have hFmem : ∀ S, S ∈ (F : Set (Finset (Fin n))) ↔ a ∈ Prod.fst '' BS W S := by
    intro S; rw [Finset.mem_coe, hF]; simp
  let g : Finset (Fin n) → Set (EuclideanSpace ℝ (Fin d)) := fun S =>
    if h : a ∈ Prod.fst '' BS W S then segment ℝ h.choose.2.1 h.choose.2.2 else ∅
  have hgb : ∀ S b, b ∈ BS W S → b.1 = a → g S = segment ℝ b.2.1 b.2.2 := by
    intro S b hb hba
    have h : a ∈ Prod.fst '' BS W S := ⟨b, hb, hba⟩
    have h1 : g S = segment ℝ h.choose.2.1 h.choose.2.2 := dif_pos h
    rw [h1, injOn_BS W S h.choose_spec.1 hb (h.choose_spec.2.trans hba.symm)]
  have hinj : Set.InjOn g (F : Set (Finset (Fin n))) := by
    intro S1 hS1 S2 hS2 heq
    obtain ⟨b1, hb1, hb1a⟩ := (hFmem S1).1 hS1
    obtain ⟨b2, hb2, hb2a⟩ := (hFmem S2).1 hS2
    rw [hgb S1 b1 hb1 hb1a, hgb S2 b2 hb2 hb2a] at heq
    have hb : b1 = b2 := by
      rcases seg_ends hb1.1.1 heq with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Prod.ext (hb1a.trans hb2a.symm) (Prod.ext e1.symm e2.symm)
      · exfalso
        have h4 := hb2.2.2.2
        rw [e1, e2] at h4
        exact lex_asymm hb1.2.2.2 h4
    subst hb
    rcases lt_trichotomy (rk S1) (rk S2) with hlt | heq' | hgt
    · exact absurd hb1.2.1 (hb2.2.2.1 S1 hlt)
    · exact rk_inj heq'
    · exact absurd hb2.2.1 (hb1.2.2.1 S2 hgt)
  have himg : g '' (F : Set (Finset (Fin n))) = edges (polygon W a) := by
    ext e; constructor
    · rintro ⟨S, hS, rfl⟩
      obtain ⟨b, hb, hba⟩ := (hFmem S).1 hS
      rw [hgb S b hb hba]
      exact ⟨b.2.1, b.2.2, hba ▸ hb.1, rfl⟩
    · intro he
      obtain ⟨t, ht, -, u, v, hA, rfl, hsub, hmid⟩ := pin_exists W a he
      let S0 : Finset (Fin n) := Finset.univ.filter (fun i => a i ∈ t)
      have hrange : Set.range (fun i : S0 => a i) = (t : Set (EuclideanSpace ℝ (Fin d))) := by
        ext x; constructor
        · rintro ⟨⟨i, hi⟩, rfl⟩; exact (Finset.mem_filter.1 hi).2
        · intro hx
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (ht hx)
          exact ⟨⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩⟩, rfl⟩
      have hV : VS W S0 a = convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin d))) ∩
          (W : Set (EuclideanSpace ℝ (Fin d))) := by
        rw [VS, hrange]
      have hex : ∃ k, ∃ S : Finset (Fin n), rk S = k ∧ ∃ u' v', Hirsch.Adj (polygon W a) u' v' ∧
          segment ℝ u v = segment ℝ u' v' ∧ RS W S (a, u', v') := by
        refine ⟨_, S0, rfl, u, v, hA, rfl, ?_⟩
        show VS W S0 a ⊆ segment ℝ u v ∧ midpoint ℝ u v ∈ VS W S0 a
        rw [hV]; exact ⟨hsub, hmid⟩
      obtain ⟨S1, hrk, u1, v1, hA1, he1, hR1⟩ := Nat.find_spec hex
      have hmin : ∀ S' : Finset (Fin n), rk S' < rk S1 → ∀ u' v',
          Hirsch.Adj (polygon W a) u' v' → segment ℝ u v = segment ℝ u' v' →
            ¬ RS W S' (a, u', v') := by
        intro S' hlt u' v' hA' he' hR'
        exact Nat.find_min hex (by rw [← hrk]; exact hlt) ⟨S', rfl, u', v', hA', he', hR'⟩
      rcases lex_total hA1.1 with hl | hl
      · have hb : ((a, u1, v1) : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
            EuclideanSpace ℝ (Fin d)) ∈ BS W S1 :=
          ⟨hA1, hR1, fun S' hlt hR' => hmin S' hlt u1 v1 hA1 he1 hR', hl⟩
        refine ⟨S1, (hFmem S1).2 ⟨_, hb, rfl⟩, ?_⟩
        rw [hgb S1 _ hb rfl, he1]
      · have hb : ((a, v1, u1) : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
            EuclideanSpace ℝ (Fin d)) ∈ BS W S1 :=
          ⟨adj_swap hA1, (RS_swap W S1 a u1 v1).1 hR1,
            fun S' hlt hR' => hmin S' hlt u1 v1 hA1 he1 ((RS_swap W S' a u1 v1).2 hR'), hl⟩
        refine ⟨S1, (hFmem S1).2 ⟨_, hb, rfl⟩, ?_⟩
        rw [hgb S1 _ hb rfl, he1, segment_symm]
  unfold edgeCount
  rw [← himg, Set.ncard_image_of_injOn hinj, Set.ncard_coe_finset]

theorem measurable_edgeCount (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    Measurable (fun a : Fin n → EuclideanSpace ℝ (Fin d) => (edgeCount (polygon W a) : ℝ≥0∞)) := by
  classical
  have h : (fun a : Fin n → EuclideanSpace ℝ (Fin d) => (edgeCount (polygon W a) : ℝ≥0∞)) =
      fun a => ∑ S : Finset (Fin n), (Prod.fst '' BS W S).indicator (fun _ => (1 : ℝ≥0∞)) a := by
    funext a
    rw [edgeCount_eq, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun S _ => ?_)
    by_cases hS : a ∈ Prod.fst '' BS W S <;> simp [hS]
  rw [h]
  exact Finset.measurable_sum _ (fun S _ => measurable_const.indicator (meas_G W S))

end C5747Cnt2
end MeasExt

-- ===== Cross.lean =====
section SecCross


open scoped RealInnerProductSpace

/-! O2b of scratch/decomp/b53119b3.plan.md: distinct extreme segments of a planar set cross a
level line `{x ∈ W | ⟪x, e⟫ = s}` at most twice. -/

namespace FSCross

variable {d : ℕ}

/-- A segment whose ends lie strictly on both sides of the level `s` crosses it at an interior
point. -/
theorem cross_point (u v e : EuclideanSpace ℝ (Fin d)) (s : ℝ)
    (hs : min ⟪u, e⟫ ⟪v, e⟫ < s ∧ s < max ⟪u, e⟫ ⟪v, e⟫) :
    ∃ p ∈ openSegment ℝ u v, ⟪p, e⟫ = s := by
  set a := ⟪u, e⟫ with ha
  set b := ⟪v, e⟫ with hb
  have hab : a ≠ b := by
    intro h
    rw [h, min_self, max_self] at hs
    linarith [hs.1, hs.2]
  have hba : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  refine ⟨u + ((s - a) / (b - a)) • (v - u), ?_, ?_⟩
  · rw [openSegment_eq_image']
    refine ⟨(s - a) / (b - a), ⟨?_, ?_⟩, rfl⟩
    · rcases lt_or_gt_of_ne hab with h | h
      · rw [min_eq_left h.le] at hs
        exact div_pos (by linarith [hs.1]) (by linarith)
      · rw [min_eq_right h.le] at hs
        rw [max_eq_left h.le] at hs
        exact div_pos_of_neg_of_neg (by linarith [hs.2]) (by linarith)
    · rcases lt_or_gt_of_ne hab with h | h
      · rw [max_eq_right h.le] at hs
        rw [div_lt_one (by linarith)]
        linarith [hs.2]
      · rw [min_eq_right h.le] at hs
        rw [div_lt_one_of_neg (by linarith)]
        linarith [hs.1]
  · rw [inner_add_left, real_inner_smul_left, inner_sub_left, ← ha, ← hb,
      div_mul_cancel₀ _ hba]
    ring

/-- On a transversal segment the level `⟪·, e⟫` is injective. -/
theorem seg_level_unique {u v e p q : EuclideanSpace ℝ (Fin d)} (huv : ⟪u, e⟫ ≠ ⟪v, e⟫)
    (hp : p ∈ segment ℝ u v) (hq : q ∈ segment ℝ u v) (hpq : ⟪p, e⟫ = ⟪q, e⟫) : p = q := by
  rw [segment_eq_image'] at hp hq
  obtain ⟨t, -, rfl⟩ := hp
  obtain ⟨t', -, rfl⟩ := hq
  simp only [inner_add_left, real_inner_smul_left, inner_sub_left] at hpq
  have h2 : (t - t') * (⟪v, e⟫ - ⟪u, e⟫) = 0 := by linear_combination hpq
  have htt : t = t' := by
    rcases mul_eq_zero.1 h2 with h | h
    · linarith
    · exact absurd (sub_eq_zero.1 h).symm huv
  rw [htt]

/-- Two extreme segments sharing a relative-interior point are equal. -/
theorem edge_eq_of_common {P : Set (EuclideanSpace ℝ (Fin d))} {u v u' v' p : EuclideanSpace ℝ (Fin d)}
    (h1 : IsExtreme ℝ P (segment ℝ u v)) (h2 : IsExtreme ℝ P (segment ℝ u' v'))
    (hp1 : p ∈ openSegment ℝ u v) (hp2 : p ∈ openSegment ℝ u' v') :
    segment ℝ u v = segment ℝ u' v' := by
  have hu : u ∈ P := h1.subset (left_mem_segment ℝ u v)
  have hv : v ∈ P := h1.subset (right_mem_segment ℝ u v)
  have hu2 : u' ∈ P := h2.subset (left_mem_segment ℝ u' v')
  have hv2 : v' ∈ P := h2.subset (right_mem_segment ℝ u' v')
  have a1 : u ∈ segment ℝ u' v' :=
    h2.left_mem_of_mem_openSegment hu hv (openSegment_subset_segment ℝ u' v' hp2) hp1
  have a2 : v ∈ segment ℝ u' v' :=
    h2.right_mem_of_mem_openSegment hu hv (openSegment_subset_segment ℝ u' v' hp2) hp1
  have b1 : u' ∈ segment ℝ u v :=
    h1.left_mem_of_mem_openSegment hu2 hv2 (openSegment_subset_segment ℝ u v hp1) hp2
  have b2 : v' ∈ segment ℝ u v :=
    h1.right_mem_of_mem_openSegment hu2 hv2 (openSegment_subset_segment ℝ u v hp1) hp2
  exact Set.Subset.antisymm ((convex_segment u' v').segment_subset a1 a2)
    ((convex_segment u v).segment_subset b1 b2)

/-- The middle crossing point of three distinct collinear crossings is impossible. -/
theorem no_middle {P : Set (EuclideanSpace ℝ (Fin d))} {u v e p₁ p₂ p₃ : EuclideanSpace ℝ (Fin d)}
    {s : ℝ} (hF : IsExtreme ℝ P (segment ℝ u v)) (htr : ⟪u, e⟫ ≠ ⟪v, e⟫)
    (hp₁ : p₁ ∈ P) (hp₃ : p₃ ∈ P) (hq : p₂ ∈ openSegment ℝ u v)
    (h₁ : ⟪p₁, e⟫ = s) (h₃ : ⟪p₃, e⟫ = s) (hw : Wbtw ℝ p₁ p₂ p₃)
    (hne₁ : p₁ ≠ p₂) (hne₃ : p₃ ≠ p₂) : False := by
  have hmid : p₂ ∈ openSegment ℝ p₁ p₃ :=
    mem_openSegment_of_ne_left_right hne₁ hne₃ (mem_segment_iff_wbtw.2 hw)
  have hF₁ : p₁ ∈ segment ℝ u v :=
    hF.left_mem_of_mem_openSegment hp₁ hp₃ (openSegment_subset_segment ℝ u v hq) hmid
  have hF₃ : p₃ ∈ segment ℝ u v :=
    hF.right_mem_of_mem_openSegment hp₁ hp₃ (openSegment_subset_segment ℝ u v hq) hmid
  have h13 : p₁ = p₃ := seg_level_unique htr hF₁ hF₃ (h₁.trans h₃.symm)
  rw [h13, openSegment_same] at hmid
  exact hne₃ (Set.mem_singleton_iff.1 hmid).symm

/-- Points of a plane `W` on one level line of a nonzero `e ∈ W` are collinear. -/
theorem collinear_level (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hW : Module.finrank ℝ W = 2) {e : EuclideanSpace ℝ (Fin d)} (he : e ∈ W) (he0 : e ≠ 0)
    {s : ℝ} {p₁ p₂ p₃ : EuclideanSpace ℝ (Fin d)} (hW₁ : p₁ ∈ W) (hW₂ : p₂ ∈ W) (hW₃ : p₃ ∈ W)
    (h₁ : ⟪p₁, e⟫ = s) (h₂ : ⟪p₂, e⟫ = s) (h₃ : ⟪p₃, e⟫ = s) :
    Collinear ℝ ({p₁, p₂, p₃} : Set (EuclideanSpace ℝ (Fin d))) := by
  set K : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := W ⊓ (ℝ ∙ e)ᗮ with hK
  have hspan : vectorSpan ℝ ({p₁, p₂, p₃} : Set (EuclideanSpace ℝ (Fin d))) ≤ K := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro x ⟨a, ha, b, hb, rfl⟩
    have hmemW : ∀ y ∈ ({p₁, p₂, p₃} : Set (EuclideanSpace ℝ (Fin d))), y ∈ W ∧ ⟪y, e⟫ = s := by
      intro y hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨hW₁, h₁⟩
      · exact ⟨hW₂, h₂⟩
      · exact ⟨hW₃, h₃⟩
    obtain ⟨haW, has⟩ := hmemW a ha
    obtain ⟨hbW, hbs⟩ := hmemW b hb
    refine ⟨W.sub_mem haW hbW, ?_⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    show ⟪e, a - b⟫ = 0
    rw [inner_sub_right, real_inner_comm a e, real_inner_comm b e, has, hbs, sub_self]
  have hlt : K < W := by
    refine lt_of_le_of_ne inf_le_left (fun h => ?_)
    have heK : e ∈ K := h ▸ he
    have := (Submodule.mem_orthogonal_singleton_iff_inner_right.1 heK.2)
    exact he0 (inner_self_eq_zero.1 this)
  have hK1 : Module.finrank ℝ K < 2 := hW ▸ Submodule.finrank_lt_finrank_of_lt hlt
  rw [collinear_iff_finrank_le_one]
  have := Submodule.finrank_mono hspan
  omega

end FSCross
end SecCross

-- ===== L19c.lean =====
section SecL19c


open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace FSLib19

/-- Union bound over the rows for the tail event of the maximum. -/
theorem tail_le {d n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (x : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (hx : ∀ i, Measurable (x i))
    (c : Fin n → EuclideanSpace ℝ (Fin d))
    (θ : EuclideanSpace ℝ (Fin d)) (hn : (Finset.univ : Finset (Fin n)).Nonempty) (t : ℝ) :
    P {ω | t ≤ Finset.univ.sup' hn (fun i => |⟪θ, x i ω - c i⟫|)} ≤
      ∑ i, (P.map (x i)) {y | t ≤ |⟪y - c i, θ⟫|} := by
  have hsub : {ω | t ≤ Finset.univ.sup' hn (fun i => |⟪θ, x i ω - c i⟫|)} ⊆
      ⋃ i, (x i) ⁻¹' {y | t ≤ |⟪y - c i, θ⟫|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' hn (fun i => |⟪θ, x i ω - c i⟫|)
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [real_inner_comm]
    linarith [hi ▸ hω]
  refine (measure_mono hsub).trans ((measure_iUnion_fintype_le P _).trans ?_)
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hS : MeasurableSet {y : EuclideanSpace ℝ (Fin d) | t ≤ |⟪y - c i, θ⟫|} :=
    measurableSet_le measurable_const
      ((continuous_abs.comp ((continuous_id.sub continuous_const).inner
        continuous_const)).measurable)
  rw [Measure.map_apply (hx i) hS]

end FSLib19

open MeasureTheory FriendlyShadow.Gaussian RealInnerProductSpace ENNReal in
/-- Lemma 19 with centers: `E[max_i |⟨θ, x_i − c_i⟩|] ≤ 2r` when row `i` has `n`-th deviation `≤ r`
about `c i` (no mean or independence hypothesis needed). -/
theorem FSLib19.max_dev_le {d n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (x : Fin n → Ω → EuclideanSpace ℝ (Fin d))
    (hx : ∀ i, Measurable (x i)) (μ : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (hlaw : ∀ i, P.map (x i) = densityMeasure (μ i))
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : ∀ i, NthDeviationLE (μ i) (c i) n r)
    (θ : EuclideanSpace ℝ (Fin d)) (hθ : ‖θ‖ = 1) :
    ∫⁻ ω, (⨆ i, ENNReal.ofReal |⟪θ, x i ω - c i⟫|) ∂P ≤ ENNReal.ofReal (2 * r) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    simp
  have hn : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty_iff.2 ⟨⟨0, hnpos⟩⟩
  set f : Ω → ℝ := fun ω => Finset.univ.sup' hn (fun i => |⟪θ, x i ω - c i⟫|) with hf
  have hfm : Measurable f := by
    have h := Finset.measurable_sup' (s := (Finset.univ : Finset (Fin n))) hn
      (f := fun i ω => |⟪θ, x i ω - c i⟫|)
      (fun i _ => (continuous_abs.comp (continuous_const.inner (continuous_id.sub continuous_const))).measurable.comp
        (hx i))
    convert h using 1
    funext ω
    rw [Finset.sup'_apply]
  have hsup : ∀ ω, (⨆ i, ENNReal.ofReal |⟪θ, x i ω - c i⟫|) = ENNReal.ofReal (f ω) := by
    intro ω
    apply le_antisymm
    · exact iSup_le (fun i => ENNReal.ofReal_le_ofReal
        (Finset.le_sup' (fun i => |⟪θ, x i ω - c i⟫|) (Finset.mem_univ i)))
    · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' hn (fun i => |⟪θ, x i ω - c i⟫|)
      rw [hf]
      simp only
      rw [hi]
      exact le_iSup (fun i => ENNReal.ofReal |⟪θ, x i ω - c i⟫|) i
  have hnn : 0 ≤ᵐ[P] f := Filter.Eventually.of_forall (fun ω => by
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' hn (fun i => |⟪θ, x i ω - c i⟫|)
    show 0 ≤ f ω
    rw [hf]
    simp only
    rw [hi]
    exact abs_nonneg _)
  simp_rw [hsup]
  rw [lintegral_eq_lintegral_meas_le P hnn hfm.aemeasurable]
  -- split `Ioi 0` into `Ioc 0 r` and `Ioi r`
  have hcover : Set.Ioi (0 : ℝ) ⊆ Set.Ioc 0 r ∪ Set.Ioi r := by
    intro t ht
    by_cases h : t ≤ r
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr (lt_of_not_ge h)
  have h1 : ∫⁻ t in Set.Ioc 0 r, P {a | t ≤ f a} ≤ ENNReal.ofReal r := by
    calc ∫⁻ t in Set.Ioc 0 r, P {a | t ≤ f a}
        ≤ ∫⁻ _t in Set.Ioc 0 r, (1 : ℝ≥0∞) := lintegral_mono (fun t => prob_le_one)
      _ = ENNReal.ofReal r := by
        rw [setLIntegral_const, one_mul, Real.volume_Ioc, sub_zero]
  have h2 : ∫⁻ t in Set.Ioi r, P {a | t ≤ f a} ≤ ENNReal.ofReal r := by
    calc ∫⁻ t in Set.Ioi r, P {a | t ≤ f a}
        ≤ ∫⁻ t in Set.Ioi r, ∑ i, densityMeasure (μ i) {y | t ≤ |⟪y - c i, θ⟫|} := by
          refine lintegral_mono (fun t => ?_)
          refine (FSLib19.tail_le P x hx c θ hn t).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl (fun i _ => by rw [hlaw i])
      _ = ∑ i, ∫⁻ t in Set.Ioi r, densityMeasure (μ i) {y | t ≤ |⟪y - c i, θ⟫|} := by
          rw [lintegral_finsetSum']
          intro i _
          refine Measurable.aemeasurable ?_
          refine Antitone.measurable (fun s t hst => measure_mono ?_)
          intro y hy
          simp only [Set.mem_ofPred_eq] at hy ⊢
          linarith
      _ ≤ ∑ _i : Fin n, ENNReal.ofReal (r / n) := Finset.sum_le_sum (fun i _ => hr i θ hθ)
      _ = ENNReal.ofReal r := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
  calc ∫⁻ t in Set.Ioi 0, P {a | t ≤ f a}
      ≤ ∫⁻ t in Set.Ioc 0 r ∪ Set.Ioi r, P {a | t ≤ f a} := lintegral_mono_set hcover
    _ ≤ (∫⁻ t in Set.Ioc 0 r, P {a | t ≤ f a}) + ∫⁻ t in Set.Ioi r, P {a | t ≤ f a} :=
        lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal r + ENNReal.ofReal r := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * r) := by
        rcases le_or_gt 0 r with hr0 | hr0
        · rw [← ENNReal.ofReal_add hr0 hr0]
          ring_nf
        · rw [ENNReal.ofReal_of_nonpos hr0.le, ENNReal.ofReal_of_nonpos (by linarith)]
          simp
end SecL19c

-- ===== Proj.lean =====
section SecProj
/-! O2b count + O2c projection sum (append after Cross.lean; same imports). -/

namespace FSCross

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

variable {d : ℕ}

/-- Three distinct edges of a planar set cannot all cross one level line transversally. -/
theorem no_three {P : Set (EuclideanSpace ℝ (Fin d))} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hW : Module.finrank ℝ W = 2) (hPW : P ⊆ W) {e : EuclideanSpace ℝ (Fin d)} (he : e ∈ W)
    (he0 : e ≠ 0) {s : ℝ} {u₁ v₁ u₂ v₂ u₃ v₃ : EuclideanSpace ℝ (Fin d)}
    (h₁ : Hirsch.Adj P u₁ v₁) (h₂ : Hirsch.Adj P u₂ v₂) (h₃ : Hirsch.Adj P u₃ v₃)
    (d₁₂ : segment ℝ u₁ v₁ ≠ segment ℝ u₂ v₂) (d₁₃ : segment ℝ u₁ v₁ ≠ segment ℝ u₃ v₃)
    (d₂₃ : segment ℝ u₂ v₂ ≠ segment ℝ u₃ v₃)
    (c₁ : min ⟪u₁, e⟫ ⟪v₁, e⟫ < s ∧ s < max ⟪u₁, e⟫ ⟪v₁, e⟫)
    (c₂ : min ⟪u₂, e⟫ ⟪v₂, e⟫ < s ∧ s < max ⟪u₂, e⟫ ⟪v₂, e⟫)
    (c₃ : min ⟪u₃, e⟫ ⟪v₃, e⟫ < s ∧ s < max ⟪u₃, e⟫ ⟪v₃, e⟫) : False := by
  have htr : ∀ {u v : EuclideanSpace ℝ (Fin d)},
      (min ⟪u, e⟫ ⟪v, e⟫ < s ∧ s < max ⟪u, e⟫ ⟪v, e⟫) → ⟪u, e⟫ ≠ ⟪v, e⟫ := by
    intro u v c h
    rw [h, min_self, max_self] at c
    linarith [c.1, c.2]
  have hP : ∀ {u v p : EuclideanSpace ℝ (Fin d)}, Hirsch.Adj P u v → p ∈ openSegment ℝ u v →
      p ∈ P := fun h hp => h.2.subset (openSegment_subset_segment ℝ _ _ hp)
  obtain ⟨p₁, hq₁, hs₁⟩ := cross_point u₁ v₁ e s c₁
  obtain ⟨p₂, hq₂, hs₂⟩ := cross_point u₂ v₂ e s c₂
  obtain ⟨p₃, hq₃, hs₃⟩ := cross_point u₃ v₃ e s c₃
  have hne : ∀ {u v u' v' p p' : EuclideanSpace ℝ (Fin d)}, Hirsch.Adj P u v → Hirsch.Adj P u' v' →
      segment ℝ u v ≠ segment ℝ u' v' → p ∈ openSegment ℝ u v → p' ∈ openSegment ℝ u' v' →
      p ≠ p' := by
    intro u v u' v' p p' h h' hd hp hp' hpp
    subst hpp
    exact hd (edge_eq_of_common h.2 h'.2 hp hp')
  have n12 := hne h₁ h₂ d₁₂ hq₁ hq₂
  have n13 := hne h₁ h₃ d₁₃ hq₁ hq₃
  have n23 := hne h₂ h₃ d₂₃ hq₂ hq₃
  have hcol := collinear_level W hW he he0 (hPW (hP h₁ hq₁)) (hPW (hP h₂ hq₂)) (hPW (hP h₃ hq₃))
    hs₁ hs₂ hs₃
  rcases hcol.wbtw_or_wbtw_or_wbtw with hw | hw | hw
  · exact no_middle h₂.2 (htr c₂) (hP h₁ hq₁) (hP h₃ hq₃) hq₂ hs₁ hs₃ hw n12 (Ne.symm n23)
  · exact no_middle h₃.2 (htr c₃) (hP h₂ hq₂) (hP h₁ hq₁) hq₃ hs₂ hs₁ hw n23 n13
  · exact no_middle h₁.2 (htr c₁) (hP h₃ hq₃) (hP h₂ hq₂) hq₁ hs₃ hs₂ hw (Ne.symm n13)
      (Ne.symm n12)

/-- At most two edges of an injective edge family cross a given level transversally. -/
theorem count_le_two {ι : Type*} {P : Set (EuclideanSpace ℝ (Fin d))}
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hW : Module.finrank ℝ W = 2) (hPW : P ⊆ W)
    {e : EuclideanSpace ℝ (Fin d)} (he : e ∈ W) (he0 : e ≠ 0)
    (u v : ι → EuclideanSpace ℝ (Fin d)) (hadj : ∀ j, Hirsch.Adj P (u j) (v j))
    (hinj : ∀ j k, segment ℝ (u j) (v j) = segment ℝ (u k) (v k) → j = k)
    (s : ℝ) (S : Finset ι) [DecidablePred (fun j => min ⟪u j, e⟫ ⟪v j, e⟫ < s ∧ s < max ⟪u j, e⟫ ⟪v j, e⟫)] :
    (S.filter (fun j => min ⟪u j, e⟫ ⟪v j, e⟫ < s ∧ s < max ⟪u j, e⟫ ⟪v j, e⟫)).card ≤ 2 := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 hlt
  rw [Finset.mem_filter] at ha hb hc
  exact no_three W hW hPW he he0 (hadj a) (hadj b) (hadj c)
    (fun h => hab (hinj a b h)) (fun h => hac (hinj a c h)) (fun h => hbc (hinj b c h))
    ha.2 hb.2 hc.2

/-- Projection sum: an injective finite family of edges of a planar set whose `e`-levels lie in
`[m, M]` has total `e`-projection at most `2 (M - m)`. -/
theorem proj_sum_le {ι : Type*} {P : Set (EuclideanSpace ℝ (Fin d))}
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hW : Module.finrank ℝ W = 2) (hPW : P ⊆ W)
    {e : EuclideanSpace ℝ (Fin d)} (he : e ∈ W)
    (u v : ι → EuclideanSpace ℝ (Fin d)) (hadj : ∀ j, Hirsch.Adj P (u j) (v j))
    (hinj : ∀ j k, segment ℝ (u j) (v j) = segment ℝ (u k) (v k) → j = k)
    (m M : ℝ) (hm : ∀ x ∈ P, m ≤ ⟪x, e⟫) (hM : ∀ x ∈ P, ⟪x, e⟫ ≤ M) (S : Finset ι) :
    ∑ j ∈ S, ENNReal.ofReal |⟪v j - u j, e⟫| ≤ 2 * ENNReal.ofReal (M - m) := by
  classical
  by_cases he0 : e = 0
  · subst he0
    simp
  set I : ι → Set ℝ := fun j => Set.Ioo (min ⟪u j, e⟫ ⟪v j, e⟫) (max ⟪u j, e⟫ ⟪v j, e⟫) with hI
  have hterm : ∀ j, ENNReal.ofReal |⟪v j - u j, e⟫| = ∫⁻ x, (I j).indicator 1 x := by
    intro j
    rw [lintegral_indicator_one measurableSet_Ioo, Real.volume_Ioo, max_sub_min_eq_abs,
      inner_sub_left, abs_sub_comm]
  have hsub : ∀ j, I j ⊆ Set.Icc m M := by
    intro j x hx
    have hu : u j ∈ P := (hadj j).2.subset (left_mem_segment ℝ _ _)
    have hv : v j ∈ P := (hadj j).2.subset (right_mem_segment ℝ _ _)
    have h1 := hm _ hu
    have h2 := hm _ hv
    have h3 := hM _ hu
    have h4 := hM _ hv
    obtain ⟨hx1, hx2⟩ := hx
    constructor
    · exact le_trans (le_min h1 h2) hx1.le
    · exact le_trans hx2.le (max_le h3 h4)
  simp_rw [hterm]
  rw [← lintegral_finsetSum _ (fun j _ => (measurable_one.indicator measurableSet_Ioo))]
  calc ∫⁻ x, ∑ j ∈ S, (I j).indicator 1 x
      ≤ ∫⁻ x, (Set.Icc m M).indicator (fun _ => (2 : ℝ≥0∞)) x := by
        refine lintegral_mono (fun x => ?_)
        by_cases hx : x ∈ Set.Icc m M
        · rw [Set.indicator_of_mem hx]
          have hcount : ∑ j ∈ S, (I j).indicator (1 : ℝ → ℝ≥0∞) x =
              ((S.filter (fun j => min ⟪u j, e⟫ ⟪v j, e⟫ < x ∧ x < max ⟪u j, e⟫ ⟪v j, e⟫)).card :
                ℝ≥0∞) := by
            rw [Finset.card_filter, Nat.cast_sum]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            simp only [Set.indicator, hI, Set.mem_Ioo, Pi.one_apply]
            split_ifs <;> simp
          rw [hcount]
          have h := count_le_two W hW hPW he he0 u v hadj hinj x S
          exact (Nat.cast_le.2 (by convert h)).trans_eq (by norm_num)
        · have : ∑ j ∈ S, (I j).indicator (1 : ℝ → ℝ≥0∞) x = 0 :=
            Finset.sum_eq_zero (fun j _ => Set.indicator_of_notMem (fun h => hx (hsub j h)) _)
          rw [this]
          positivity
    _ = 2 * ENNReal.ofReal (M - m) := by
        rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]

end FSCross
end SecProj

-- ===== Angle.lean =====
section SecAngle


/-! O2d of scratch/decomp/b53119b3.plan.md: the direction average
`∫_0^{2π} |⟪x, cos φ • b₀ + sin φ • b₁⟫| dφ = 4 ‖x‖` for `x` in the plane spanned by the
orthonormal pair `b₀, b₁`. -/

namespace FSAngle

open Real intervalIntegral MeasureTheory
open scoped RealInnerProductSpace

theorem abs_cos_periodic : Function.Periodic (fun φ : ℝ => |cos φ|) (2 * π) := fun φ => by
  simp only [cos_add_two_pi]

theorem integral_abs_cos : ∫ φ in (0:ℝ)..(2 * π), |cos φ| = 4 := by
  have h1 : ∫ φ in (0:ℝ)..(2 * π), |cos φ| = ∫ φ in (-(π / 2))..(-(π / 2) + 2 * π), |cos φ| := by
    have := abs_cos_periodic.intervalIntegral_add_eq 0 (-(π / 2))
    rw [zero_add] at this
    exact this
  rw [h1]
  have hc : Continuous (fun φ : ℝ => |cos φ|) := continuous_abs.comp continuous_cos
  rw [← integral_add_adjacent_intervals (b := π / 2) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have hA : ∫ φ in (-(π / 2))..(π / 2), |cos φ| = ∫ φ in (-(π / 2))..(π / 2), cos φ := by
    refine integral_congr (fun φ hφ => ?_)
    rw [Set.uIcc_of_le (by linarith [pi_pos])] at hφ
    exact abs_of_nonneg (cos_nonneg_of_mem_Icc hφ)
  have hB : ∫ φ in (π / 2)..(-(π / 2) + 2 * π), |cos φ| =
      ∫ φ in (π / 2)..(-(π / 2) + 2 * π), -cos φ := by
    refine integral_congr (fun φ hφ => ?_)
    rw [Set.uIcc_of_le (by linarith [pi_pos])] at hφ
    exact abs_of_nonpos (cos_nonpos_of_pi_div_two_le_of_le hφ.1 (by linarith [hφ.2]))
  rw [hA, hB, integral_cos, intervalIntegral.integral_neg, integral_cos]
  have : sin (-(π / 2) + 2 * π) = -1 := by rw [sin_add_two_pi, sin_neg, sin_pi_div_two]
  rw [this, sin_neg, sin_pi_div_two]
  norm_num

theorem integral_abs_lin (α β : ℝ) :
    ∫ φ in (0:ℝ)..(2 * π), |α * cos φ + β * sin φ| = 4 * ‖(⟨α, β⟩ : ℂ)‖ := by
  set z : ℂ := ⟨α, β⟩ with hz
  set θ := Complex.arg z
  have hα : ‖z‖ * cos θ = α := Complex.norm_mul_cos_arg z
  have hβ : ‖z‖ * sin θ = β := Complex.norm_mul_sin_arg z
  have hfun : ∀ φ, |α * cos φ + β * sin φ| = ‖z‖ * |cos (φ - θ)| := by
    intro φ
    have : α * cos φ + β * sin φ = ‖z‖ * cos (φ - θ) := by
      rw [cos_sub, ← hα, ← hβ]
      ring
    rw [this, abs_mul, abs_norm]
  simp_rw [hfun]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (fun x => |cos x|) θ]
  have h2 : (2 * π - θ) = (0 - θ) + 2 * π := by ring
  rw [h2, abs_cos_periodic.intervalIntegral_add_eq (0 - θ) 0, zero_add, integral_abs_cos]
  ring

/-- The direction average in a plane with orthonormal basis `b`. -/
theorem integral_abs_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (W : Submodule ℝ E) (b : OrthonormalBasis (Fin 2) ℝ W) (x : E) (hx : x ∈ W) :
    ∫ φ in (0:ℝ)..(2 * π), |⟪x, cos φ • (b 0 : E) + sin φ • (b 1 : E)⟫| = 4 * ‖x‖ := by
  set α := ⟪x, (b 0 : E)⟫
  set β := ⟪x, (b 1 : E)⟫
  have hfun : ∀ φ, ⟪x, cos φ • (b 0 : E) + sin φ • (b 1 : E)⟫ = α * cos φ + β * sin φ := by
    intro φ
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    ring
  simp_rw [hfun]
  rw [integral_abs_lin]
  congr 1
  have hsq : ‖x‖ ^ 2 = α ^ 2 + β ^ 2 := by
    have := b.sum_sq_inner_left ⟨x, hx⟩
    rw [Fin.sum_univ_two] at this
    exact this.symm
  have hz : ‖(⟨α, β⟩ : ℂ)‖ ^ 2 = α ^ 2 + β ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_mk]
    ring
  have := hz.trans hsq.symm
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

/-- Lintegral form over `Ioc 0 (2π)`. -/
theorem lintegral_abs_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (W : Submodule ℝ E) (b : OrthonormalBasis (Fin 2) ℝ W) (x : E) (hx : x ∈ W) :
    ∫⁻ φ in Set.Ioc 0 (2 * π), ENNReal.ofReal |⟪x, cos φ • (b 0 : E) + sin φ • (b 1 : E)⟫| =
      ENNReal.ofReal (4 * ‖x‖) := by
  have hc : Continuous (fun φ : ℝ => |⟪x, cos φ • (b 0 : E) + sin φ • (b 1 : E)⟫|) := by
    fun_prop
  rw [← integral_abs_inner W b x hx, intervalIntegral.integral_of_le (by positivity),
    ofReal_integral_eq_lintegral_ofReal ((hc.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self)
      (ae_of_all _ (fun _ => abs_nonneg _))]

/-- The direction vectors are unit vectors. -/
theorem norm_dir {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (W : Submodule ℝ E) (b : OrthonormalBasis (Fin 2) ℝ W) (φ : ℝ) :
    ‖cos φ • (b 0 : E) + sin φ • (b 1 : E)‖ = 1 := by
  have h0 : ‖(b 0 : E)‖ = 1 := b.orthonormal.1 0
  have h1 : ‖(b 1 : E)‖ = 1 := b.orthonormal.1 1
  have h01 : ⟪(b 0 : E), (b 1 : E)⟫ = 0 := b.orthonormal.2 (by decide)
  have hsq : ‖cos φ • (b 0 : E) + sin φ • (b 1 : E)‖ ^ 2 = 1 := by
    rw [@norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      h01, h0, h1, Real.norm_eq_abs, Real.norm_eq_abs]
    nlinarith [sin_sq_add_cos_sq φ, sq_abs (cos φ), sq_abs (sin φ)]
  have hn := norm_nonneg (cos φ • (b 0 : E) + sin φ • (b 1 : E))
  nlinarith [hsq]

end FSAngle
end SecAngle

-- ===== Perim.lean =====
section SecPerim
/-! O2e: E[perimeter(Q ∩ W)] ≤ 2π(1 + 2r). Append after Cross.lean, Proj.lean, Angle.lean. -/

namespace FSPerim

open scoped RealInnerProductSpace ENNReal
open MeasureTheory Real FriendlyShadow.Gaussian

variable {d n : ℕ}

/-- Points of `conv(a)` have `|⟪w, x⟫| ≤ 1 + D` when the centers are in the unit ball. -/
theorem hull_bound (a abar : Fin n → EuclideanSpace ℝ (Fin d)) (habar : ∀ i, ‖abar i‖ ≤ 1)
    (w : EuclideanSpace ℝ (Fin d)) (hw : ‖w‖ = 1) (D : ℝ)
    (hD : ∀ i, |⟪w, a i - abar i⟫| ≤ D) :
    ∀ x ∈ convexHull ℝ (Set.range a), |⟪w, x⟫| ≤ 1 + D := by
  have hconv : Convex ℝ {x : EuclideanSpace ℝ (Fin d) | |⟪w, x⟫| ≤ 1 + D} := by
    intro x hx y hy s t hs ht hst
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    calc |s * ⟪w, x⟫ + t * ⟪w, y⟫| ≤ |s * ⟪w, x⟫| + |t * ⟪w, y⟫| := abs_add_le _ _
      _ = s * |⟪w, x⟫| + t * |⟪w, y⟫| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
      _ ≤ s * (1 + D) + t * (1 + D) := by gcongr
      _ = 1 + D := by rw [← add_mul, hst, one_mul]
  refine fun x hx => convexHull_min ?_ hconv hx
  rintro _ ⟨i, rfl⟩
  simp only [Set.mem_setOf_eq]
  have h1 : ⟪w, a i⟫ = ⟪w, abar i⟫ + ⟪w, a i - abar i⟫ := by
    rw [inner_sub_right]; ring
  have h2 : |⟪w, abar i⟫| ≤ 1 := by
    calc |⟪w, abar i⟫| ≤ ‖w‖ * ‖abar i‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 := by rw [hw, one_mul]; exact habar i
  rw [h1]
  exact (abs_add_le _ _).trans (add_le_add h2 (hD i))

/-- Deterministic perimeter bound via the direction average. -/
theorem perimeter_le (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hW : Module.finrank ℝ W = 2)
    (b : OrthonormalBasis (Fin 2) ℝ W) (a abar : Fin n → EuclideanSpace ℝ (Fin d))
    (habar : ∀ i, ‖abar i‖ ≤ 1) :
    perimeter (polygon W a) ≤ ∫⁻ φ in Set.Ioc 0 (2 * π),
      ENNReal.ofReal (1 + ⨆ i, |⟪cos φ • (b 0 : EuclideanSpace ℝ (Fin d)) + sin φ • (b 1 : _),
        a i - abar i⟫|) := by
  classical
  set P := polygon W a with hP
  have hPW : P ⊆ W := Set.inter_subset_right
  have hch : ∀ F : edges P, ∃ u v, Hirsch.Adj P u v ∧ (F : Set _) = segment ℝ u v := fun F => F.2
  choose u v huv hF using hch
  have hinj : ∀ F G, segment ℝ (u F) (v F) = segment ℝ (u G) (v G) → F = G :=
    fun F G h => Subtype.ext ((hF F).trans (h.trans (hF G).symm))
  have hwW : ∀ φ : ℝ, cos φ • (b 0 : EuclideanSpace ℝ (Fin d)) + sin φ • (b 1 : _) ∈ W :=
    fun φ => W.add_mem (W.smul_mem _ (b 0).2) (W.smul_mem _ (b 1).2)
  have hDr : ∀ (φ : ℝ) (i : Fin n),
      |⟪cos φ • (b 0 : EuclideanSpace ℝ (Fin d)) + sin φ • (b 1 : _), a i - abar i⟫| ≤
        ⨆ j, |⟪cos φ • (b 0 : EuclideanSpace ℝ (Fin d)) + sin φ • (b 1 : _), a j - abar j⟫| :=
    fun φ i => le_ciSup (f := fun j =>
      |⟪cos φ • (b 0 : EuclideanSpace ℝ (Fin d)) + sin φ • (b 1 : _), a j - abar j⟫|)
      (Set.finite_range _).bddAbove i
  have hbd : ∀ (φ : ℝ), ∀ x ∈ P,
      |⟪x, cos φ • (b 0 : EuclideanSpace ℝ (Fin d)) + sin φ • (b 1 : _)⟫| ≤
        1 + ⨆ j, |⟪cos φ • (b 0 : EuclideanSpace ℝ (Fin d)) + sin φ • (b 1 : _), a j - abar j⟫| := by
    intro φ x hx
    rw [real_inner_comm]
    exact hull_bound a abar habar _ (FSAngle.norm_dir W b φ) _ (hDr φ) x hx.1
  have hdiam : ∀ F : edges P, 4 * Metric.ediam (F : Set (EuclideanSpace ℝ (Fin d))) =
      ∫⁻ φ in Set.Ioc 0 (2 * π), ENNReal.ofReal
        |⟪v F - u F, cos φ • (b 0 : EuclideanSpace ℝ (Fin d)) + sin φ • (b 1 : _)⟫| := by
    intro F
    have hu : u F ∈ P := (huv F).2.subset (left_mem_segment ℝ _ _)
    have hv : v F ∈ P := (huv F).2.subset (right_mem_segment ℝ _ _)
    rw [hF F, ← convexHull_pair, convexHull_ediam, Metric.ediam_pair, edist_dist, dist_eq_norm,
      FSAngle.lintegral_abs_inner W b _ (W.sub_mem (hPW hv) (hPW hu)), norm_sub_rev,
      ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hmeas : ∀ F : edges P, Measurable fun φ : ℝ => ENNReal.ofReal
      |⟪v F - u F, cos φ • (b 0 : EuclideanSpace ℝ (Fin d)) + sin φ • (b 1 : _)⟫| := by
    intro F
    exact (ENNReal.continuous_ofReal.comp (continuous_abs.comp
      (continuous_const.inner (by fun_prop)))).measurable
  rw [perimeter, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le (fun S => ?_)
  rw [← ENNReal.mul_le_mul_iff_right (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ⊤),
    Finset.mul_sum, Finset.sum_congr rfl (fun F _ => hdiam F),
    ← lintegral_finsetSum _ (fun F _ => hmeas F)]
  calc ∫⁻ φ in Set.Ioc 0 (2 * π), ∑ F ∈ S, ENNReal.ofReal
        |⟪v F - u F, cos φ • (b 0 : EuclideanSpace ℝ (Fin d)) + sin φ • (b 1 : _)⟫|
      ≤ ∫⁻ φ in Set.Ioc 0 (2 * π), 2 * ENNReal.ofReal
          ((1 + ⨆ j, |⟪cos φ • (b 0 : EuclideanSpace ℝ (Fin d)) + sin φ • (b 1 : _),
            a j - abar j⟫|) -
           -(1 + ⨆ j, |⟪cos φ • (b 0 : EuclideanSpace ℝ (Fin d)) + sin φ • (b 1 : _),
            a j - abar j⟫|)) := by
        refine lintegral_mono (fun φ => ?_)
        exact FSCross.proj_sum_le W hW hPW (hwW φ) u v huv hinj _ _
          (fun x hx => (abs_le.1 (hbd φ x hx)).1) (fun x hx => (abs_le.1 (hbd φ x hx)).2) S
    _ = 4 * ∫⁻ φ in Set.Ioc 0 (2 * π), ENNReal.ofReal (1 + ⨆ i,
          |⟪cos φ • (b 0 : EuclideanSpace ℝ (Fin d)) + sin φ • (b 1 : _), a i - abar i⟫|) := by
        rw [← lintegral_const_mul' 4 _ (by norm_num)]
        refine lintegral_congr (fun φ => ?_)
        rw [sub_neg_eq_add, ← two_mul, ENNReal.ofReal_mul (by norm_num), ← mul_assoc]
        norm_num

theorem dens_prob {μ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsDensity μ) :
    IsProbabilityMeasure (densityMeasure μ) := by
  constructor
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal h.2.1 (ae_of_all _ h.1), h.2.2, ENNReal.ofReal_one]

/-- O2: `E[perimeter(Q ∩ W)] ≤ 2π(1 + 2r)`. -/
theorem perimeter_lintegral_le (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hW : Module.finrank ℝ W = 2) (μ : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (hμ : ∀ i, IsDensity (μ i)) (abar : Fin n → EuclideanSpace ℝ (Fin d))
    (habar : ∀ i, ‖abar i‖ ≤ 1) (r : ℝ) (hr0 : 0 ≤ r)
    (hr : ∀ i, NthDeviationLE (μ i) (abar i) n r) :
    ∫⁻ a, perimeter (polygon W a) ∂(rowLaw μ) ≤ ENNReal.ofReal (2 * π * (1 + 2 * r)) := by
  have hp : ∀ i, IsProbabilityMeasure (densityMeasure (μ i)) := fun i => dens_prob (hμ i)
  have : IsProbabilityMeasure (rowLaw μ) := by unfold rowLaw; infer_instance
  let b : OrthonormalBasis (Fin 2) ℝ W := (stdOrthonormalBasis ℝ W).reindex (finCongr hW)
  set G : (Fin n → EuclideanSpace ℝ (Fin d)) → ℝ → ℝ≥0∞ := fun a φ =>
    1 + ⨆ i, ENNReal.ofReal
      |⟪cos φ • (b 0 : EuclideanSpace ℝ (Fin d)) + sin φ • (b 1 : _), a i - abar i⟫| with hG
  have hstep1 : ∀ a, perimeter (polygon W a) ≤ ∫⁻ φ in Set.Ioc 0 (2 * π), G a φ := by
    intro a
    refine (perimeter_le W hW b a abar habar).trans (lintegral_mono (fun φ => ?_))
    refine (ENNReal.ofReal_add_le).trans ?_
    rw [ENNReal.ofReal_one]
    refine add_le_add le_rfl ?_
    rcases isEmpty_or_nonempty (Fin n) with hn | hn
    · rw [Real.iSup_of_isEmpty, ENNReal.ofReal_zero]
      positivity
    · obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i =>
        |⟪cos φ • (b 0 : EuclideanSpace ℝ (Fin d)) + sin φ • (b 1 : _), a i - abar i⟫|)
      rw [← hi]
      exact le_iSup (fun i => ENNReal.ofReal
        |⟪cos φ • (b 0 : EuclideanSpace ℝ (Fin d)) + sin φ • (b 1 : _), a i - abar i⟫|) i
  have hGm : Measurable (Function.uncurry G) := by
    show Measurable fun p : (Fin n → EuclideanSpace ℝ (Fin d)) × ℝ => 1 + ⨆ i, ENNReal.ofReal
      |⟪cos p.2 • (b 0 : EuclideanSpace ℝ (Fin d)) + sin p.2 • (b 1 : _), p.1 i - abar i⟫|
    refine Measurable.const_add (Measurable.iSup fun i => ?_) 1
    exact (ENNReal.continuous_ofReal.comp (continuous_abs.comp (by fun_prop))).measurable
  have hstep3 : ∀ φ : ℝ, ∫⁻ a, G a φ ∂(rowLaw μ) ≤ 1 + ENNReal.ofReal (2 * r) := by
    intro φ
    rw [hG, lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    gcongr
    exact FSLib19.max_dev_le (rowLaw μ) (fun i a => a i) (fun i => measurable_pi_apply i) μ
      (fun i => (measurePreserving_eval (μ := fun i => densityMeasure (μ i)) i).map_eq) abar r hr
      _ (FSAngle.norm_dir W b φ)
  calc ∫⁻ a, perimeter (polygon W a) ∂(rowLaw μ)
      ≤ ∫⁻ a, (∫⁻ φ in Set.Ioc 0 (2 * π), G a φ) ∂(rowLaw μ) := lintegral_mono hstep1
    _ = ∫⁻ φ in Set.Ioc 0 (2 * π), ∫⁻ a, G a φ ∂(rowLaw μ) :=
        lintegral_lintegral_swap hGm.aemeasurable
    _ ≤ ∫⁻ φ in Set.Ioc 0 (2 * π), (1 + ENNReal.ofReal (2 * r)) := lintegral_mono hstep3
    _ = ENNReal.ofReal (2 * π * (1 + 2 * r)) := by
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add (by norm_num) (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end FSPerim
end SecPerim

-- ===== theorem_22 assembly (relay 12) =====
namespace FSFinal22
open FriendlyShadow.Gaussian

lemma key_arith {d : ℕ} (hd : 3 ≤ d) (L τ R r : ℝ) (hL : 0 < L) (hτ : 0 < τ) (hR : 0 ≤ R) :
    (1 / 2) * (Real.exp (-2) / ((d : ℝ) * L * (1 + R))) * (τ / (2 * Real.sqrt d)) *
      (2 + 8 * Real.pi * Real.exp 2 * ((d : ℝ) * Real.sqrt d) * (L / τ) * (1 + R) * (1 + 4 * r)) =
    2 * ((1 / 2) * (Real.exp (-2) / ((d : ℝ) * L * (1 + R))) * (τ / (2 * Real.sqrt d))) +
      2 * Real.pi * (1 + 4 * r) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 hd0
  have he : Real.exp (-2) = 1 / Real.exp 2 := by rw [Real.exp_neg]; ring
  have he2 : 0 < Real.exp 2 := Real.exp_pos 2
  have hR1 : 0 < 1 + R := by linarith
  rw [he]
  field_simp
  ring

end FSFinal22

open MeasureTheory FriendlyShadow.Gaussian ENNReal in
theorem solution {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hW : Module.finrank ℝ W = 2)
    (μ : Fin n → EuclideanSpace ℝ (Fin d) → ℝ) (hμ : ∀ i, IsDensity (μ i))
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (hmean : ∀ i, HasMean (μ i) (abar i))
    (habar : ∀ i, ‖abar i‖ ≤ 1) (L τ R r : ℝ) (hL : 0 < L) (hτ : 0 < τ) (hR : 0 ≤ R)
    (hr : 0 ≤ r) (hLL : ∀ i, LogLipschitz (μ i) L) (hLV : ∀ i, LineVarianceGE (μ i) τ)
    (hCR : ∀ i, CutoffRadiusLE (μ i) (abar i) (cutoffLevel n d) R)
    (hND : ∀ i, NthDeviationLE (μ i) (abar i) n r) :
    AEMeasurable (fun a => (edgeCount (polygon W a) : ℝ≥0∞)) (rowLaw μ) ∧
    ∫⁻ a, (edgeCount (polygon W a) : ℝ≥0∞) ∂(rowLaw μ) ≤
      ENNReal.ofReal (2 + 8 * Real.pi * Real.exp 2 * ((d : ℝ) * Real.sqrt d) * (L / τ) *
        (1 + R) * (1 + 4 * r)) := by
  refine ⟨(C5747Cnt2.measurable_edgeCount (n := n) W).aemeasurable, ?_⟩
  set c : ℝ := (1 / 2) * (Real.exp (-2) / ((d : ℝ) * L * (1 + R))) * (τ / (2 * Real.sqrt d)) with hcdef
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hR1 : 0 < 1 + R := by linarith
  have hc : 0 < c := by
    have := Real.sqrt_pos.2 hd0
    have := Real.exp_pos (-2)
    positivity
  have hm : ∀ I : Finset (Fin n), I.card = d →
      ENNReal.ofReal (2 / (n.choose d : ℝ)) ≤ rowLaw μ {a | edgeEvent W a I} →
      ENNReal.ofReal c * rowLaw μ {a | edgeEvent W a I} ≤
        ∫⁻ a in {a | edgeEvent W a I}, edgeLen W a I ∂(rowLaw μ) :=
    fun I hI hB => FSC8.elb_of_meas hd hdn W hW μ hμ abar hmean habar L τ R hL hτ hR hLL hLV hCR
      I hI hB (FSELM.meas_edgeLen W I)
  have h25 := FSO1.lemma25_full hd hdn W hW μ _ hm
  have hP := FSPerim.perimeter_lintegral_le W hW μ hμ abar habar r hr hND
  have hT := FSFinal22.key_arith hd L τ R r hL hτ hR
  rw [← hcdef] at hT
  have hbound : ENNReal.ofReal c * ∫⁻ a, (edgeCount (polygon W a) : ℝ≥0∞) ∂(rowLaw μ) ≤
      ENNReal.ofReal c * ENNReal.ofReal (2 + 8 * Real.pi * Real.exp 2 * ((d : ℝ) * Real.sqrt d) *
        (L / τ) * (1 + R) * (1 + 4 * r)) := by
    rw [← ENNReal.ofReal_mul hc.le, hT]
    refine h25.trans ?_
    have h2c : 2 * ENNReal.ofReal c = ENNReal.ofReal (2 * c) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    rw [h2c, ENNReal.ofReal_add (by positivity) (by positivity)]
    gcongr
    refine hP.trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [Real.pi_pos]
  exact (ENNReal.mul_le_mul_iff_right (by simpa using hc) ENNReal.ofReal_ne_top).1 hbound
