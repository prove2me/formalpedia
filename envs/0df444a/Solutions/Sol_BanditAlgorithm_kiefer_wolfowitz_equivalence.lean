-- Prove2me | solution 1 for BanditAlgorithm.kiefer_wolfowitz_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T13:54:33.760973+00:00
-- url     : https://prove2.me/submissions/fb5cd49f-3cf0-4add-8a08-434b3f76a58c

import Mathlib
import Definitions.Def_SelfNormalizedProcess

/- Source: Basic.lean; SHA256: da330a17ef5b3dc66a756d3187437a90093442502650b50ccf5d0f8ecd3115c6 -/
section BundledSource0

open Matrix Set MeasureTheory

namespace KieferWolfowitz

def rankOne (d : ℕ) (a : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.vecMulVec a a

def momentBody (d : ℕ) (A : Set (Fin d → ℝ)) : Set (Matrix (Fin d) (Fin d) ℝ) :=
  convexHull ℝ (rankOne d '' A)

end KieferWolfowitz
end BundledSource0

/- Source: Geometry.lean; SHA256: ff976337d9d6980cb84760168ce229960fdc90e38786a64cac40ddb9443f73ca -/
section BundledSource1

open Matrix Set MeasureTheory

namespace KieferWolfowitz

theorem isCompact_convexHull_real {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [FiniteDimensional ℝ E] {s : Set E} (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  classical
  let F (n : ℕ) (p : (Fin n → ℝ) × (Fin n → E)) : E :=
    ∑ i, p.1 i • p.2 i
  let K (n : ℕ) : Set ((Fin n → ℝ) × (Fin n → E)) :=
    stdSimplex ℝ (Fin n) ×ˢ Set.pi Set.univ (fun _ => s)
  have hK (n : ℕ) : IsCompact (K n) :=
    (isCompact_stdSimplex ℝ (Fin n)).prod (isCompact_univ_pi (fun _ => hs))
  have hF (n : ℕ) : Continuous (F n) := by unfold F; fun_prop
  have heq : convexHull ℝ s = ⋃ n : Fin (Module.finrank ℝ E + 2), F n.val '' K n.val := by
    apply Set.Subset.antisymm
    · intro x hx
      let t := Caratheodory.minCardFinsetOfMemConvexHull hx
      have ht : (t : Set E) ⊆ s := Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
      have hx' : x ∈ convexHull ℝ (t : Set E) := Caratheodory.mem_minCardFinsetOfMemConvexHull hx
      have hind : AffineIndependent ℝ ((↑) : t → E) :=
        Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
      have hcard : t.card ≤ Module.finrank ℝ E + 1 := by
        simpa using hind.card_le_finrank_succ.trans
          (Nat.add_le_add_right (Submodule.finrank_le _) 1)
      let e : Fin t.card ≃ t := t.equivFin.symm
      rw [Finset.convexHull_eq] at hx'
      obtain ⟨w, hw, hsum, hx'⟩ := hx'
      have hsum' : ∑ i : Fin t.card, w (e i) = 1 := by
        rw [e.sum_comp (fun a : t => w a), Finset.sum_coe_sort]
        exact hsum
      have hpoint : F t.card ((fun i => w (e i)), fun i => (e i : E)) = x := by
        dsimp [F]
        rw [e.sum_comp (fun a : t => w a • (a : E)),
          Finset.sum_coe_sort t (fun a : E => w a • a)]
        simpa [Finset.centerMass_eq_of_sum_1 _ _ hsum] using hx'
      refine Set.mem_iUnion.mpr ⟨⟨t.card, by omega⟩, ?_⟩
      refine ⟨((fun i => w (e i)), fun i => (e i : E)), ?_, hpoint⟩
      exact ⟨⟨fun i => hw (e i) (e i).property, hsum'⟩,
        fun i _ => ht (e i).property⟩
    · intro x hx
      obtain ⟨n, p, hp, rfl⟩ := Set.mem_iUnion.mp hx
      exact (convex_convexHull ℝ s).sum_mem (fun i _ => hp.1.1 i) hp.1.2
        (fun i _ => subset_convexHull ℝ s (hp.2 i (Set.mem_univ _)))
  rw [heq]
  exact isCompact_iUnion (fun n => (hK n.val).image (hF n.val))

theorem continuous_rankOne (d : ℕ) : Continuous (rankOne d) := by
  unfold rankOne Matrix.vecMulVec
  fun_prop

theorem convex_momentBody (d : ℕ) (A : Set (Fin d → ℝ)) :
    Convex ℝ (momentBody d A) := convex_convexHull _ _

theorem isCompact_momentBody {d : ℕ} {A : Set (Fin d → ℝ)} (hA : IsCompact A) :
    IsCompact (momentBody d A) := by
  unfold momentBody
  apply isCompact_convexHull_real
  exact hA.image (continuous_rankOne d)

theorem rankOne_posSemidef {d : ℕ} (a : Fin d → ℝ) : (rankOne d a).PosSemidef := by
  simpa [rankOne] using Matrix.posSemidef_vecMulVec_self_star a

theorem posSemidef_of_mem_momentBody {d : ℕ} {A : Set (Fin d → ℝ)}
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : M ∈ momentBody d A) : M.PosSemidef := by
  have hconv : Convex ℝ {M : Matrix (Fin d) (Fin d) ℝ | M.PosSemidef} := by
    intro M hM N hN a b ha hb _
    exact (hM.smul ha).add (hN.smul hb)
  exact convexHull_min (by rintro _ ⟨a, _, rfl⟩; exact rankOne_posSemidef a) hconv hM

theorem quadraticForm_rankOne {d : ℕ} (a x : Fin d → ℝ) :
    x ⬝ᵥ (rankOne d a) *ᵥ x = (a ⬝ᵥ x) ^ 2 := by
  simp [rankOne, Matrix.vecMulVec_mulVec, dotProduct_smul, dotProduct_comm, pow_two]

theorem exists_posDef_mem_momentBody {d : ℕ} (hd : 0 < d)
    {A : Set (Fin d → ℝ)} (hspan : Submodule.span ℝ A = ⊤) :
    ∃ M ∈ momentBody d A, M.PosDef := by
  classical
  obtain ⟨t, ht, htcard, htspan, _⟩ := Submodule.exists_finset_span_eq_linearIndepOn ℝ A
  have htd : t.card = d := by
    rw [hspan] at htcard
    simpa using htcard
  have htpos : 0 < (t.card : ℝ) := by exact_mod_cast htd ▸ hd
  have hsp : Submodule.span ℝ (t : Set (Fin d → ℝ)) = ⊤ := htspan.trans hspan
  let M : Matrix (Fin d) (Fin d) ℝ := ∑ a ∈ t, rankOne d a
  have hMsemi : M.PosSemidef := Matrix.posSemidef_sum t (fun a _ => rankOne_posSemidef a)
  have hM : M.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hMsemi.isHermitian
    intro x hx
    have hex : ∃ a ∈ t, a ⬝ᵥ x ≠ 0 := by
      by_contra! hn
      have horth : ∀ y ∈ Submodule.span ℝ (t : Set (Fin d → ℝ)), y ⬝ᵥ x = 0 := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem a ha => exact hn a ha
        | zero => simp
        | add a b _ _ ha hb => simp [add_dotProduct, ha, hb]
        | smul c a _ ha => simp [smul_dotProduct, ha]
      exact hx (dotProduct_self_eq_zero.mp (horth x (hsp ▸ Submodule.mem_top)))
    have hpos : 0 < ∑ a ∈ t, (a ⬝ᵥ x) ^ 2 := by
      obtain ⟨a, ha, hax⟩ := hex
      exact Finset.sum_pos' (fun a _ => sq_nonneg _) ⟨a, ha, sq_pos_of_ne_zero hax⟩
    simpa [M, Matrix.sum_mulVec, dotProduct_sum, quadraticForm_rankOne] using hpos
  let r : ℝ := (t.card : ℝ)⁻¹
  have hr : 0 < r := inv_pos.mpr htpos
  refine ⟨r • M, ?_, hM.smul hr⟩
  have hsum : ∑ _a ∈ t, r = 1 := by simp [r, htpos.ne']
  have hmem := (convex_momentBody d A).sum_mem (fun _ _ => hr.le) hsum
    (fun a ha => subset_convexHull ℝ (rankOne d '' A) ⟨a, ht ha, rfl⟩)
  simpa [M, Finset.smul_sum] using hmem

theorem exists_det_maximizer {d : ℕ} (hd : 0 < d)
    {A : Set (Fin d → ℝ)} (hA : IsCompact A) (hspan : Submodule.span ℝ A = ⊤) :
    ∃ M ∈ momentBody d A, M.PosDef ∧
      ∀ N ∈ momentBody d A, N.det ≤ M.det := by
  obtain ⟨V, hV, hVpd⟩ := exists_posDef_mem_momentBody hd hspan
  have hcont : Continuous (fun N : Matrix (Fin d) (Fin d) ℝ => N.det) :=
    continuous_id.matrix_det
  obtain ⟨M, hM, hmax⟩ := (isCompact_momentBody hA).exists_isMaxOn ⟨V, hV⟩
    hcont.continuousOn
  refine ⟨M, hM, ?_, fun N hN => hmax hN⟩
  apply (posSemidef_of_mem_momentBody hM).posDef_iff_det_ne_zero.mpr
  exact ne_of_gt (lt_of_lt_of_le hVpd.det_pos (hmax hV))

end KieferWolfowitz
end BundledSource1

/- Source: Moments.lean; SHA256: 3b67394f0d34f9465dae7051ef26c7e8fddab70e4962599e37a9e4c930434df5 -/
section BundledSource2

open Matrix Set MeasureTheory
open scoped BigOperators

namespace KieferWolfowitz

open BanditAlgorithm

variable {d : ℕ} {A : Set (Fin d → ℝ)} {π : Measure (Fin d → ℝ)}

theorem ae_mem_of_isDesignOn (hπ : IsDesignOn d A π) : ∀ᵐ a ∂π, a ∈ A :=
  ae_iff.mpr hπ.2

theorem integrable_on_design (hA : IsCompact A) (hπ : IsDesignOn d A π)
    {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) : Integrable f π := by
  let : IsProbabilityMeasure π := hπ.1
  have h := hf.continuousOn.integrableOn_compact (μ := π) hA
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (ae_mem_of_isDesignOn hπ)] at h

theorem integrable_designMatrix_entry (hA : IsCompact A) (hπ : IsDesignOn d A π)
    (i j : Fin d) : Integrable (fun a : Fin d → ℝ => a i * a j) π :=
  integrable_on_design hA hπ (by fun_prop)

theorem designMatrix_isSymm (π : Measure (Fin d → ℝ)) :
    (designMatrix d π).IsSymm := by
  ext i j
  simp [designMatrix, mul_comm]

private theorem integral_sum_moments (hA : IsCompact A) (hπ : IsDesignOn d A π)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    (∫ a, ∑ i, ∑ j, M i j * (a i * a j) ∂π) =
      ∑ i, ∑ j, M i j * designMatrix d π i j := by
  rw [integral_finsetSum _ (fun i _ =>
    integrable_on_design hA hπ (by fun_prop))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ =>
    (integrable_designMatrix_entry hA hπ i j).const_mul (M i j))]
  simp only [integral_const_mul, designMatrix, of_apply]

theorem integral_quadraticForm (hA : IsCompact A) (hπ : IsDesignOn d A π)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    (∫ a, a ⬝ᵥ (M *ᵥ a) ∂π) = trace (M * designMatrix d π) := by
  calc
    (∫ a, a ⬝ᵥ (M *ᵥ a) ∂π) =
        ∫ a, ∑ i, ∑ j, M i j * (a i * a j) ∂π := by
      apply integral_congr_ae
      filter_upwards [] with a
      simp only [dotProduct, mulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i, ∑ j, M i j * designMatrix d π i j :=
      integral_sum_moments hA hπ M
    _ = trace (M * designMatrix d π) := by
      simp only [trace, diag, mul_apply]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      simpa only [transpose_apply] using
        congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M j i) (designMatrix_isSymm π).eq

theorem quadraticForm_designMatrix (hA : IsCompact A) (hπ : IsDesignOn d A π)
    (x : Fin d → ℝ) :
    x ⬝ᵥ (designMatrix d π *ᵥ x) = ∫ a, (x ⬝ᵥ a) ^ 2 ∂π := by
  calc
    x ⬝ᵥ (designMatrix d π *ᵥ x) =
        ∑ i, ∑ j, (x i * x j) * designMatrix d π i j := by
      simp only [dotProduct, mulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∫ a, ∑ i, ∑ j, (x i * x j) * (a i * a j) ∂π :=
      (integral_sum_moments hA hπ (Matrix.vecMulVec x x)).symm
    _ = ∫ a, (x ⬝ᵥ a) ^ 2 ∂π := by
      apply integral_congr_ae
      filter_upwards [] with a
      simp only [dotProduct, pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem designMatrix_posSemidef (hA : IsCompact A) (hπ : IsDesignOn d A π) :
    (designMatrix d π).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simpa only [star_trivial, Matrix.transpose_apply] using
      congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M i j) (designMatrix_isSymm π).eq
  · intro x
    simpa only [star_trivial, quadraticForm_designMatrix hA hπ] using
      (integral_nonneg (fun a => sq_nonneg (x ⬝ᵥ a)) :
        0 ≤ ∫ a, (x ⬝ᵥ a) ^ 2 ∂π)

theorem integral_inverse_quadraticForm (hA : IsCompact A) (hπ : IsDesignOn d A π)
    (hpd : (designMatrix d π).PosDef) :
    (∫ a, a ⬝ᵥ ((designMatrix d π)⁻¹ *ᵥ a) ∂π) = (d : ℝ) := by
  rw [integral_quadraticForm hA hπ,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit)]
  simp

theorem dim_le_designGValue (hA : IsCompact A) (hπ : IsDesignOn d A π)
    (hpd : (designMatrix d π).PosDef) :
    (d : ℝ) ≤ designGValue d A π := by
  let : IsProbabilityMeasure π := hπ.1
  let f : (Fin d → ℝ) → ℝ := fun a => a ⬝ᵥ ((designMatrix d π)⁻¹ *ᵥ a)
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have hbdd : BddAbove (f '' A) := (hA.image hf).bddAbove
  have hle : ∀ᵐ a ∂π, f a ≤ designGValue d A π := by
    filter_upwards [ae_mem_of_isDesignOn hπ] with a ha
    exact le_csSup hbdd (mem_image_of_mem f ha)
  have hi := integral_mono_ae (integrable_on_design hA hπ hf)
    (integrable_const (designGValue d A π)) hle
  simpa only [f, integral_inverse_quadraticForm hA hπ hpd,
    integral_const, probReal_univ, smul_eq_mul, one_mul] using hi

end KieferWolfowitz
end BundledSource2

/- Source: MatrixBound.lean; SHA256: 79ef4fce4603381177590edc78be763d5b1b30c7bd861ad10cf71b247878cd64 -/
section BundledSource3

open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace KieferWolfowitz

theorem det_le_one_of_trace_le_card {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosSemidef) (htrace : Matrix.trace A ≤ (d : ℝ)) : A.det ≤ 1 := by
  have hsum : ∑ i, hA.isHermitian.eigenvalues i ≤ (d : ℝ) := by
    simpa [hA.isHermitian.trace_eq_sum_eigenvalues] using htrace
  calc
    A.det = ∏ i, hA.isHermitian.eigenvalues i := by
      simpa using hA.isHermitian.det_eq_prod_eigenvalues
    _ ≤ ∏ i, Real.exp (hA.isHermitian.eigenvalues i - 1) := by
      apply Finset.prod_le_prod
      · intro i _
        exact hA.eigenvalues_nonneg i
      · intro i _
        simpa using Real.add_one_le_exp (hA.isHermitian.eigenvalues i - 1)
    _ = Real.exp (∑ i, (hA.isHermitian.eigenvalues i - 1)) :=
      (Real.exp_sum Finset.univ _).symm
    _ ≤ Real.exp 0 := by
      apply Real.exp_le_exp.mpr
      simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one] using sub_nonpos.mpr hsum
    _ = 1 := Real.exp_zero

theorem det_le_of_trace_inv_mul_le {d : ℕ} (M N : Matrix (Fin d) (Fin d) ℝ)
    (hM : M.PosDef) (hN : N.PosSemidef)
    (htrace : Matrix.trace (M⁻¹ * N) ≤ (d : ℝ)) : N.det ≤ M.det := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.posSemidef.inv.nonneg
  have hfactor : M⁻¹ = B.conjTranspose * B := by
    simpa only [Matrix.star_eq_conjTranspose] using hB
  let Q := B * N * B.conjTranspose
  have hQ : Q.PosSemidef := hN.mul_mul_conjTranspose_same B
  have hQtrace : Matrix.trace Q = Matrix.trace (M⁻¹ * N) := by
    dsimp [Q]
    rw [Matrix.trace_mul_cycle, ← hfactor]
  have hQdet : Q.det = N.det / M.det := by
    calc
      Q.det = (B.conjTranspose * B).det * N.det := by
        dsimp [Q]
        simp only [Matrix.det_mul]
        ring
      _ = (M⁻¹).det * N.det := by rw [← hfactor]
      _ = N.det / M.det := by
        rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
        ring
  apply (div_le_one hM.det_pos).mp
  rw [← hQdet]
  exact det_le_one_of_trace_le_card Q hQ (hQtrace.trans_le htrace)

end KieferWolfowitz
end BundledSource3

/- Source: Variation.lean; SHA256: 078e6846256920e3baf923cbcca7d59608b8d164c627b701d1645f9762d4b7a1 -/
section BundledSource4

namespace KieferWolfowitz

open Matrix

theorem hasDerivAt_det_one_add_smul {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • A).det) A.trace 0 := by
  let p : Polynomial ℝ := (1 + (Polynomial.X : Polynomial ℝ) • A.map Polynomial.C).det
  have heval (t : ℝ) : p.eval t = (1 + t • A).det := by
    change (Polynomial.evalRingHom t) _ = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    change Polynomial.eval t
      ((if i = j then 1 else 0) + Polynomial.X * Polynomial.C (A i j)) =
        (if i = j then 1 else 0) + t * A i j
    by_cases hij : i = j <;> simp [hij] <;> ring
  have hd : p.derivative.eval 0 = A.trace :=
    Matrix.derivative_det_one_add_X_smul A
  simpa only [heval, hd] using p.hasDerivAt (0 : ℝ)

theorem hasDerivAt_det_add_smul {d : ℕ} (M N : Matrix (Fin d) (Fin d) ℝ)
    (hM : IsUnit M.det) :
    HasDerivAt (fun t : ℝ => (M + t • N).det)
      (M.det * (M⁻¹ * N).trace) 0 := by
  have hfactor (t : ℝ) : (M + t • N).det = M.det * (1 + t • (M⁻¹ * N)).det := by
    rw [← Matrix.det_mul]
    congr 1
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
      Matrix.mul_nonsing_inv_cancel_left M N hM]
  simpa only [← hfactor] using (hasDerivAt_det_one_add_smul (M⁻¹ * N)).const_mul M.det

theorem trace_inv_mul_le_of_det_segment_max {d : ℕ}
    (M N : Matrix (Fin d) (Fin d) ℝ) (hM : M.PosDef)
    (hmax : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((1 - t) • M + t • N).det ≤ M.det) :
    (M⁻¹ * N).trace ≤ (d : ℝ) := by
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hM.det_pos.ne'
  let f : ℝ → ℝ := fun t => (M + t • (N - M)).det
  have hf : HasDerivAt f (M.det * ((M⁻¹ * N).trace - d)) 0 := by
    simpa [f, Matrix.mul_sub, Matrix.trace_sub, Matrix.nonsing_inv_mul M hunit,
      Matrix.trace_one] using hasDerivAt_det_add_smul M (N - M) hunit
  have hlocal : IsMaxOn f (Set.Icc 0 1) 0 := by
    intro t ht
    have heq : M + t • (N - M) = (1 - t) • M + t • N := by module
    simpa [f, heq] using hmax t ht
  have htangent : (1 : ℝ) ∈ posTangentConeAt (Set.Icc 0 1) 0 := by
    apply mem_posTangentConeAt_of_segment_subset
    simpa only [zero_add, segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)]
      using (Set.Subset.rfl : Set.Icc (0 : ℝ) 1 ⊆ Set.Icc 0 1)
  have hnonpos := hlocal.localize.hasFDerivWithinAt_nonpos
    hf.hasFDerivAt.hasFDerivWithinAt htangent
  have hmul : M.det * ((M⁻¹ * N).trace - d) ≤ 0 := by simpa using hnonpos
  nlinarith [hM.det_pos]

end KieferWolfowitz

end BundledSource4

/- Source: DesignBody.lean; SHA256: ddd76c9d96b679549e3432c1d218e30937613d5c4c924eb117fa5aa2021518c4 -/
section BundledSource5

open Matrix Set MeasureTheory
open scoped BigOperators

noncomputable section

namespace KieferWolfowitz

open BanditAlgorithm

variable {d : ℕ} {A : Set (Fin d → ℝ)} {π : Measure (Fin d → ℝ)}

local instance : NormedAddCommGroup (Matrix (Fin d) (Fin d) ℝ) := Matrix.normedAddCommGroup
local instance : NormedSpace ℝ (Matrix (Fin d) (Fin d) ℝ) := Matrix.normedSpace
local instance : ContinuousENorm (Matrix (Fin d) (Fin d) ℝ) :=
  inferInstanceAs (ContinuousENorm (Fin d → Fin d → ℝ))

theorem integrable_rankOne (hA : IsCompact A) (hπ : IsDesignOn d A π) :
    Integrable (rankOne d) π := by
  let : IsProbabilityMeasure π := hπ.1
  have h := (continuous_rankOne d).continuousOn.integrableOn_compact (μ := π) hA
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (ae_mem_of_isDesignOn hπ)] at h

theorem designMatrix_eq_integral_rankOne (hA : IsCompact A) (hπ : IsDesignOn d A π) :
    designMatrix d π = ∫ a, rankOne d a ∂π := by
  ext i j
  let ei : Matrix (Fin d) (Fin d) ℝ →L[ℝ] (Fin d → ℝ) := ContinuousLinearMap.proj i
  let eij : Matrix (Fin d) (Fin d) ℝ →L[ℝ] ℝ := (ContinuousLinearMap.proj j).comp ei
  change (∫ a, a i * a j ∂π) = (∫ a, rankOne d a ∂π) i j
  exact eij.integral_comp_comm (μ := π) (integrable_rankOne hA hπ)

theorem designMatrix_mem_momentBody (hA : IsCompact A) (hπ : IsDesignOn d A π) :
    designMatrix d π ∈ momentBody d A := by
  let : IsProbabilityMeasure π := hπ.1
  rw [designMatrix_eq_integral_rankOne hA hπ]
  apply (convex_momentBody d A).integral_mem (isCompact_momentBody hA).isClosed
  · filter_upwards [ae_mem_of_isDesignOn hπ] with a ha
    exact subset_convexHull ℝ (rankOne d '' A) (mem_image_of_mem (rankOne d) ha)
  · exact integrable_rankOne hA hπ

noncomputable def weightedDirac {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (a : ι → Fin d → ℝ) : Measure (Fin d → ℝ) :=
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac (a i)

theorem weightedDirac_compl_eq_zero {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (a : ι → Fin d → ℝ) {S : Set (Fin d → ℝ)}
    (ha : ∀ i, a i ∈ S) : weightedDirac w a Sᶜ = 0 := by
  classical
  simp only [weightedDirac, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i _
  simp [Measure.dirac_apply, ha i]

theorem isProbabilityMeasure_weightedDirac {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (a : ι → Fin d → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) : IsProbabilityMeasure (weightedDirac w a) := by
  constructor
  simp only [weightedDirac, Measure.finsetSum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i), hsum, ENNReal.ofReal_one]

theorem isDesignOn_weightedDirac {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (a : ι → Fin d → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (ha : ∀ i, a i ∈ A) :
    IsDesignOn d A (weightedDirac w a) :=
  ⟨isProbabilityMeasure_weightedDirac w a hw hsum, weightedDirac_compl_eq_zero w a ha⟩

theorem integral_weightedDirac {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (a : ι → Fin d → ℝ) (hw : ∀ i, 0 ≤ w i)
    (f : (Fin d → ℝ) → ℝ) :
    (∫ x, f x ∂weightedDirac w a) = ∑ i, w i * f (a i) := by
  rw [weightedDirac, integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw _),
      smul_eq_mul]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

theorem designMatrix_weightedDirac {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (a : ι → Fin d → ℝ) (hw : ∀ i, 0 ≤ w i) :
    designMatrix d (weightedDirac w a) = ∑ i, w i • rankOne d (a i) := by
  ext j k
  simpa [designMatrix, rankOne, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul] using
    integral_weightedDirac w a hw (fun x => x j * x k)

theorem weightedDirac_finite_support {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (a : ι → Fin d → ℝ) (ha : ∀ i, a i ∈ A) :
    ∃ s : Finset (Fin d → ℝ), ↑s ⊆ A ∧ s.card ≤ Fintype.card ι ∧
      weightedDirac w a ((↑s : Set (Fin d → ℝ))ᶜ) = 0 := by
  classical
  refine ⟨Finset.univ.image a, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact ha i
  · exact (Finset.card_image_le).trans_eq (Finset.card_univ)
  · exact weightedDirac_compl_eq_zero w a (fun i => Finset.mem_image.mpr ⟨i, by simp, rfl⟩)

theorem exists_designOn_of_mem_momentBody {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M ∈ momentBody d A) :
    ∃ π : Measure (Fin d → ℝ), IsDesignOn d A π ∧ designMatrix d π = M := by
  classical
  obtain ⟨ι, _, w, z, hw, hsum, hz, hMz⟩ := mem_convexHull_iff_exists_fintype.mp hM
  choose a ha haz using hz
  refine ⟨weightedDirac w a, isDesignOn_weightedDirac w a hw hsum ha, ?_⟩
  rw [designMatrix_weightedDirac w a hw]
  convert hMz using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [haz i]

theorem mem_momentBody_iff_exists_design (hA : IsCompact A)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    M ∈ momentBody d A ↔
      ∃ π : Measure (Fin d → ℝ), IsDesignOn d A π ∧ designMatrix d π = M := by
  constructor
  · exact exists_designOn_of_mem_momentBody
  · rintro ⟨π, hπ, rfl⟩
    exact designMatrix_mem_momentBody hA hπ

end KieferWolfowitz

end
end BundledSource5

/- Source: GValue.lean; SHA256: 487d1afedba27c0bbdf10c21d984dfb2acc6a3d956e4d5fc1251c4a85a87e3e6 -/
section BundledSource6

open Matrix Set MeasureTheory

namespace KieferWolfowitz

open BanditAlgorithm

variable {d : ℕ} {A : Set (Fin d → ℝ)} {π πs : Measure (Fin d → ℝ)}

theorem nonempty_of_isDesignOn (hπ : IsDesignOn d A π) : A.Nonempty := by
  let : IsProbabilityMeasure π := hπ.1
  by_contra h
  have hA : A = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  have hzero : (1 : ENNReal) = 0 := by simpa [hA] using hπ.2
  exact one_ne_zero hzero

theorem bddAbove_quadraticForm_image (hA : IsCompact A)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    BddAbove ((fun a => a ⬝ᵥ (M *ᵥ a)) '' A) :=
  (hA.image (by fun_prop)).bddAbove

theorem quadraticForm_le_designGValue (hA : IsCompact A)
    (π : Measure (Fin d → ℝ)) {a : Fin d → ℝ} (ha : a ∈ A) :
    a ⬝ᵥ ((designMatrix d π)⁻¹ *ᵥ a) ≤ designGValue d A π :=
  le_csSup (bddAbove_quadraticForm_image hA _) (mem_image_of_mem _ ha)

theorem designGValue_le_of_forall_le (hA : A.Nonempty) {C : ℝ}
    (h : ∀ a ∈ A, a ⬝ᵥ ((designMatrix d π)⁻¹ *ᵥ a) ≤ C) :
    designGValue d A π ≤ C := by
  apply csSup_le (hA.image _)
  rintro _ ⟨a, ha, rfl⟩
  exact h a ha

theorem designGValue_eq_zero_of_det_eq_zero (hA : A.Nonempty)
    (hdet : (designMatrix d π).det = 0) : designGValue d A π = 0 := by
  have hinv : (designMatrix d π)⁻¹ = 0 :=
    Matrix.nonsing_inv_apply_not_isUnit _ (by simp [hdet])
  simp only [designGValue, hinv, Matrix.zero_mulVec, dotProduct_zero]
  rw [hA.image_const, csSup_singleton]

theorem posDef_of_designGValue_eq (hd : 0 < d) (hA : IsCompact A)
    (hπ : IsDesignOn d A π) (hg : designGValue d A π = (d : ℝ)) :
    (designMatrix d π).PosDef := by
  apply (designMatrix_posSemidef hA hπ).posDef_iff_det_ne_zero.mpr
  intro hdet
  have hz := designGValue_eq_zero_of_det_eq_zero (nonempty_of_isDesignOn hπ) hdet
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  linarith

theorem isGOptimalDesign_of_designGValue_eq (hd : 0 < d) (hA : IsCompact A)
    (hπ : IsDesignOn d A π) (hg : designGValue d A π = (d : ℝ)) :
    IsGOptimalDesign d A π := by
  refine ⟨posDef_of_designGValue_eq hd hA hπ hg, ?_⟩
  intro ν hν hpd
  rw [hg]
  exact dim_le_designGValue hA hν hpd

theorem trace_inverse_mul_le_of_designGValue_eq (hA : IsCompact A)
    (hg : designGValue d A πs = (d : ℝ)) (hπ : IsDesignOn d A π) :
    trace ((designMatrix d πs)⁻¹ * designMatrix d π) ≤ (d : ℝ) := by
  let : IsProbabilityMeasure π := hπ.1
  have hle : ∀ᵐ a ∂π, a ⬝ᵥ ((designMatrix d πs)⁻¹ *ᵥ a) ≤ (d : ℝ) := by
    filter_upwards [ae_mem_of_isDesignOn hπ] with a ha
    exact (quadraticForm_le_designGValue hA πs ha).trans_eq hg
  have hi := integral_mono_ae
    (integrable_on_design hA hπ (show Continuous
      (fun a => a ⬝ᵥ ((designMatrix d πs)⁻¹ *ᵥ a)) by fun_prop))
    (integrable_const (d : ℝ)) hle
  simpa only [integral_quadraticForm hA hπ, integral_const,
    probReal_univ, smul_eq_mul, one_mul] using hi

theorem det_le_of_designGValue_eq (hd : 0 < d) (hA : IsCompact A)
    (hπs : IsDesignOn d A πs) (hg : designGValue d A πs = (d : ℝ))
    (hπ : IsDesignOn d A π) : (designMatrix d π).det ≤ (designMatrix d πs).det :=
  det_le_of_trace_inv_mul_le _ _
    (posDef_of_designGValue_eq hd hA hπs hg)
    (designMatrix_posSemidef hA hπ)
    (trace_inverse_mul_le_of_designGValue_eq hA hg hπ)

end KieferWolfowitz
end BundledSource6

/- Source: Support.lean; SHA256: bd35c346d6ed33427b2aa9c8d5d715864f30c174870c3552d5cb1ca6686e8144 -/
section BundledSource7

open Matrix
open scoped BigOperators

namespace KieferWolfowitz

def supportCoordinates (d : ℕ) (a : Fin d → ℝ) : Sym2 (Fin d) → ℝ :=
  Sym2.lift ⟨fun i j => a i * a j, fun i j => mul_comm (a i) (a j)⟩

def supportReconstruction (d : ℕ) :
    (Sym2 (Fin d) → ℝ) →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ where
  toFun q i j := q (Sym2.mk i j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem supportReconstruction_coordinates (d : ℕ) (a : Fin d → ℝ) :
    supportReconstruction d (supportCoordinates d a) = rankOne d a := rfl

theorem linearIndependent_of_affineIndependent_of_constant
    {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ι → E) (L : E →ₗ[ℝ] ℝ) (c : ℝ) (hc : c ≠ 0)
    (hp : AffineIndependent ℝ p) (hL : ∀ i, L (p i) = c) :
    LinearIndependent ℝ p := by
  rw [linearIndependent_iff']
  intro s w hw i hi
  have hsum : ∑ j ∈ s, w j = 0 := by
    have h := congrArg L hw
    simp only [map_sum, map_smul, smul_eq_mul, map_zero, hL] at h
    have hmul : (∑ j ∈ s, w j) * c = 0 := by
      simpa only [Finset.sum_mul] using h
    exact (mul_eq_zero.mp hmul).resolve_right hc
  apply hp s w hsum ?_ i hi
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hsum 0,
    Finset.weightedVSubOfPoint_apply]
  simpa only [vsub_eq_sub, sub_zero] using hw

theorem card_le_of_independent_rankOne {d : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → Fin d → ℝ)
    (h : LinearIndependent ℝ (fun i => rankOne d (a i))) :
    Fintype.card ι ≤ d * (d + 1) / 2 := by
  have hcoords : LinearIndependent ℝ (fun i => supportCoordinates d (a i)) := by
    apply LinearIndependent.of_comp (supportReconstruction d)
    simpa only [Function.comp_def, supportReconstruction_coordinates] using h
  have hcard := hcoords.fintype_card_le_finrank
  simpa [Module.finrank_fintype_fun_eq_card, Sym2.card, Nat.choose_two_right,
    Nat.mul_comm] using hcard

noncomputable def supportTrace (d : ℕ) (M : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] ℝ :=
  (Matrix.traceLinearMap (Fin d) ℝ ℝ).comp
    (LinearMap.mulLeft ℝ M⁻¹)

theorem supportTrace_rankOne (d : ℕ) (M : Matrix (Fin d) (Fin d) ℝ)
    (a : Fin d → ℝ) : supportTrace d M (rankOne d a) = a ⬝ᵥ M⁻¹ *ᵥ a := by
  change Matrix.trace (M⁻¹ * Matrix.vecMulVec a a) = _
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

theorem exists_small_contact_combination {d : ℕ} (hd : 0 < d)
    (A : Set (Fin d → ℝ)) (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : M.PosDef) (hmem : M ∈ momentBody d A)
    (hbound : ∀ a ∈ A, a ⬝ᵥ M⁻¹ *ᵥ a ≤ (d : ℝ)) :
    ∃ k : ℕ, k ≤ d * (d + 1) / 2 ∧
      ∃ (a : Fin k → Fin d → ℝ) (w : Fin k → ℝ),
        (∀ i, a i ∈ A) ∧ (∀ i, 0 < w i) ∧
        (∑ i, w i) = 1 ∧
        (∑ i, w i • rankOne d (a i)) = M ∧
        ∀ i, a i ⬝ᵥ M⁻¹ *ᵥ a i = (d : ℝ) := by
  classical
  obtain ⟨ι, inst, z, w, hz, hind, hw, hsum, hcombo⟩ :=
    eq_pos_convex_span_of_mem_convexHull hmem
  let : Fintype ι := inst
  have hzA (i : ι) : ∃ a ∈ A, rankOne d a = z i := hz ⟨i, rfl⟩
  choose a ha hza using hzA
  let L := supportTrace d M
  have hLM : L M = (d : ℝ) := by
    change Matrix.trace (M⁻¹ * M) = (d : ℝ)
    rw [Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr (ne_of_gt hM.det_pos)),
      Matrix.trace_one]
    simp
  have hLz (i : ι) : L (z i) ≤ (d : ℝ) := by
    change supportTrace d M (z i) ≤ _
    rw [← hza i, supportTrace_rankOne]
    exact hbound (a i) (ha i)
  have hLcombo : ∑ i, w i * L (z i) = (d : ℝ) := by
    calc
      ∑ i, w i * L (z i) = L (∑ i, w i • z i) := by simp
      _ = (d : ℝ) := by rw [hcombo, hLM]
  have hslack : ∑ i, w i * ((d : ℝ) - L (z i)) = 0 := by
    calc
      ∑ i, w i * ((d : ℝ) - L (z i)) =
          (∑ i, w i) * (d : ℝ) - ∑ i, w i * L (z i) := by
        simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
      _ = 0 := by rw [hsum, hLcombo]; ring
  have hcontact (i : ι) : L (z i) = (d : ℝ) := by
    have hnonneg : ∀ j ∈ Finset.univ, 0 ≤ w j * ((d : ℝ) - L (z j)) :=
      fun j _ => mul_nonneg (hw j).le (sub_nonneg.mpr (hLz j))
    have hi := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hslack i (Finset.mem_univ i)
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left (ne_of_gt (hw i)))).symm
  have hlin : LinearIndependent ℝ z :=
    linearIndependent_of_affineIndependent_of_constant z L (d : ℝ)
      (ne_of_gt (by exact_mod_cast hd)) hind hcontact
  have hcard : Fintype.card ι ≤ d * (d + 1) / 2 := by
    apply card_le_of_independent_rankOne a
    simpa only [hza] using hlin
  let k := Fintype.card ι
  let e : Fin k ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨k, hcard, a ∘ e, w ∘ e, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ha (e i)
  · intro i
    exact hw (e i)
  · exact (e.sum_comp w).trans hsum
  · calc
      ∑ i, (w ∘ e) i • rankOne d ((a ∘ e) i) =
          ∑ i, w i • rankOne d (a i) := by
        simpa only [Function.comp_apply] using
          e.sum_comp (fun i => w i • rankOne d (a i))
      _ = M := by simpa only [hza] using hcombo
  · intro i
    have hi := hcontact (e i)
    change supportTrace d M (z (e i)) = (d : ℝ) at hi
    rw [← hza (e i), supportTrace_rankOne] at hi
    exact hi

end KieferWolfowitz
end BundledSource7

/- Source: Optimality.lean; SHA256: 310fa628786d2633379466ff3dbf3872d284248e998d1b6463772138dc34ff9e -/
section BundledSource8

open Matrix Set MeasureTheory

namespace KieferWolfowitz

open BanditAlgorithm

variable {d : ℕ} {A : Set (Fin d → ℝ)} {π : Measure (Fin d → ℝ)}

theorem quadraticForm_le_dim_of_det_max
    {M : Matrix (Fin d) (Fin d) ℝ} (hmem : M ∈ momentBody d A) (hM : M.PosDef)
    (hmax : ∀ N ∈ momentBody d A, N.det ≤ M.det)
    {a : Fin d → ℝ} (ha : a ∈ A) : a ⬝ᵥ M⁻¹ *ᵥ a ≤ (d : ℝ) := by
  have ha' : rankOne d a ∈ momentBody d A :=
    subset_convexHull ℝ (rankOne d '' A) (mem_image_of_mem _ ha)
  have ht := trace_inv_mul_le_of_det_segment_max M (rankOne d a) hM (by
    intro t ht
    exact hmax _ ((convex_momentBody d A) hmem ha' (sub_nonneg.mpr ht.2) ht.1
      (by ring)))
  simpa only [rankOne, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec,
    dotProduct_comm] using ht

theorem designGValue_eq_of_det_maximizing_moment (hA : IsCompact A)
    (hπ : IsDesignOn d A π) (hpd : (designMatrix d π).PosDef)
    (hmax : ∀ N ∈ momentBody d A, N.det ≤ (designMatrix d π).det) :
    designGValue d A π = (d : ℝ) := by
  apply le_antisymm
  · apply designGValue_le_of_forall_le (nonempty_of_isDesignOn hπ)
    intro a ha
    exact quadraticForm_le_dim_of_det_max (designMatrix_mem_momentBody hA hπ) hpd hmax ha
  · exact dim_le_designGValue hA hπ hpd

theorem exists_design_GValue_eq (hd : 0 < d) (hA : IsCompact A)
    (hspan : Submodule.span ℝ A = ⊤) :
    ∃ π : Measure (Fin d → ℝ), IsDesignOn d A π ∧ designGValue d A π = (d : ℝ) := by
  obtain ⟨M, hM, hpd, hmax⟩ := exists_det_maximizer hd hA hspan
  obtain ⟨π, hπ, heq⟩ := exists_designOn_of_mem_momentBody hM
  refine ⟨π, hπ, designGValue_eq_of_det_maximizing_moment hA hπ ?_ ?_⟩
  · rwa [heq]
  · rwa [heq]

theorem designGValue_eq_of_det_max (hd : 0 < d) (hA : IsCompact A)
    (hspan : Submodule.span ℝ A = ⊤) (hπ : IsDesignOn d A π)
    (hmax : ∀ ν : Measure (Fin d → ℝ), IsDesignOn d A ν →
      (designMatrix d ν).det ≤ (designMatrix d π).det) :
    designGValue d A π = (d : ℝ) := by
  obtain ⟨ν, hν, hg⟩ := exists_design_GValue_eq hd hA hspan
  have hpos : 0 < (designMatrix d π).det :=
    lt_of_lt_of_le (posDef_of_designGValue_eq hd hA hν hg).det_pos (hmax ν hν)
  have hpd : (designMatrix d π).PosDef :=
    (designMatrix_posSemidef hA hπ).posDef_iff_det_ne_zero.mpr (ne_of_gt hpos)
  apply designGValue_eq_of_det_maximizing_moment hA hπ hpd
  intro M hM
  obtain ⟨ν, hν, heq⟩ := exists_designOn_of_mem_momentBody hM
  simpa only [heq] using hmax ν hν

theorem designGValue_eq_of_isGOptimalDesign (hd : 0 < d) (hA : IsCompact A)
    (hspan : Submodule.span ℝ A = ⊤) (hπ : IsDesignOn d A π)
    (hopt : IsGOptimalDesign d A π) : designGValue d A π = (d : ℝ) := by
  obtain ⟨ν, hν, hg⟩ := exists_design_GValue_eq hd hA hspan
  apply le_antisymm
  · exact (hopt.2 ν hν (posDef_of_designGValue_eq hd hA hν hg)).trans_eq hg
  · exact dim_le_designGValue hA hπ hopt.1

theorem exists_small_gOptimal (hd : 0 < d) (hA : IsCompact A)
    (hspan : Submodule.span ℝ A = ⊤) :
    ∃ πs : Measure (Fin d → ℝ), IsDesignOn d A πs ∧ IsGOptimalDesign d A πs ∧
      ∃ s : Finset (Fin d → ℝ), ↑s ⊆ A ∧ s.card ≤ d * (d + 1) / 2 ∧
        πs ((↑s : Set (Fin d → ℝ))ᶜ) = 0 := by
  obtain ⟨M, hM, hpd, hmax⟩ := exists_det_maximizer hd hA hspan
  have hbound : ∀ a ∈ A, a ⬝ᵥ M⁻¹ *ᵥ a ≤ (d : ℝ) :=
    fun _ ha => quadraticForm_le_dim_of_det_max hM hpd hmax ha
  obtain ⟨k, hk, a, w, ha, hw, hsum, hcombo, _⟩ :=
    exists_small_contact_combination hd A M hpd hM hbound
  let πs := weightedDirac w a
  have hπs : IsDesignOn d A πs :=
    isDesignOn_weightedDirac w a (fun i => (hw i).le) hsum ha
  have heq : designMatrix d πs = M := by
    change designMatrix d (weightedDirac w a) = M
    rw [designMatrix_weightedDirac w a (fun i => (hw i).le), hcombo]
  have hg : designGValue d A πs = (d : ℝ) := by
    apply designGValue_eq_of_det_maximizing_moment hA hπs
    · rwa [heq]
    · rwa [heq]
  obtain ⟨s, hs, hcard, hzero⟩ := weightedDirac_finite_support w a ha
  refine ⟨πs, hπs, isGOptimalDesign_of_designGValue_eq hd hA hπs hg, s, hs, ?_, hzero⟩
  exact (by simpa using hcard : s.card ≤ k).trans hk

end KieferWolfowitz
end BundledSource8

/- Source: Main.lean; SHA256: 7b667d34c6c4b6f604ee96f6c6de638355d91a8a50b8eafb5e268a5b5d6c2ce3 -/
section BundledSource9

open MeasureTheory Matrix KieferWolfowitz BanditAlgorithm

theorem solution
    {d : ℕ} (hd : 0 < d) (𝒜 : Set (Fin d → ℝ)) (h𝒜 : IsCompact 𝒜)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) :
    (∀ πs : Measure (Fin d → ℝ), IsDesignOn d 𝒜 πs →
      ((IsGOptimalDesign d 𝒜 πs ↔
          ∀ π : Measure (Fin d → ℝ), IsDesignOn d 𝒜 π →
            (designMatrix d π).det ≤ (designMatrix d πs).det) ∧
        (IsGOptimalDesign d 𝒜 πs ↔ designGValue d 𝒜 πs = (d : ℝ)))) ∧
    ∃ πs : Measure (Fin d → ℝ), IsDesignOn d 𝒜 πs ∧ IsGOptimalDesign d 𝒜 πs ∧
      ∃ s : Finset (Fin d → ℝ), ↑s ⊆ 𝒜 ∧ s.card ≤ d * (d + 1) / 2 ∧
        πs ((↑s : Set (Fin d → ℝ))ᶜ) = 0 := by
  refine ⟨?_, exists_small_gOptimal hd h𝒜 hspan⟩
  intro πs hπs
  have heq : IsGOptimalDesign d 𝒜 πs ↔ designGValue d 𝒜 πs = (d : ℝ) :=
    ⟨designGValue_eq_of_isGOptimalDesign hd h𝒜 hspan hπs,
      isGOptimalDesign_of_designGValue_eq hd h𝒜 hπs⟩
  refine ⟨⟨?_, ?_⟩, heq⟩
  · intro hopt π hπ
    exact det_le_of_designGValue_eq hd h𝒜 hπs (heq.mp hopt) hπ
  · intro hmax
    exact heq.mpr (designGValue_eq_of_det_max hd h𝒜 hspan hπs hmax)
end BundledSource9
