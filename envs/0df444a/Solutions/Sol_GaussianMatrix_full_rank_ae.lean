-- Prove2me | solution 1 for GaussianMatrix.full_rank_ae
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T03:22:06.40125+00:00
-- url     : https://prove2.me/submissions/c429298c-9a9a-4223-b246-4e205830c189

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem ae_ne_zero_mvPolynomial_fin (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    ∀ (n : ℕ) (f : MvPolynomial (Fin n) ℝ), f ≠ 0 →
      ∀ᵐ x ∂(Measure.pi fun _ : Fin n => μ), MvPolynomial.eval x f ≠ 0 := by
  intro n
  induction n with
  | zero =>
    intro f hf
    refine Filter.Eventually.of_forall fun x hx => hf ?_
    apply MvPolynomial.funext
    intro y
    have : y = x := Subsingleton.elim _ _
    subst this
    simpa using hx
  | succ n ih =>
    intro f hf
    set g := MvPolynomial.finSuccEquiv ℝ n f with hg
    have hg0 : g ≠ 0 := by
      intro h; apply hf
      exact (MvPolynomial.finSuccEquiv ℝ n).injective (by rw [← hg, h, map_zero])
    have hc : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg0
    have hih := ih g.leadingCoeff hc
    rw [ae_iff]
    simp only [ne_eq, not_not]
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0
    let T : Set (ℝ × (Fin n → ℝ)) :=
      {q | MvPolynomial.eval (Fin.cons q.1 q.2 : Fin (n+1) → ℝ) f = 0}
    have hT : MeasurableSet T := by
      have hcont : Continuous fun q : ℝ × (Fin n → ℝ) =>
          MvPolynomial.eval (Fin.cons q.1 q.2 : Fin (n+1) → ℝ) f := by
        apply (MvPolynomial.continuous_eval f).comp
        refine continuous_pi fun i => ?_
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using continuous_fst
        · simp only [Fin.cons_succ]; exact (continuous_apply j).comp continuous_snd
      exact hcont.measurable (measurableSet_singleton 0)
    have hpre : MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 ⁻¹' T =
        {x | MvPolynomial.eval x f = 0} := by
      ext x
      have hx : (Fin.cons (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 x).1
          (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 x).2 : Fin (n+1) → ℝ) = x := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [MeasurableEquiv.piFinSuccAbove_apply]
        · simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.tail]
      simp only [Set.mem_preimage, T, Set.mem_ofPred_eq]
      rw [hx]
    rw [← hpre, hmp.measure_preimage hT.nullMeasurableSet, Measure.prod_apply_symm hT]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hih] with s hs
    have hpoly : Polynomial.map (MvPolynomial.eval s) g ≠ 0 := by
      intro h0
      apply hs
      have := congrArg (fun q => Polynomial.coeff q g.natDegree) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at this
      exact this
    have hfin : ((fun y => (y, s)) ⁻¹' T).Finite := by
      refine (Polynomial.roots (Polynomial.map (MvPolynomial.eval s) g)).toFinset.finite_toSet.subset ?_
      intro y hy
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, T, MvPolynomial.eval_eq_eval_mv_eval'] at hy
      simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hpoly,
        Polynomial.IsRoot.def]
      exact hy
    simpa using hfin.measure_zero μ

/-- The zero set of a nonzero real polynomial in finitely many variables is null for a product of
copies of an atomless probability measure on `ℝ`. -/
theorem ae_ne_zero_mvPolynomial {ι : Type*} [Fintype ι] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (f : MvPolynomial ι ℝ) (hf : f ≠ 0) :
    ∀ᵐ x ∂(Measure.pi fun _ : ι => μ), MvPolynomial.eval x f ≠ 0 := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hg : MvPolynomial.rename e f ≠ 0 := by
    intro h; apply hf
    exact MvPolynomial.rename_injective e e.injective (by rw [h, map_zero])
  have h := ae_ne_zero_mvPolynomial_fin μ _ _ hg
  let T : (Fin (Fintype.card ι) → ℝ) → (ι → ℝ) := fun y i => y (e i)
  have hT : Measurable T := measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hmap : Measure.map T (Measure.pi fun _ => μ) = Measure.pi fun _ : ι => μ := by
    symm
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply hT (MeasurableSet.univ_pi hs)]
    have hpre : T ⁻¹' Set.univ.pi s = Set.univ.pi fun k => s (e.symm k) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_univ_pi, T]
      constructor
      · intro hy k; simpa using hy (e.symm k)
      · intro hy i; simpa using hy (e i)
    rw [hpre, Measure.pi_pi]
    exact Fintype.prod_equiv e.symm _ _ (fun _ => rfl)
  have hmeas : MeasurableSet {x : ι → ℝ | MvPolynomial.eval x f ≠ 0} :=
    ((MvPolynomial.continuous_eval f).measurable (measurableSet_singleton 0)).compl
  rw [← hmap, ae_map_iff hT.aemeasurable hmeas]
  filter_upwards [h] with y hy
  rw [MvPolynomial.eval_rename] at hy
  exact hy

theorem measurable_uncurry_matrix (p m : ℕ) :
    Measurable fun G : Fin p → Fin m → ℝ => fun ab : Fin p × Fin m => G ab.1 ab.2 :=
  measurable_pi_lambda _ fun ab => (measurable_pi_apply ab.2).comp (measurable_pi_apply ab.1)

/-- Flattening a standard Gaussian matrix gives i.i.d. standard Gaussians indexed by
`Fin p × Fin m`. -/
theorem gaussianMatrix_map_uncurry (p m : ℕ) :
    Measure.map (fun G : Fin p → Fin m → ℝ => fun ab : Fin p × Fin m => G ab.1 ab.2)
      (gaussianMatrix p m) = Measure.pi fun _ : Fin p × Fin m => gaussianReal 0 1 := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (measurable_uncurry_matrix p m) (MeasurableSet.univ_pi hs)]
  have hpre : (fun G : Fin p → Fin m → ℝ => fun ab : Fin p × Fin m => G ab.1 ab.2) ⁻¹'
      Set.univ.pi s = Set.univ.pi fun a => Set.univ.pi fun b => s (a, b) := by
    ext G
    simp only [Set.mem_preimage, Set.mem_univ_pi, Prod.forall]
  rw [hpre, gaussianMatrix, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

/-- A nonzero polynomial in the entries of a standard Gaussian matrix is almost surely nonzero. -/
theorem ae_ne_zero_of_mvPolynomial (p m : ℕ) (f : MvPolynomial (Fin p × Fin m) ℝ) (hf : f ≠ 0) :
    ∀ᵐ G ∂(gaussianMatrix p m), MvPolynomial.eval (fun ab => G ab.1 ab.2) f ≠ 0 := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have h := ae_ne_zero_mvPolynomial (gaussianReal 0 1) f hf
  rw [← gaussianMatrix_map_uncurry] at h
  exact ae_of_ae_map (measurable_uncurry_matrix p m).aemeasurable h

theorem eval_det_gram (p m : ℕ) (G : Fin p → Fin m → ℝ) :
    MvPolynomial.eval (fun ab : Fin p × Fin m => G ab.1 ab.2)
      (Matrix.mvPolynomialX (Fin p) (Fin m) ℝ * (Matrix.mvPolynomialX (Fin p) (Fin m) ℝ)ᵀ).det
      = (Matrix.of G * (Matrix.of G)ᵀ).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map]
  have hX : (Matrix.mvPolynomialX (Fin p) (Fin m) ℝ).map
      (MvPolynomial.eval fun ab : Fin p × Fin m => G ab.1 ab.2) = Matrix.of G := by
    ext i j; simp
  rw [hX]

theorem eval_det_gram_transpose (p m : ℕ) (G : Fin p → Fin m → ℝ) :
    MvPolynomial.eval (fun ab : Fin p × Fin m => G ab.1 ab.2)
      ((Matrix.mvPolynomialX (Fin p) (Fin m) ℝ)ᵀ * Matrix.mvPolynomialX (Fin p) (Fin m) ℝ).det
      = ((Matrix.of G)ᵀ * Matrix.of G).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map]
  have hX : (Matrix.mvPolynomialX (Fin p) (Fin m) ℝ).map
      (MvPolynomial.eval fun ab : Fin p × Fin m => G ab.1 ab.2) = Matrix.of G := by
    ext i j; simp
  rw [hX]

end GaussianMatrix

open GaussianMatrix

theorem solution (p m : ℕ) :
    ∀ᵐ G ∂(gaussianMatrix p m), (Matrix.of G).rank = min p m := by
  rcases le_total p m with h | h
  · have hP : (Matrix.mvPolynomialX (Fin p) (Fin m) ℝ *
        (Matrix.mvPolynomialX (Fin p) (Fin m) ℝ)ᵀ).det ≠ 0 := by
      intro h0
      let G0 : Fin p → Fin m → ℝ := fun i j => if j = Fin.castLE h i then 1 else 0
      have hE : Matrix.of G0 * (Matrix.of G0)ᵀ = 1 := by
        ext i k
        simp [G0, Matrix.mul_apply, Matrix.one_apply, Fin.castLE_inj, eq_comm]
      have := eval_det_gram p m G0
      rw [h0, map_zero, hE, Matrix.det_one] at this
      exact zero_ne_one this
    filter_upwards [ae_ne_zero_of_mvPolynomial p m _ hP] with G hG
    rw [eval_det_gram] at hG
    have hu : IsUnit (Matrix.of G * (Matrix.of G)ᵀ) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hG)
    have h1 := Matrix.rank_of_isUnit _ hu
    have h2 := Matrix.rank_mul_le_left (Matrix.of G) (Matrix.of G)ᵀ
    have h3 := Matrix.rank_le_height (Matrix.of G)
    rw [Fintype.card_fin] at h1
    rw [min_eq_left h]; omega
  · have hP : ((Matrix.mvPolynomialX (Fin p) (Fin m) ℝ)ᵀ *
        Matrix.mvPolynomialX (Fin p) (Fin m) ℝ).det ≠ 0 := by
      intro h0
      let G0 : Fin p → Fin m → ℝ := fun i j => if i = Fin.castLE h j then 1 else 0
      have hE : (Matrix.of G0)ᵀ * Matrix.of G0 = 1 := by
        ext i k
        simp [G0, Matrix.mul_apply, Matrix.one_apply, Fin.castLE_inj, eq_comm]
      have := eval_det_gram_transpose p m G0
      rw [h0, map_zero, hE, Matrix.det_one] at this
      exact zero_ne_one this
    filter_upwards [ae_ne_zero_of_mvPolynomial p m _ hP] with G hG
    rw [eval_det_gram_transpose] at hG
    have hu : IsUnit ((Matrix.of G)ᵀ * Matrix.of G) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hG)
    have h1 := Matrix.rank_of_isUnit _ hu
    have h2 := Matrix.rank_mul_le_right (Matrix.of G)ᵀ (Matrix.of G)
    have h3 := Matrix.rank_le_width (Matrix.of G)
    rw [Fintype.card_fin] at h1
    rw [min_eq_right h]; omega
