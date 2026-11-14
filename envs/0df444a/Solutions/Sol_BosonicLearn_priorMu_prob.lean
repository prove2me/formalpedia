-- Prove2me | solution 1 for BosonicLearn.priorMu_prob
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T07:31:26.140137+00:00
-- url     : https://prove2.me/submissions/b3ce827e-3cbc-49ff-b674-11a0dcbe93ea

import Mathlib
import Definitions.Def_BosonicLearn_priorMu

open MeasureTheory
open scoped ENNReal

open BosonicLearn

noncomputable section

/-- The operator norm of a matrix, through its action on Euclidean space. -/
private def opnM (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M‖

private lemma continuous_toCLM (n : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) ℂ => Matrix.toEuclideanCLM (𝕜 := ℂ) M :=
  LinearMap.continuous_of_finiteDimensional
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)

private lemma continuous_opnM (n : ℕ) : Continuous (opnM n) := (continuous_toCLM n).norm

private lemma gsupp_eq (n : ℕ) : Gsupp n = {X : Herm0 n | opnM n (X : Matrix (Fin n) (Fin n) ℂ) ≤ 4} := by
  ext X
  simp [Gsupp, WHMultiplicativity.schattenNorm, opnM]

private lemma gsupp_closed (n : ℕ) : IsClosed (Gsupp n) := by
  rw [gsupp_eq]
  exact isClosed_le ((continuous_opnM n).comp continuous_subtype_val) continuous_const

/-- The operator-norm ball of matrices is compact. -/
private lemma compact_ball (n : ℕ) :
    IsCompact {M : Matrix (Fin n) (Fin n) ℂ | opnM n M ≤ 4} := by
  have hsymm : Continuous fun T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) =>
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm T :=
    LinearMap.continuous_of_finiteDimensional
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm.toAlgEquiv.toLinearMap)
  have himg : {M : Matrix (Fin n) (Fin n) ℂ | opnM n M ≤ 4} =
      (fun T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) =>
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm T) '' Metric.closedBall 0 4 := by
    ext M
    constructor
    · intro hM
      refine ⟨Matrix.toEuclideanCLM (𝕜 := ℂ) M, ?_, by simp⟩
      rw [mem_closedBall_zero_iff]
      exact hM
    · rintro ⟨T, hT, rfl⟩
      rw [mem_closedBall_zero_iff] at hT
      show ‖Matrix.toEuclideanCLM (𝕜 := ℂ) ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm T)‖ ≤ 4
      simpa using hT
  rw [himg]
  exact (isCompact_closedBall _ _).image hsymm

private lemma gsupp_compact (n : ℕ) : IsCompact (Gsupp n) := by
  have h := (Herm0_isClosed n).isClosedEmbedding_subtypeVal.isCompact_preimage (compact_ball n)
  rw [gsupp_eq]
  exact h

private lemma haar_gsupp_pos (n : ℕ) : 0 < (Measure.addHaar : Measure (Herm0 n)) (Gsupp n) := by
  have hopen : IsOpen {X : Herm0 n | opnM n (X : Matrix (Fin n) (Fin n) ℂ) < 4} :=
    isOpen_lt ((continuous_opnM n).comp continuous_subtype_val) continuous_const
  have hne : {X : Herm0 n | opnM n (X : Matrix (Fin n) (Fin n) ℂ) < 4}.Nonempty :=
    ⟨0, by simp [opnM]⟩
  refine (hopen.measure_pos _ hne).trans_le (measure_mono ?_)
  rw [gsupp_eq]
  intro X hX
  have h : opnM n (X : Matrix (Fin n) (Fin n) ℂ) < 4 := hX
  exact h.le

/-- The Frobenius norm is continuous. -/
private lemma continuous_frob (n : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) ℂ => WHMultiplicativity.schattenNorm 2 M := by
  have h : ∀ M : Matrix (Fin n) (Fin n) ℂ, WHMultiplicativity.schattenNorm 2 M =
      ((M.conjTranspose * M).trace.re) ^ ((1 : ℝ) / 2) := by
    intro M
    unfold WHMultiplicativity.schattenNorm
    rw [if_neg (by norm_num)]
    have h2 : (2 : ℝ≥0∞).toReal = 2 := by simp
    rw [h2]
    have hfun : (fun x : ℝ => x ^ ((2 : ℝ) / 2)) = fun x => x := by
      funext x
      rw [div_self (by norm_num), Real.rpow_one]
    rw [hfun, cfc_id' ℝ (M.conjTranspose * M)
      (by rw [← Matrix.star_eq_conjTranspose]; exact IsSelfAdjoint.star_mul_self M)]
  simp only [h]
  exact (Complex.continuous_re.comp
    ((continuous_id.matrix_conjTranspose.matrix_mul continuous_id).matrix_trace)).rpow_const
    (fun _ => Or.inr (by norm_num))

theorem solution (n : ℕ) :
    IsProbabilityMeasure (priorMu n) ∧ ∀ᵐ X ∂(priorMu n), X ∈ Gsupp n := by
  set f : Herm0 n → ℝ≥0∞ := fun X => ENNReal.ofReal (Real.exp (-(n / 4 : ℝ) *
    WHMultiplicativity.schattenNorm 2 (X : Matrix (Fin n) (Fin n) ℂ) ^ 2)) with hf
  set m : Measure (Herm0 n) :=
    ((Measure.addHaar : Measure (Herm0 n)).restrict (Gsupp n)).withDensity f with hm
  have hdef : priorMu n = (m Set.univ)⁻¹ • m := rfl
  have hfmeas : Measurable f :=
    (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul
      (((continuous_frob n).comp continuous_subtype_val).pow 2)))).measurable
  have hfpos : ∀ X, 0 < f X := fun X => ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hfle : ∀ X, f X ≤ 1 := by
    intro X
    rw [hf]
    refine ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr ?_)
    have h1 : 0 ≤ (n / 4 : ℝ) := by positivity
    nlinarith [sq_nonneg (WHMultiplicativity.schattenNorm 2 (X : Matrix (Fin n) (Fin n) ℂ))]
  have hmuniv : m Set.univ = ∫⁻ X, f X ∂((Measure.addHaar : Measure (Herm0 n)).restrict (Gsupp n)) := by
    rw [hm, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hfin : m Set.univ ≠ ⊤ := by
    rw [hmuniv]
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono hfle) ?_)
    rw [lintegral_one, Measure.restrict_apply_univ]
    exact (gsupp_compact n).measure_lt_top
  have hpos : m Set.univ ≠ 0 := by
    rw [hmuniv]
    refine ne_of_gt ((lintegral_pos_iff_support hfmeas).mpr ?_)
    have hsupp : Function.support f = Set.univ := by
      ext X
      simp [Function.mem_support, (hfpos X).ne']
    rw [hsupp, Measure.restrict_apply_univ]
    exact haar_gsupp_pos n
  refine ⟨⟨?_⟩, ?_⟩
  · rw [hdef, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hpos hfin]
  · rw [hdef]
    refine Measure.ae_smul_measure ?_ _
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem (gsupp_closed n).measurableSet)
