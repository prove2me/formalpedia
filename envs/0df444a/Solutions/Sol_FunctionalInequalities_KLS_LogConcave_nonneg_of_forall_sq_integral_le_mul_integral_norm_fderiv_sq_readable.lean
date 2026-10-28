-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.nonneg_of_forall_sq_integral_le_mul_integral_norm_fderiv_sq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:38:22.996875+00:00
-- url     : https://prove2.me/submissions/3d453e9e-8bc6-436e-84c2-8e2ee7feec4b

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HminusOne

noncomputable section
open MeasureTheory
open scoped ContDiff
/-- **A dual gradient bound has a nonnegative constant** (support for the `H⁻¹` variance lemma,
Letwin arXiv:2607.24164v1, Proposition 2.8): if `ν = e^{-W} dm` with `W` continuous on
`EuclideanSpace ℝ (Fin n)`, `n ≥ 1`, and `(∫ F h dν)² ≤ K ∫ ‖∇h‖² dν` for every `h ∈ C_c^∞`, then
`0 ≤ K` (some test has `∫ ‖∇h‖² dν > 0 because the density is positive). -/
theorem solution {n : ℕ} (hn : 0 < n)
    (m : Measure (EuclideanSpace ℝ (Fin n))) [m.IsAddHaarMeasure]
    {ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
    {W : EuclideanSpace ℝ (Fin n) → ℝ} (hνW : (ν : Measure _) = m.tilted (-W))
    (hW : Continuous W) {F : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ}
    (hK : ∀ h : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h →
      (∫ x, F x * h x ∂(ν : Measure _)) ^ 2 ≤
        K * ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(ν : Measure _)) :
    0 ≤ K := by
  by_contra hK'
  have hKneg : K < 0 := lt_of_not_ge hK'
  let Z : ℝ := ∫ x, Real.exp (-W x) ∂m
  have hZne : Z ≠ 0 := by
    intro hZ
    have hUniv := congrArg
      (fun μ : Measure (EuclideanSpace ℝ (Fin n)) => μ Set.univ) hνW
    simp [Measure.tilted, Z, hZ] at hUniv
  have hZpos : 0 < Z := by
    have hZnonneg : 0 ≤ Z := by
      exact integral_nonneg (fun x => Real.exp_nonneg (-W x))
    exact lt_of_le_of_ne hZnonneg hZne.symm
  have hνopen :
      ∀ U : Set (EuclideanSpace ℝ (Fin n)), IsOpen U → U.Nonempty →
        (ν : Measure (EuclideanSpace ℝ (Fin n))) U ≠ 0 := by
    intro U hUopen hUnonempty
    rw [hνW]
    change
      (m.withDensity
          (fun x => ENNReal.ofReal (Real.exp ((-W) x) / Z))) U ≠ 0
    have hcontden :
        Continuous
          (fun x : EuclideanSpace ℝ (Fin n) =>
            ENNReal.ofReal (Real.exp ((-W) x) / Z)) := by
      exact
        ENNReal.continuous_ofReal.comp
          ((Real.continuous_exp.comp hW.neg).div_const Z)
    have haeden :
        AEMeasurable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            ENNReal.ofReal (Real.exp ((-W) x) / Z)) m :=
      hcontden.aemeasurable
    have hset :
        {x : EuclideanSpace ℝ (Fin n) |
            ENNReal.ofReal (Real.exp ((-W) x) / Z) ≠ 0} = Set.univ := by
      ext x
      change ENNReal.ofReal (Real.exp ((-W) x) / Z) ≠ 0 ↔ True
      exact iff_true_intro
        (ne_of_gt (ENNReal.ofReal_pos.mpr (div_pos (Real.exp_pos _) hZpos)))
    intro hzero
    have hmzero :
        m
            ({x : EuclideanSpace ℝ (Fin n) |
                ENNReal.ofReal (Real.exp ((-W) x) / Z) ≠ 0} ∩ U) = 0 :=
      (withDensity_apply_eq_zero' haeden).mp hzero
    have hmzeroU : m U = 0 := by
      rw [← Set.univ_inter U, ← hset]
      exact hmzero
    exact (Measure.IsOpenPosMeasure.open_pos U hUopen hUnonempty) hmzeroU
  let c : EuclideanSpace ℝ (Fin n) := 0
  let φ : ContDiffBump c := ⟨1, 2, by norm_num, by norm_num⟩
  let i : Fin n := ⟨0, hn⟩
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
  let h : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => φ x * (L x - L c)
  have hcφ : (φ c : ℝ) = 1 := by
    apply φ.one_of_mem_closedBall
    simpa [Metric.mem_closedBall] using φ.rIn_pos.le
  have hφdiff : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => (φ x : ℝ)) :=
    φ.contDiff
  have hφ :
      HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) => (φ x : ℝ))
        (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) => (φ x : ℝ)) c) c := by
    exact ((hφdiff.differentiable (by simp)) c).hasFDerivAt
  have hL :
      HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) => L x - L c) L c := by
    simpa using L.hasFDerivAt.sub_const (L c)
  have hh : HasFDerivAt h L c := by
    change HasFDerivAt
      (fun x : EuclideanSpace ℝ (Fin n) => (φ x : ℝ) * (L x - L c)) L c
    have hm := hφ.mul hL
    rw [hcφ, sub_self, one_smul, zero_smul, add_zero] at hm
    exact hm
  have hcont : ContDiff ℝ ∞ h := by
    exact hφdiff.mul (L.contDiff.sub contDiff_const)
  have hcomp : HasCompactSupport h := by
    exact φ.hasCompactSupport.mul_right
  have hLne : L ≠ 0 := by
    intro hLzero
    have hLzero' := congrArg
      (fun q : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
        q (EuclideanSpace.single i 1)) hLzero
    simp [L] at hLzero'
  have hderivc : fderiv ℝ h c ≠ 0 := by
    rw [hh.fderiv]
    exact hLne
  have hfdcont : Continuous (fderiv ℝ h) := by
    exact hcont.continuous_fderiv (by simp)
  let g : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => ‖fderiv ℝ h x‖ ^ 2
  have hgcont : Continuous g := by
    exact (continuous_norm.comp hfdcont).pow 2
  have hgcomp : HasCompactSupport g := by
    have hderivcomp : HasCompactSupport (fderiv ℝ h) := hcomp.fderiv ℝ
    apply hderivcomp.norm.mono
    intro x hx
    apply Function.mem_support.mpr
    intro hzero
    apply hx
    simp [g, hzero]
  have hgint : Integrable g (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
    exact hgcont.integrable_of_hasCompactSupport hgcomp
  have hgpos : 0 < g c := by
    have hnorm : 0 < ‖fderiv ℝ h c‖ := norm_pos_iff.mpr hderivc
    exact sq_pos_of_pos hnorm
  let U : Set (EuclideanSpace ℝ (Fin n)) := {x | 0 < g x}
  have hUopen : IsOpen U := by
    exact isOpen_lt continuous_const hgcont
  have hcU : c ∈ U := by
    exact hgpos
  have hUzero : (ν : Measure (EuclideanSpace ℝ (Fin n))) U ≠ 0 := by
    exact hνopen U hUopen ⟨c, hcU⟩
  have hUpos : 0 < (ν : Measure (EuclideanSpace ℝ (Fin n))) U :=
    pos_iff_ne_zero.mpr hUzero
  have hgsupp :
      0 < (ν : Measure (EuclideanSpace ℝ (Fin n))) (Function.support g) := by
    apply lt_of_lt_of_le hUpos
    apply measure_mono
    intro x hx
    exact Function.mem_support.mpr (ne_of_gt hx)
  have henergy :
      0 < ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(ν : Measure (EuclideanSpace ℝ (Fin n))) := by
    exact
      (integral_pos_iff_support_of_nonneg (fun x => sq_nonneg _) hgint).mpr hgsupp
  have hineq := hK h hcont hcomp
  have hleft :
      0 ≤ (∫ x, F x * h x ∂(ν : Measure (EuclideanSpace ℝ (Fin n)))) ^ 2 :=
    sq_nonneg _
  have hright :
      K * ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(ν : Measure (EuclideanSpace ℝ (Fin n))) < 0 :=
    mul_neg_of_neg_of_pos hKneg henergy
  have hcontra :
      (∫ x, F x * h x ∂(ν : Measure (EuclideanSpace ℝ (Fin n)))) ^ 2 < 0 :=
    lt_of_le_of_lt hineq hright
  exact (not_lt_of_ge hleft) hcontra
