-- Prove2me | solution 1 for ChanceStateCtrl.Robust.lemma_3_15
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T13:33:38.819037+00:00
-- url     : https://prove2.me/submissions/d5b99f21-fb94-4124-8f73-6ace5cb23a4c

import Mathlib
import Definitions.Def_ChanceStateCtrl_Robust_Setting

open MeasureTheory
open ChanceStateCtrl.Robust

theorem solution {d m : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} {Ξ : Set (EuclideanSpace ℝ (Fin m))}
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (hd : d = 1 ∨ d = 2 ∨ d = 3)
    (hS : ChanceStateCtrl.PDE.IsClassS D) [CompactSpace (closure D)] [CompactSpace Ξ]
    (f0 : ChanceStateCtrl.PDE.L2 D) (phi : Fin m → ChanceStateCtrl.PDE.L2 D)
    (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ)) (hA : ChanceStateCtrl.AlmostSure.IsSolutionOperator D Ainv) (α : ℝ)
    (F : ChanceStateCtrl.PDE.L2 D → ℝ) (hFconv : ConvexOn ℝ Set.univ F) (hFdiff : ContDiff ℝ 1 F)
    (hD0 : D.Nonempty) (hΞ0 : Ξ.Nonempty) (us : ChanceStateCtrl.PDE.L2 D) :
    (∃ μ : Measure (closure D × Ξ), IsFiniteMeasure μ ∧
        (∀ h : ChanceStateCtrl.PDE.L2 D, fderiv ℝ F us h + ∫ q, Ainv h q.1 ∂μ = 0) ∧
        (∀ q : closure D × Ξ, Shat Ainv f0 phi us q ≤ α) ∧
        ∫ q, (Shat Ainv f0 phi us q - α) ∂μ = 0) ↔
      ∃ lam : ℝ, ∃ μt : Measure (closure D × Ξ), IsProbabilityMeasure μt ∧
        μt (argmaxSet Ainv f0 phi us)ᶜ = 0 ∧
        (∀ h : ChanceStateCtrl.PDE.L2 D, fderiv ℝ F us h + lam * ∫ q, Ainv h q.1 ∂μt = 0) ∧
        0 ≤ lam ∧ (⨆ q : closure D × Ξ, Shat Ainv f0 phi us q) ≤ α ∧
        lam * ((⨆ q : closure D × Ξ, Shat Ainv f0 phi us q) - α) = 0 := by
  classical
  set y := Shat (Ξ := Ξ) Ainv f0 phi us with hy
  haveI : Nonempty (closure D × Ξ) := by
    obtain ⟨x, hx⟩ := hD0
    obtain ⟨z, hz⟩ := hΞ0
    exact ⟨(⟨x, subset_closure hx⟩, ⟨z, hz⟩)⟩
  have hbdd : BddAbove (Set.range fun q => y q) :=
    (isCompact_range y.continuous).bddAbove
  have hint : ∀ (ν : Measure (closure D × Ξ)) [IsFiniteMeasure ν] (z : C(closure D × Ξ, ℝ)),
      Integrable (fun q => z q) ν := fun ν _ z =>
    z.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- points where `y = α` are maximizers when `y ≤ α`
  have hmax : (∀ q, y q ≤ α) → ∀ q, y q = α → q ∈ argmaxSet (Ξ := Ξ) Ainv f0 phi us := by
    intro hle q hq q'
    rw [← hy, hq]; exact hle q'
  have hsup_of : ∀ q, q ∈ argmaxSet (Ξ := Ξ) Ainv f0 phi us → y q = ⨆ q', y q' := by
    intro q hq
    exact le_antisymm (le_ciSup hbdd q) (ciSup_le hq)
  constructor
  · rintro ⟨μ, hμ, h66a, h66b, h66c⟩
    have hsupα : (⨆ q, y q) ≤ α := ciSup_le h66b
    by_cases hc : μ Set.univ = 0
    · -- zero measure: `λ = 0`, Dirac mass at a maximizer
      obtain ⟨q0, -, hq0⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
        y.continuous.continuousOn
      have hq0' : q0 ∈ argmaxSet (Ξ := Ξ) Ainv f0 phi us := fun q' => hq0 (Set.mem_univ q')
      have hμ0 : μ = 0 := Measure.measure_univ_eq_zero.1 hc
      refine ⟨0, Measure.dirac q0, inferInstance, ?_, fun h => ?_, le_rfl, hsupα, by ring⟩
      · rw [Measure.dirac_apply]
        simp [hq0']
      · have := h66a h
        rw [hμ0, integral_zero_measure] at this
        simpa using this
    · set c := μ Set.univ with hcdef
      have hctop : c ≠ ⊤ := measure_ne_top μ _
      have hcpos : 0 < c.toReal := ENNReal.toReal_pos hc hctop
      -- `y = α` μ-a.e.
      have hae : (fun q => y q - α) =ᵐ[μ] 0 := by
        have hnn : 0 ≤ (fun q => α - y q) := fun q => sub_nonneg.2 (h66b q)
        have hi : Integrable (fun q => α - y q) μ :=
          (integrable_const α).sub (hint μ y)
        have h0 : ∫ q, (α - y q) ∂μ = 0 := by
          have : ∫ q, (α - y q) ∂μ = -∫ q, (y q - α) ∂μ := by
            rw [← integral_neg]; congr 1; ext q; ring
          rw [this, h66c, neg_zero]
        have := (integral_eq_zero_iff_of_nonneg hnn hi).1 h0
        filter_upwards [this] with q hq
        simp only [Pi.zero_apply] at hq ⊢
        linarith
      have hnull : μ {q | y q - α ≠ 0} = 0 := by
        rw [Filter.EventuallyEq, ae_iff] at hae; exact hae
      have hnullc : μ (argmaxSet (Ξ := Ξ) Ainv f0 phi us)ᶜ = 0 := by
        refine measure_mono_null (fun q hq => ?_) hnull
        intro h0
        exact hq (hmax h66b q (by linarith))
      -- some point attains `α`
      have hex : ∃ q, y q = α := by
        by_contra hne
        push Not at hne
        apply hc
        show μ Set.univ = 0
        have : {q | y q - α ≠ 0} = Set.univ := by
          ext q; simp [sub_eq_zero, hne q]
        rw [← this]; exact hnull
      obtain ⟨q1, hq1⟩ := hex
      have hsup_eq : (⨆ q, y q) = α :=
        le_antisymm hsupα (hq1 ▸ le_ciSup hbdd q1)
      refine ⟨c.toReal, c⁻¹ • μ, ⟨?_⟩, ?_, fun h => ?_, hcpos.le, hsupα, ?_⟩
      · rw [Measure.smul_apply, smul_eq_mul, ← hcdef, ENNReal.inv_mul_cancel hc hctop]
      · rw [Measure.smul_apply, hnullc, smul_zero]
      · rw [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul, ← mul_assoc,
          mul_inv_cancel₀ hcpos.ne', one_mul]
        exact h66a h
      · rw [hsup_eq, sub_self, mul_zero]
  · rintro ⟨lam, μt, hμt, hsupp, h67a, hlam, hsupα, hcomp⟩
    have hle : ∀ q, y q ≤ α := fun q => (le_ciSup hbdd q).trans hsupα
    have hfin : IsFiniteMeasure (ENNReal.ofReal lam • μt) := ⟨by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
    refine ⟨ENNReal.ofReal lam • μt, hfin, fun h => ?_, hle, ?_⟩
    · rw [integral_smul_measure, ENNReal.toReal_ofReal hlam, smul_eq_mul]
      exact h67a h
    · rw [integral_smul_measure, ENNReal.toReal_ofReal hlam, smul_eq_mul]
      rcases hlam.eq_or_lt with h0 | hpos
      · rw [← h0, zero_mul]
      · have hsup_eq : (⨆ q, y q) = α := by
          have := (mul_eq_zero.1 hcomp).resolve_left hpos.ne'
          linarith
        have hae : ∀ᵐ q ∂μt, q ∈ argmaxSet (Ξ := Ξ) Ainv f0 phi us := by
          rw [ae_iff]; exact hsupp
        have : ∫ q, (y q - α) ∂μt = 0 := by
          refine integral_eq_zero_of_ae ?_
          filter_upwards [hae] with q hq
          rw [hsup_of q hq, hsup_eq]; simp
        rw [this, mul_zero]
