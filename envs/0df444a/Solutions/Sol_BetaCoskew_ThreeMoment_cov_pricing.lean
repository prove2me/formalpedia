-- Prove2me | solution 1 for BetaCoskew.ThreeMoment.cov_pricing
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-25T23:25:20.258619+00:00
-- url     : https://prove2.me/submissions/6937b866-b864-4eaa-b6d0-a77ef55593ef

import Mathlib
import Definitions.Def_BetaCoskew_ThreeMoment_Model

namespace BetaCoskew.ThreeMoment

open MeasureTheory ProbabilityTheory

private theorem cov_manual {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hX : Integrable X P) (hY : Integrable Y P)
    (hXY : Integrable (fun ω => X ω * Y ω) P) :
    cov[X, Y; P] = (∫ ω, X ω * Y ω ∂P) - (∫ ω, X ω ∂P) * (∫ ω, Y ω ∂P) := by
  unfold covariance
  have h1 : Integrable (fun ω => X ω * (∫ ω, Y ω ∂P)) P := hX.mul_const _
  have h2 : Integrable (fun ω => (∫ ω, X ω ∂P) * Y ω) P := hY.const_mul _
  have e : ∀ ω, (X ω - ∫ ω, X ω ∂P) * (Y ω - ∫ ω, Y ω ∂P) =
      X ω * Y ω - X ω * (∫ ω, Y ω ∂P) - (∫ ω, X ω ∂P) * Y ω
        + (∫ ω, X ω ∂P) * (∫ ω, Y ω ∂P) := fun ω => by ring
  simp_rw [e]
  have i3 : Integrable (fun ω => X ω * Y ω - X ω * (∫ ω, Y ω ∂P)
      - (∫ ω, X ω ∂P) * Y ω) P := (hXY.sub h1).sub h2
  have i2 : Integrable (fun ω => X ω * Y ω - X ω * (∫ ω, Y ω ∂P)) P := hXY.sub h1
  have s1 := integral_add i3 (integrable_const ((∫ ω, X ω ∂P) * (∫ ω, Y ω ∂P)))
  have s2 := integral_sub i2 h2
  have s3 := integral_sub hXY h1
  rw [s1, s2, s3, integral_mul_const, integral_const_mul, integral_const]
  simp only [probReal_univ, one_smul]
  ring

theorem cov_pricing {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (mt ri : Ω → ℝ)
    (hmt : Integrable mt P) (hri : Integrable ri P)
    (hprod : Integrable (fun ω => mt ω * ri ω) P)
    (hprice : (∫ ω, mt ω * (1 + ri ω) ∂P) = 1)
    (hmean : 0 < ∫ ω, mt ω ∂P) :
    cov[mt, fun ω => 1 + ri ω; P] +
      (∫ ω, 1 + ri ω ∂P) * (∫ ω, mt ω ∂P) = 1 ∧
    (∫ ω, ri ω ∂P) =
      (1 - cov[mt, ri; P]) / (∫ ω, mt ω ∂P) - 1 := by
  have hi1 : Integrable (fun ω => 1 + ri ω) P := (integrable_const _).add hri
  have hp1 : Integrable (fun ω => mt ω * (1 + ri ω)) P := by
    have : (fun ω => mt ω * (1 + ri ω)) = fun ω => mt ω + mt ω * ri ω := by
      funext ω; ring
    rw [this]; exact hmt.add hprod
  have hsplit : (∫ ω, mt ω * (1 + ri ω) ∂P) =
      (∫ ω, mt ω ∂P) + ∫ ω, mt ω * ri ω ∂P := by
    rw [← integral_add hmt hprod]; congr 1; funext ω; ring
  have hE : (∫ ω, 1 + ri ω ∂P) = 1 + ∫ ω, ri ω ∂P := by
    rw [integral_add (integrable_const _) hri]; simp
  rw [cov_manual P mt _ hmt hi1 hp1, cov_manual P mt ri hmt hri hprod]
  refine ⟨by rw [hprice]; ring, ?_⟩
  have hne : (∫ ω, mt ω ∂P) ≠ 0 := hmean.ne'
  rw [hE] at *
  field_simp
  have : (∫ ω, mt ω * ri ω ∂P) = 1 - ∫ ω, mt ω ∂P := by linarith
  rw [this]
  ring

end BetaCoskew.ThreeMoment

open BetaCoskew.ThreeMoment in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (mt ri : Ω → ℝ)
    (hmt : MeasureTheory.Integrable mt P) (hri : MeasureTheory.Integrable ri P)
    (hprod : MeasureTheory.Integrable (fun ω => mt ω * ri ω) P)
    (hprice : (∫ ω, mt ω * (1 + ri ω) ∂P) = 1)
    (hmean : 0 < ∫ ω, mt ω ∂P) :
    ProbabilityTheory.covariance mt (fun ω => 1 + ri ω) P +
      (∫ ω, 1 + ri ω ∂P) * (∫ ω, mt ω ∂P) = 1 ∧
    (∫ ω, ri ω ∂P) =
      (1 - ProbabilityTheory.covariance mt ri P) / (∫ ω, mt ω ∂P) - 1 :=
  cov_pricing P mt ri hmt hri hprod hprice hmean
