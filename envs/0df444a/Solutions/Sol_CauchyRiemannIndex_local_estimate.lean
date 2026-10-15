-- Prove2me | solution 1 for CauchyRiemannIndex.local_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-15T08:07:04.679753+00:00
-- url     : https://prove2.me/submissions/1b06d5db-bfae-4d5e-a553-a8a931f1eee7

import Theorems.Thm_CauchyRiemannIndex_periodic_cauchyRiemann_estimate
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Topology.Algebra.Module.FiniteDimension

-- ===== Scratch/CRLocParent.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Matrix Set Filter
open scoped ENNReal NNReal ContDiff

noncomputable section

lemma crlp_clm_cont {n : ℕ} :
    Continuous (fun A : Mat n => (Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ) A)) :=
  LinearMap.continuous_of_finiteDimensional
    (Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ)).toAlgEquiv.toLinearMap

lemma crlp_lin_norm {n : ℕ} (A : Mat n) (v : Vec n) :
    ‖Matrix.toEuclideanLin A v‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ) A‖ * ‖v‖ :=
  (Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ) A).le_opNorm v

lemma crlp_apply {n : ℕ} (A : Mat n) (v : Vec n) :
    Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ) A v = Matrix.toEuclideanLin A v := rfl

theorem local_estimate_aux (n : ℕ) (p : ℝ≥0∞) (hp : 1 < p) (hp' : p ≠ ⊤) (R : ℝ)
    (S : ℝ × ℝ → Mat n) (hS : Continuous S) :
    ∃ c : ℝ≥0, ∀ u : ℝ × ℝ → Vec n, IsTestSection u → (∀ s t, R ≤ |s| → u (s, t) = 0) →
      w1pNorm p u ≤ c * eLpNorm (crOp S u) p cylMeasure + c * eLpNorm u p cylMeasure := by
  obtain ⟨A, hA⟩ := periodic_cauchyRiemann_estimate n p hp hp'
  set T : ℝ × ℝ → (Vec n →L[ℝ] Vec n) :=
    fun x => Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ) (S x)
  have hTc : Continuous T := crlp_clm_cont.comp hS
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_Icc (a := (0 : ℝ)) (b := 1)) :
      IsCompact (Icc (-|R|) |R| ×ˢ Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hTc.continuousOn
  set K : ℝ≥0 := C.toNNReal
  refine ⟨1 + A + A * K, fun u hu hR => ?_⟩
  obtain ⟨hsm, hper, -⟩ := hu
  have hu1 : ContDiff ℝ 1 u := hsm.of_le (by simp)
  have hAu := hA u hu1 hper ⟨R, fun s t h => hR s t h.le⟩
  -- continuity
  have hcd : Continuous (fun x => fderiv ℝ u x) := hu1.continuous_fderiv one_ne_zero
  have hcS : Continuous (partialS u) := hcd.clm_apply continuous_const
  have hcT : Continuous (partialT u) := hcd.clm_apply continuous_const
  set Jc : Vec n →L[ℝ] Vec n := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (J₀ n))
  have hcF : Continuous (fun x => partialS u x + Matrix.toEuclideanLin (J₀ n) (partialT u x)) :=
    hcS.add (Jc.continuous.comp hcT)
  have hcSu : Continuous (fun x => Matrix.toEuclideanLin (S x) (u x)) :=
    hTc.clm_apply hu1.continuous
  have hcD : Continuous (crOp S u) := hcF.add hcSu
  -- the zeroth-order term
  have hae : ∀ᵐ x ∂cylMeasure, x.2 ∈ Ico (0 : ℝ) 1 := by
    unfold cylMeasure
    filter_upwards [ae_restrict_mem (show MeasurableSet ((univ : Set ℝ) ×ˢ Ico (0 : ℝ) 1) from
      MeasurableSet.univ.prod measurableSet_Ico)] with x hx
    exact hx.2
  have hpt : ∀ᵐ x ∂cylMeasure, ‖Matrix.toEuclideanLin (S x) (u x)‖ ≤ (K : ℝ) * ‖u x‖ := by
    filter_upwards [hae] with x hx
    by_cases h : R ≤ |x.1|
    · have : u x = 0 := by
        obtain ⟨s, t⟩ := x; exact hR s t h
      simp [this]
    · have hxK : x ∈ Icc (-|R|) |R| ×ˢ Icc (0 : ℝ) 1 := by
        refine ⟨?_, hx.1, hx.2.le⟩
        rw [mem_Icc, ← abs_le]; exact ((not_le.1 h).le).trans (le_abs_self R)
      calc ‖Matrix.toEuclideanLin (S x) (u x)‖ ≤ ‖T x‖ * ‖u x‖ := crlp_lin_norm _ _
        _ ≤ (K : ℝ) * ‖u x‖ := by
          gcongr
          exact (hC x hxK).trans (Real.le_coe_toNNReal C)
  have hE : eLpNorm (fun x => partialS u x + Matrix.toEuclideanLin (J₀ n) (partialT u x)) p
      cylMeasure ≤ eLpNorm (crOp S u) p cylMeasure + K * eLpNorm u p cylMeasure := by
    have heq : (fun x => partialS u x + Matrix.toEuclideanLin (J₀ n) (partialT u x)) =
        fun x => crOp S u x - Matrix.toEuclideanLin (S x) (u x) := by
      funext x; simp [crOp]
    rw [heq]
    calc eLpNorm (fun x => crOp S u x - Matrix.toEuclideanLin (S x) (u x)) p cylMeasure
        ≤ eLpNorm (crOp S u) p cylMeasure +
            eLpNorm (fun x => Matrix.toEuclideanLin (S x) (u x)) p cylMeasure :=
          eLpNorm_sub_le hcD.aestronglyMeasurable hcSu.aestronglyMeasurable hp.le
      _ ≤ eLpNorm (crOp S u) p cylMeasure + K * eLpNorm u p cylMeasure := by
          gcongr
          have := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpt p
          rwa [ENNReal.ofReal_coe_nnreal] at this
  -- combine
  set U := eLpNorm u p cylMeasure
  set D := eLpNorm (crOp S u) p cylMeasure
  calc w1pNorm p u
      = U + (eLpNorm (partialS u) p cylMeasure + eLpNorm (partialT u) p cylMeasure) := by
        rw [w1pNorm, add_assoc]
    _ ≤ U + (A * (D + K * U) + A * U) := by
        have h2 : (A : ℝ≥0∞) * eLpNorm (fun x => partialS u x +
            Matrix.toEuclideanLin (J₀ n) (partialT u x)) p cylMeasure + A * U ≤
            A * (D + K * U) + A * U := by gcongr
        exact add_le_add le_rfl (hAu.trans h2)
    _ = A * D + (1 + A + A * K) * U := by ring
    _ ≤ ((1 + A + A * K : ℝ≥0) : ℝ≥0∞) * D + ((1 + A + A * K : ℝ≥0) : ℝ≥0∞) * U := by
        push_cast
        gcongr
        calc (A : ℝ≥0∞) = 0 + A + 0 := by simp
          _ ≤ 1 + A + A * K := by gcongr <;> exact bot_le

end

end CauchyRiemannIndex

open CauchyRiemannIndex in
theorem solution (n : ℕ) (p : ENNReal) (hp : 1 < p) (hp' : p ≠ ⊤) (R : ℝ)
    (S : ℝ × ℝ → Mat n) (hS : Continuous S) (hper : ∀ s t, S (s, t + 1) = S (s, t)) :
    ∃ c : NNReal, ∀ u : ℝ × ℝ → Vec n, IsTestSection u → (∀ s t, R ≤ |s| → u (s, t) = 0) →
      w1pNorm p u ≤ c * MeasureTheory.eLpNorm (crOp S u) p cylMeasure +
        c * MeasureTheory.eLpNorm u p cylMeasure :=
  local_estimate_aux n p hp hp' R S hS
