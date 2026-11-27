-- Prove2me | solution 1 for DRJointCC.Individual.Supplement.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:43:58.470941+00:00
-- url     : https://prove2.me/submissions/15ffab8d-0cda-48a2-bed2-8d48062240a6

import Mathlib
import Definitions.Def_DRJointCC_Individual_Supplement_Bonferroni

open MeasureTheory
open scoped ENNReal

open DRJointCC
open DRJointCC.Individual
open DRJointCC.Individual.Supplement

/-- Theorem 3.1 (Bonferroni Approximation), p. 14: for every vector of safety factors
`𝛜 ∈ ℰ` (`ε_i ≥ 0`, `Σ_i ε_i ≤ ε`), `𝒵_B^JCC(𝛜) ⊆ 𝒳^JCC`. -/
theorem solution {m n k : ℕ} (D : DRJointCC.Joint.JCCData m n k)
    (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) (hSig : Sig.PosDef)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (e : Fin m → ℝ) (he : e ∈ safetyFactors m ε) :
    ZB D μ Sig e ⊆ DRJointCC.Joint.XJCC D μ Sig ε := by
      intro x hx
      obtain ⟨he0, hesum⟩ := he
      simp only [DRJointCC.Joint.XJCC, Set.mem_setOf_eq]
      refine le_iInf₂ (fun P hP => ?_)
      obtain ⟨⟨hprob, hL2⟩, hmean, hcov⟩ := hP
      haveI := hprob
      have hint1 : ∀ i, Integrable (fun ξ : Fin k → ℝ => ξ i) P :=
        fun i => (hL2 i).integrable one_le_two
      have hint2 : ∀ i j, Integrable (fun ξ : Fin k → ℝ => ξ i * ξ j) P :=
        fun i j => (hL2 i).integrable_mul (hL2 j)
      have hm1 : ∀ i, ∫ ξ, ξ i ∂P = μ i := fun i => congrFun hmean i
      have hm2 : ∀ i j, ∫ ξ, ξ i * ξ j ∂P = Sig i j + μ i * μ j := by
        intro i j
        have h := congrFun (congrFun hcov i) j
        simp only [MomentDRO.Conf.covMat, MomentDRO.Conf.secondMomentAbout, hmean,
          Matrix.of_apply] at h
        have e1 : (fun ξ : Fin k → ℝ => (ξ i - μ i) * (ξ j - μ j)) =
            fun ξ => ξ i * ξ j - (μ j * ξ i + μ i * ξ j - μ i * μ j) := by
          funext ξ; ring
        have hA : Integrable (fun ξ : Fin k → ℝ => μ j * ξ i + μ i * ξ j) P :=
          ((hint1 i).const_mul _).add ((hint1 j).const_mul _)
        have A : ∫ ξ, (μ j * ξ i + μ i * ξ j - μ i * μ j) ∂P = μ i * μ j := by
          rw [integral_sub hA (integrable_const _),
            integral_add ((hint1 i).const_mul _) ((hint1 j).const_mul _),
            integral_const_mul, integral_const_mul, hm1, hm1, integral_const]
          simp; ring
        have B : ∫ ξ, (ξ i * ξ j - (μ j * ξ i + μ i * ξ j - μ i * μ j)) ∂P =
            ∫ ξ, ξ i * ξ j ∂P - ∫ ξ, (μ j * ξ i + μ i * ξ j - μ i * μ j) ∂P :=
          integral_sub (hint2 i j) (hA.sub (integrable_const _))
        rw [e1, B, A] at h
        linarith
      have hlift : ∀ a b, Integrable (fun ξ => lift ξ a * lift ξ b) P ∧
          ∫ ξ, lift ξ a * lift ξ b ∂P = momentMatrix μ Sig a b := by
        rintro (i | ⟨⟩) (j | ⟨⟩) <;>
          simp only [lift, momentMatrix, ConvexOptimization.symQuadBlock, Matrix.fromBlocks_apply₁₁,
            Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
            Sum.elim_inl, Sum.elim_inr, mul_one, one_mul]
        · exact ⟨hint2 i j, by
            rw [hm2]; change _ = (Sig + Matrix.vecMulVec μ μ) i j
            rw [Matrix.add_apply, Matrix.vecMulVec_apply]⟩
        · exact ⟨hint1 i, hm1 i⟩
        · exact ⟨hint1 j, hm1 j⟩
        · exact ⟨integrable_const _, by simp [Matrix.fromBlocks]⟩
      have hrow : ∀ i, P {ξ | 0 < DRJointCC.Joint.y0 D i x + DRJointCC.Joint.y D i x ⬝ᵥ ξ}
          ≤ ENNReal.ofReal (e i) := by
        intro i
        obtain ⟨β, M, hM, h1, hβ, hMQ⟩ := hx i
        have hf_eq : ∀ ξ, liftQuad M ξ = ∑ a, ∑ b, M a b * (lift ξ a * lift ξ b) := by
          intro ξ
          simp only [liftQuad, dotProduct, Matrix.mulVec, Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
        have hfint : Integrable (fun ξ => liftQuad M ξ) P := by
          simp_rw [hf_eq]
          exact integrable_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ =>
            ((hlift a b).1.const_mul _)
        have hfI : ∫ ξ, liftQuad M ξ ∂P = frob (momentMatrix μ Sig) M := by
          simp_rw [hf_eq]
          have S1 : ∫ ξ, ∑ a, ∑ b, M a b * (lift ξ a * lift ξ b) ∂P =
              ∑ a, ∫ ξ, ∑ b, M a b * (lift ξ a * lift ξ b) ∂P :=
            integral_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ =>
              ((hlift a b).1.const_mul _)
          rw [S1]
          simp only [frob, Matrix.trace, Matrix.diag, Matrix.mul_apply]
          refine Finset.sum_congr rfl fun a _ => ?_
          have S2 : ∫ ξ, ∑ b, M a b * (lift ξ a * lift ξ b) ∂P =
              ∑ b, ∫ ξ, M a b * (lift ξ a * lift ξ b) ∂P :=
            integral_finset_sum _ fun b _ => ((hlift a b).1.const_mul _)
          rw [S2]
          refine Finset.sum_congr rfl fun b _ => ?_
          have S3 : ∫ ξ, M a b * (lift ξ a * lift ξ b) ∂P =
              M a b * ∫ ξ, lift ξ a * lift ξ b ∂P := integral_const_mul _ _
          rw [S3, (hlift a b).2]
          have := hM.1.apply a b
          simp at this
          rw [← this]; ring
        have hf0 : ∀ ξ, 0 ≤ liftQuad M ξ := fun ξ => by
          have := hM.dotProduct_mulVec_nonneg (lift ξ)
          simpa [liftQuad] using this
        have hfge : ∀ ξ, DRJointCC.Joint.y0 D i x + DRJointCC.Joint.y D i x ⬝ᵥ ξ - β ≤
            liftQuad M ξ := by
          intro ξ
          have := hMQ.dotProduct_mulVec_nonneg (lift ξ)
          rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at this
          have hQ : lift ξ ⬝ᵥ (ConvexOptimization.symQuadBlock 0
              ((1 / 2 : ℝ) • DRJointCC.Joint.y D i x) (DRJointCC.Joint.y0 D i x - β)).mulVec
              (lift ξ) = DRJointCC.Joint.y D i x ⬝ᵥ ξ + (DRJointCC.Joint.y0 D i x - β) := by
            simp only [DRJointCC.Individual.lift,
              ConvexOptimization.symQuadBlock, dotProduct, Fintype.sum_sum_type, Matrix.mulVec,
              Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique,
              Finset.sum_singleton, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add,
              Finset.sum_add_distrib, mul_one, one_mul, Matrix.zero_apply, mul_zero, zero_mul,
              Finset.sum_const_zero, zero_add]
            have h1 : ∑ a, ξ a * (1 / 2 * DRJointCC.Joint.y D i x a) =
                1 / 2 * ∑ j, DRJointCC.Joint.y D i x j * ξ j := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
            have h2 : ∑ j, 1 / 2 * DRJointCC.Joint.y D i x j * ξ j =
                1 / 2 * ∑ j, DRJointCC.Joint.y D i x j * ξ j := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
            rw [h1, h2]; ring
          rw [hQ] at this
          unfold liftQuad
          linarith
        rcases hβ.lt_or_eq with hβn | hβ0
        · have hmk := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hf0) hfint (-β)
          have hsub : {ξ | 0 < DRJointCC.Joint.y0 D i x + DRJointCC.Joint.y D i x ⬝ᵥ ξ} ⊆
              {ξ | -β ≤ liftQuad M ξ} := fun ξ hξ => by
            have := hfge ξ
            simp only [Set.mem_setOf_eq] at hξ ⊢
            linarith
          have hr : P.real {ξ | -β ≤ liftQuad M ξ} ≤ e i := by
            rw [hfI] at hmk
            have : (-β) * P.real {ξ | -β ≤ liftQuad M ξ} ≤ (-β) * e i := by nlinarith
            exact le_of_mul_le_mul_left this (by linarith)
          calc P _ ≤ P {ξ | -β ≤ liftQuad M ξ} := measure_mono hsub
            _ = ENNReal.ofReal (P.real {ξ | -β ≤ liftQuad M ξ}) :=
              (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
            _ ≤ ENNReal.ofReal (e i) := ENNReal.ofReal_le_ofReal hr
        · subst hβ0
          have hI0 : ∫ ξ, liftQuad M ξ ∂P = 0 :=
            le_antisymm (by rw [hfI]; linarith) (integral_nonneg hf0)
          have hae := (integral_eq_zero_iff_of_nonneg (fun ξ => hf0 ξ) hfint).1 hI0
          have : P {ξ | 0 < DRJointCC.Joint.y0 D i x + DRJointCC.Joint.y D i x ⬝ᵥ ξ} = 0 := by
            rw [measure_eq_zero_iff_ae_notMem]
            filter_upwards [hae] with ξ hξ
            have := hfge ξ
            simp only [Pi.zero_apply] at hξ
            simp only [Set.mem_setOf_eq, not_lt]
            linarith
          rw [this]; exact bot_le
      set good := {ξ : Fin k → ℝ | ∀ i, DRJointCC.Joint.y0 D i x + DRJointCC.Joint.y D i x ⬝ᵥ ξ ≤ 0}
      set bad := ⋃ i, {ξ : Fin k → ℝ | 0 < DRJointCC.Joint.y0 D i x + DRJointCC.Joint.y D i x ⬝ᵥ ξ}
      have hbad : P bad ≤ ENNReal.ofReal ε := by
        calc P bad ≤ ∑ i, P {ξ : Fin k → ℝ | 0 < DRJointCC.Joint.y0 D i x +
              DRJointCC.Joint.y D i x ⬝ᵥ ξ} := measure_iUnion_fintype_le _ _
          _ ≤ ∑ i, ENNReal.ofReal (e i) := Finset.sum_le_sum fun i _ => hrow i
          _ = ENNReal.ofReal (∑ i, e i) := (ENNReal.ofReal_sum_of_nonneg fun i _ => he0 i).symm
          _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hesum
      have hunion : 1 ≤ P good + P bad := by
        calc (1 : ℝ≥0∞) = P Set.univ := measure_univ.symm
          _ ≤ P (good ∪ bad) := measure_mono (fun ξ _ => by
              by_cases h : ∀ i, DRJointCC.Joint.y0 D i x + DRJointCC.Joint.y D i x ⬝ᵥ ξ ≤ 0
              · exact Or.inl h
              · right
                push_neg at h
                obtain ⟨i, hi⟩ := h
                exact Set.mem_iUnion.2 ⟨i, hi⟩)
          _ ≤ _ := measure_union_le _ _
      calc ENNReal.ofReal (1 - ε) = 1 - ENNReal.ofReal ε := by
            rw [ENNReal.ofReal_sub _ hε.le, ENNReal.ofReal_one]
        _ ≤ 1 - P bad := tsub_le_tsub_left hbad _
        _ ≤ P good := tsub_le_iff_right.2 hunion
