-- Prove2me | solution 1 for AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/6c94186c-f613-548d-bb83-41ee324b7a49

import Theorems.Thm_AutomorphicForm_isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_conjAe_of_nhds_forall_isRegularSemisimple_of_pos
import Theorems.Thm_AutomorphicForm_isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isRegularSemisimple_of_neg
import Theorems.Thm_AutomorphicForm_isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_of_algHom_real_of_nhds_forall_isRegularSemisimple
import Theorems.Thm_AutomorphicForm_isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_of_algHom_complex_of_nhds_forall_isRegularSemisimple
import Theorems.Thm_AutomorphicForm_exists_isNormConjugator_and_coupled_of_gram_conjAe_of_pos
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_SplitFibreIntegral
import Theorems.Thm_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_finrank_eq_two
p2m_attr_erase "simp" "LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (γ : GL (Fin 2) (InfiniteAdeleRing K))
    (hγ : ∃ c : (InfiniteAdeleRing K)ˣ, γ = Matrix.GeneralLinearGroup.scalar (Fin 2) c)
    (δ y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hδ : AutomorphicForm.IsNormConjugator K L (InfiniteAdeleRing K) σ γ δ y)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) γ) τ)
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ) τ')
    (hnorm :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
      letI := AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) γ
      letI := AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ
      ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
        (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (s : ENNReal),
        s ≠ 0 ∧ s ≠ ⊤ ∧
        LinearIndependent ℝ e₁ ∧
          (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
            Set.range (fun Y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) =>
              Y.map (Algebra.TensorProduct.includeRight :
                InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K)) ∧
        LinearIndependent ℝ e₂ ∧
          (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
            {X | X * (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
              (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
                X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)} ∧
        Measure.map (fun t : ↥(Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) =>
            ((t : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)).map
              (Algebra.TensorProduct.includeRight :
                InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K)) τ =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                Measure.map (fun c : Fin n₁ → ℝ => ∑ i, c i • e₁ i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
        Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) =>
            ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τ' =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                Measure.map (fun c : Fin n₂ → ℝ => ∑ i, c i • e₂ i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹)) :
    ∀ (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ), AutomorphicForm.IsArchTestFactor L φa →
      ∀ (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ), AutomorphicForm.IsArchTestFactor K fa →
        AutomorphicForm.AreMatchingArch K L σ φa fa →
        ∀ I I' : ℂ,
          AutomorphicForm.IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (AutomorphicForm.archHaarL K L) δ τ'
            (φa ∘ AutomorphicForm.archIdentGL K L) I' →
          AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) (AutomorphicForm.archHaarK K) γ τ fa I →
          I' = (-1 : ℂ) ^ (Nat.card {w : NumberField.InfinitePlace K //
            ∀ z : (L ⊗[K] w.Completion)ˣ,
              ¬ AutomorphicForm.IsSigmaConjugate K L w.Completion σ
                  (Matrix.GeneralLinearGroup.map
                    (Algebra.TensorProduct.map (AlgHom.id K L)
                      (Pi.evalAlgHom K (fun w : NumberField.InfinitePlace K => w.Completion) w)).toRingHom δ)
                  (Matrix.GeneralLinearGroup.scalar (Fin 2) z)}) * I := by
  have hprime : (Module.finrank K L).Prime := by rw [h2]; exact Nat.prime_two
  exact AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom
    K L h2 σ hgen γ hγ δ y hδ τ hτ τ' hτ' hnorm hprime
    (AutomorphicForm.isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_conjAe_of_nhds_forall_isRegularSemisimple_of_pos)
    (AutomorphicForm.isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isRegularSemisimple_of_neg)
    (fun hσ _ ι => AutomorphicForm.isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_of_algHom_real_of_nhds_forall_isRegularSemisimple
      K L hprime σ hσ ι)
    (fun hσ _ ι => AutomorphicForm.isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_of_algHom_complex_of_nhds_forall_isRegularSemisimple
      K L hprime σ hσ ι)
    (AutomorphicForm.exists_isNormConjugator_and_coupled_of_gram_conjAe_of_pos)

end S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_finrank_eq_two (solution)
