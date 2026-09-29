-- Prove2me | solution 1 for AutomorphicForm.weight_localCentralizer_mul_and_semiLocalWeight_twistedCentralizer_mul_of_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/43c622df-2d17-56a5-bce6-c2355acd0d19

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_weight_localCentralizer_mul_and_semiLocalWeight_twistedCentralizer_mul_of_diagonal

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

namespace FWI9

open AutomorphicForm

section generic
variable {R : Type*} [CommRing R]

theorem val_mul_apply (x y : GL (Fin 2) R) (i j : Fin 2) :
    ((x * y : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j =
      (x : Matrix (Fin 2) (Fin 2) R) i 0 * (y : Matrix (Fin 2) (Fin 2) R) 0 j +
        (x : Matrix (Fin 2) (Fin 2) R) i 1 * (y : Matrix (Fin 2) (Fin 2) R) 1 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem offdiag_eq_zero_of_commute (T t : GL (Fin 2) R)
    (hT01 : (T : Matrix (Fin 2) (Fin 2) R) 0 1 = 0) (hT10 : (T : Matrix (Fin 2) (Fin 2) R) 1 0 = 0)
    (hreg : IsUnit ((T : Matrix (Fin 2) (Fin 2) R) 0 0 - (T : Matrix (Fin 2) (Fin 2) R) 1 1))
    (hc : T * t = t * T) :
    (t : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := by
  have hv := congrArg (fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R)) hc
  have e01 := congrFun (congrFun hv 0) 1
  have e10 := congrFun (congrFun hv 1) 0
  rw [val_mul_apply, val_mul_apply, hT01, zero_mul, add_zero, mul_zero, zero_add] at e01
  rw [val_mul_apply, val_mul_apply, hT10, zero_mul, zero_add, mul_zero, add_zero] at e10
  constructor
  · have h : ((T : Matrix (Fin 2) (Fin 2) R) 0 0 - (T : Matrix (Fin 2) (Fin 2) R) 1 1) *
        (t : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 := by
      rw [sub_mul, e01, mul_comm, sub_self]
    exact (hreg.mul_right_eq_zero).mp h
  · have h : ((T : Matrix (Fin 2) (Fin 2) R) 0 0 - (T : Matrix (Fin 2) (Fin 2) R) 1 1) *
        (t : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := by
      rw [sub_mul, e10, mul_comm, sub_self]
    exact (hreg.mul_right_eq_zero).mp h

theorem isUnit_sub_of_isRegularSemisimple (T : GL (Fin 2) R)
    (hT01 : (T : Matrix (Fin 2) (Fin 2) R) 0 1 = 0) (hT10 : (T : Matrix (Fin 2) (Fin 2) R) 1 0 = 0)
    (hreg : IsRegularSemisimple T) :
    IsUnit ((T : Matrix (Fin 2) (Fin 2) R) 0 0 - (T : Matrix (Fin 2) (Fin 2) R) 1 1) := by
  have h : Matrix.trace (T : Matrix (Fin 2) (Fin 2) R) ^ 2 - 4 * Matrix.det (T : Matrix (Fin 2) (Fin 2) R) =
      ((T : Matrix (Fin 2) (Fin 2) R) 0 0 - (T : Matrix (Fin 2) (Fin 2) R) 1 1) *
        ((T : Matrix (Fin 2) (Fin 2) R) 0 0 - (T : Matrix (Fin 2) (Fin 2) R) 1 1) := by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two, hT01, hT10]; ring
  have h2 : IsUnit (Matrix.trace (T : Matrix (Fin 2) (Fin 2) R) ^ 2 - 4 * Matrix.det (T : Matrix (Fin 2) (Fin 2) R)) := hreg
  rw [h] at h2
  exact (IsUnit.mul_iff.mp h2).1

end generic

theorem weight_diag_mul {F : Type*} [NormedField F] (d y : GL (Fin 2) F)
    (hd01 : (d : Matrix (Fin 2) (Fin 2) F) 0 1 = 0) (hd10 : (d : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    LocalWeight.weight (d * y) = LocalWeight.weight y := by
  have hdet : (d : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
  have hdet' : (d : Matrix (Fin 2) (Fin 2) F).det = (d : Matrix (Fin 2) (Fin 2) F) 0 0 * (d : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    rw [Matrix.det_fin_two, hd01, hd10, mul_zero, sub_zero]
  rw [hdet'] at hdet
  obtain ⟨h0, h1⟩ := mul_ne_zero_iff.mp hdet
  have n0 : 0 < ‖(d : Matrix (Fin 2) (Fin 2) F) 0 0‖ := norm_pos_iff.mpr h0
  have n1 : 0 < ‖(d : Matrix (Fin 2) (Fin 2) F) 1 1‖ := norm_pos_iff.mpr h1
  unfold LocalWeight.weight AdelicHeight.rowMaxNorm
  simp only [val_mul_apply, hd01, hd10, zero_mul, add_zero, zero_add, norm_mul, Units.val_mul, Matrix.det_mul, hdet']
  rw [← mul_max_of_nonneg _ _ n0.le, ← mul_max_of_nonneg _ _ n1.le]
  congr 1
  field_simp

section sigma

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]

theorem sigmaTensor_mul_apply (σ τ : L ≃ₐ[K] L) (x : L ⊗[K] A) :
    sigmaTensor K L A (σ * τ) x = sigmaTensor K L A σ (sigmaTensor K L A τ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l a =>
    change Algebra.TensorProduct.map (σ * τ).toAlgHom (AlgHom.id K A) (l ⊗ₜ a) =
      Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A) (Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id K A) (l ⊗ₜ a))
    simp only [Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem sigmaTensor_one_apply (x : L ⊗[K] A) : sigmaTensor K L A 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l a =>
    change Algebra.TensorProduct.map (1 : L ≃ₐ[K] L).toAlgHom (AlgHom.id K A) (l ⊗ₜ a) = l ⊗ₜ a
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy => rw [map_add, hx, hy]

theorem sigmaTensor_iterate (σ : L ≃ₐ[K] L) (n : ℕ) (x : L ⊗[K] A) :
    (⇑(sigmaTensor K L A σ))^[n] x = sigmaTensor K L A (σ ^ n) x := by
  induction n with
  | zero => rw [Function.iterate_zero_apply, pow_zero, sigmaTensor_one_apply]
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', sigmaTensor_mul_apply]

theorem sigmaGL_iterate_apply (σ : L ≃ₐ[K] L) (n : ℕ) (x : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2) :
    (((⇑(sigmaGL K L A σ))^[n] x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      (⇑(sigmaTensor K L A σ))^[n] ((x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

theorem sigmaGL_iterate_finrank [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (x : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(sigmaGL K L A σ))^[Module.finrank K L] x = x := by
  have hdvd : orderOf σ ∣ Module.finrank K L := by
    have h1 : Module.finrank (IntermediateField.fixedField (Subgroup.zpowers σ)) L = Nat.card (Subgroup.zpowers σ) :=
      IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers σ)
    rw [Nat.card_zpowers] at h1
    rw [← h1]
    exact Dvd.intro_left _ (Module.finrank_mul_finrank K (IntermediateField.fixedField (Subgroup.zpowers σ)) L)
  have hpow : σ ^ Module.finrank K L = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
  apply Units.ext
  ext i j
  rw [sigmaGL_iterate_apply, sigmaTensor_iterate, hpow, sigmaTensor_one_apply]

theorem mul_prod_eq (σ : L ≃ₐ[K] L) (δ t : GL (Fin 2) (L ⊗[K] A)) (ht : t * δ * (sigmaGL K L A σ t)⁻¹ = δ) (n : ℕ) :
    t * ((List.range n).map fun i => (⇑(sigmaGL K L A σ))^[i] δ).prod =
      ((List.range n).map fun i => (⇑(sigmaGL K L A σ))^[i] δ).prod * (⇑(sigmaGL K L A σ))^[n] t := by
  have htδ : t * δ = δ * sigmaGL K L A σ t := by
    calc t * δ = t * δ * (sigmaGL K L A σ t)⁻¹ * sigmaGL K L A σ t := by group
      _ = δ * sigmaGL K L A σ t := by rw [ht]
  induction n with
  | zero => simp
  | succ n ih =>
    have key : ∀ P : GL (Fin 2) (L ⊗[K] A), t * P = P * (⇑(sigmaGL K L A σ))^[n] t →
        t * (P * (⇑(sigmaGL K L A σ))^[n] δ) =
          P * (⇑(sigmaGL K L A σ))^[n] δ * (⇑(sigmaGL K L A σ))^[n + 1] t := by
      intro P hP
      rw [← mul_assoc, hP, mul_assoc, ← iterate_map_mul, htδ, iterate_map_mul, Function.iterate_succ_apply, mul_assoc]
    rw [List.range_succ, List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]
    exact key _ ih

end sigma

end FWI9

open FWI9 AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K)) :
    (∀ γv : GL (Fin 2) (v.adicCompletion K),
      (γv : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 →
      (γv : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 →
      AutomorphicForm.IsRegularSemisimple γv →
      ∀ t : AutomorphicForm.localCentralizer K v γv, ∀ x : GL (Fin 2) (v.adicCompletion K),
        AutomorphicForm.LocalWeight.weight ((t : GL (Fin 2) (v.adicCompletion K)) * x) =
          AutomorphicForm.LocalWeight.weight x) ∧
    (∀ δv : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      (δv : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0 →
      (δv : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0 →
      AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ δv) →
      ∀ t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δv,
        ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
          AutomorphicForm.semiLocalWeight K L v ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * x) =
            AutomorphicForm.semiLocalWeight K L v x)  := by
  refine ⟨fun γv h10 h01 hreg t x => ?_, fun δv h10 h01 hreg t x => ?_⟩
  ·
    have hcomm : γv * (t : GL (Fin 2) (v.adicCompletion K)) = (t : GL (Fin 2) (v.adicCompletion K)) * γv :=
      (Subgroup.mem_centralizer_iff.mp t.2) γv (Set.mem_singleton _)
    have hu := FWI9.isUnit_sub_of_isRegularSemisimple γv h01 h10 hreg
    obtain ⟨ht01, ht10⟩ := FWI9.offdiag_eq_zero_of_commute γv (t : GL (Fin 2) (v.adicCompletion K)) h01 h10 hu hcomm
    exact FWI9.weight_diag_mul _ x ht01 ht10
  ·
    set A := v.adicCompletion K with hA
    set N := normString K L A σ δv with hN
    have ht : (t : GL (Fin 2) (L ⊗[K] A)) * δv * (sigmaGL K L A σ (t : GL (Fin 2) (L ⊗[K] A)))⁻¹ = δv :=
      mem_sigmaCentralizer_iff.mp t.2

    have hcomm : N * (t : GL (Fin 2) (L ⊗[K] A)) = (t : GL (Fin 2) (L ⊗[K] A)) * N := by
      rw [hN]
      change _ = (t : GL (Fin 2) (L ⊗[K] A)) * ((List.range (Module.finrank K L)).map fun i => (⇑(sigmaGL K L A σ))^[i] δv).prod
      rw [FWI9.mul_prod_eq K L A σ δv _ ht, FWI9.sigmaGL_iterate_finrank]
      rfl

    have hNd : ∀ n : ℕ, ((((List.range n).map fun i => (⇑(sigmaGL K L A σ))^[i] δv).prod : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 ∧
        ((((List.range n).map fun i => (⇑(sigmaGL K L A σ))^[i] δv).prod : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        obtain ⟨ih01, ih10⟩ := ih
        have e01 : (((⇑(sigmaGL K L A σ))^[n] δv : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 := by
          rw [FWI9.sigmaGL_iterate_apply, h01]; exact Function.iterate_fixed (map_zero _) n
        have e10 : (((⇑(sigmaGL K L A σ))^[n] δv : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0 := by
          rw [FWI9.sigmaGL_iterate_apply, h10]; exact Function.iterate_fixed (map_zero _) n
        simp only [List.range_succ, List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]
        refine ⟨?_, ?_⟩
        · rw [FWI9.val_mul_apply, ih01, e01, mul_zero, zero_mul, add_zero]
        · rw [FWI9.val_mul_apply, ih10, e10, mul_zero, zero_mul, add_zero]
    obtain ⟨hN01, hN10⟩ := hNd (Module.finrank K L)
    have hu := FWI9.isUnit_sub_of_isRegularSemisimple N hN01 hN10 hreg
    obtain ⟨ht01, ht10⟩ := FWI9.offdiag_eq_zero_of_commute N (t : GL (Fin 2) (L ⊗[K] A)) hN01 hN10 hu hcomm

    unfold semiLocalWeight
    congr 1
    funext w
    rw [map_mul]
    refine FWI9.weight_diag_mul _ _ ?_ ?_
    · change ((Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w).comp
          (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v).toAlgEquiv.toRingEquiv.toRingHom)
          (((t : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1) = 0
      rw [ht01, map_zero]
    · change ((Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w).comp
          (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v).toAlgEquiv.toRingEquiv.toRingHom)
          (((t : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0) = 0
      rw [ht10, map_zero]

end S_AutomorphicForm_weight_localCentralizer_mul_and_semiLocalWeight_twistedCentralizer_mul_of_diagonal
end P2MW
export P2MW.S_AutomorphicForm_weight_localCentralizer_mul_and_semiLocalWeight_twistedCentralizer_mul_of_diagonal (solution)
