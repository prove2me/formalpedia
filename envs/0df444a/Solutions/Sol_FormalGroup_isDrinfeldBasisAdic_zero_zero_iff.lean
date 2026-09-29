-- Prove2me | solution 1 for FormalGroup.isDrinfeldBasisAdic_zero_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/c7188776-05d9-59ff-9b4f-a2d4c2f44a0c

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_isDrinfeldBasisAdic_zero_zero_iff

set_option autoImplicit false

open FormalGroup

namespace QuotIsoAux

open Filter Topology

theorem mv_eval₂_zero {R₀ : Type*} [CommRing R₀] [UniformSpace R₀] [DiscreteUniformity R₀]
    {A : Type*} [CommRing A] [Algebra R₀ A] (I : Ideal A) [IsAdicComplete I A]
    {σ : Type*} [Finite σ] (f : MvPowerSeries σ R₀) :
    (letI : WithIdeal A := ⟨I⟩; MvPowerSeries.eval₂ (algebraMap R₀ A) (0 : σ → A) f) =
      algebraMap R₀ A (MvPowerSeries.constantCoeff f) := by
  classical
  letI : WithIdeal A := ⟨I⟩
  have hI : IsAdic I := rfl
  obtain ⟨hcs, ht2⟩ := hI.isAdicComplete_iff.mp (inferInstance : IsAdicComplete I A)
  have hφ : Continuous (algebraMap R₀ A) := continuous_of_discreteTopology
  have hsum := MvPowerSeries.hasSum_eval₂ hφ (MvPowerSeries.HasEval.zero) f
  refine hsum.unique ?_
  convert hasSum_single
    (f := fun d : σ →₀ ℕ => algebraMap R₀ A (MvPowerSeries.coeff d f) * d.prod fun s e => (0 : σ → A) s ^ e)
    0 ?_ using 1
  · simp
  · intro d hd
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd
    have hi' : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
    rw [Finsupp.prod, Finset.prod_eq_zero hi (by simp [hi']), mul_zero]

theorem eval_zero_zero {T : Type*} [CommRing T] (I : Ideal T) [IsAdicComplete I T] (F : FormalGroup T) :
    (letI : WithIdeal T := ⟨I⟩; F.eval (0 : T) 0) = 0 := by
  have hv : (![(0 : T), 0] : Fin 2 → T) = 0 := by
    funext i; fin_cases i <;> rfl
  have h := @mv_eval₂_zero T _ ⊥ inferInstance T _ _ I _ (Fin 2) _ F.toPowerSeries
  rw [F.zero_constantCoeff, map_zero] at h
  unfold FormalGroup.eval
  rw [hv]
  exact h

theorem evalNSMul_zero_right {T : Type*} [CommRing T] (I : Ideal T) [IsAdicComplete I T]
    (F : FormalGroup T) (n : ℕ) :
    (letI : WithIdeal T := ⟨I⟩; F.evalNSMul n (0 : T)) = 0 := by
  letI : WithIdeal T := ⟨I⟩
  induction n with
  | zero => rfl
  | succ n ih => rw [FormalGroup.evalNSMul_succ, ih]; exact eval_zero_zero I F

theorem linCombAdic_zero_zero {T : Type*} [CommRing T] (I : Ideal T) [IsAdicComplete I T]
    (F : FormalGroup T) (a b : ℕ) :
    F.linCombAdic I 0 0 a b = 0 := by
  unfold FormalGroup.linCombAdic FormalGroup.linComb
  rw [evalNSMul_zero_right I F a, evalNSMul_zero_right I F b]
  exact eval_zero_zero I F

end QuotIsoAux

theorem solution
    {T : Type*} [CommRing T] (I : Ideal T) [IsAdicComplete I T] (F : FormalGroup T) (q : ℕ) :
    F.IsDrinfeldBasisAdic I q 0 0 ↔
      ∃ u : PowerSeries T, IsUnit u ∧ F.nthSeries q = u * PowerSeries.X ^ (q * q) := by
  have hdiv : F.drinfeldDivisorAdic I q 0 0 = PowerSeries.X ^ (q * q) := by
    show (∏ a ∈ Finset.range q, ∏ b ∈ Finset.range q,
        (PowerSeries.X - PowerSeries.C (F.linCombAdic I 0 0 a b))) = _
    simp only [QuotIsoAux.linCombAdic_zero_zero, map_zero, sub_zero, Finset.prod_const,
      Finset.card_range]
    exact (pow_mul PowerSeries.X q q).symm
  rw [FormalGroup.isDrinfeldBasisAdic_iff, hdiv]

end S_FormalGroup_isDrinfeldBasisAdic_zero_zero_iff
end P2MW
export P2MW.S_FormalGroup_isDrinfeldBasisAdic_zero_zero_iff (solution)
