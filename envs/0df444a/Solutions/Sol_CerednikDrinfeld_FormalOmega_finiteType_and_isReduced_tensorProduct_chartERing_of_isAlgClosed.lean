-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.finiteType_and_isReduced_tensorProduct_chartERing_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/889a358b-7395-556b-a609-b49dd52ad500

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Theorems.Thm_CerednikDrinfeld_FormalOmega_chartERing_existsUnique_isPushout_baseChange
import Theorems.Thm_CerednikDrinfeld_FormalOmega_chartERing_isReduced_quotient_level_zero
import Theorems.Thm_WittVector_nonempty_ringEquiv_quotient_pIdeal_of_perfectRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_finiteType_and_isReduced_tensorProduct_chartERing_of_isAlgClosed

set_option autoImplicit false

open CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic TensorProduct

open CategoryTheory AlgebraicGeometry

namespace OmegaRingSol

theorem finiteType_chartERing (R : Type) [CommRing R] (π : R) (q : ℕ) :
    Algebra.FiniteType R (chartERing R π q) := by
  haveI h1 : Algebra.FiniteType R (edgeQuot R π) :=
    Algebra.FiniteType.of_surjective (edgeQuot.mk R π)
      (show Function.Surjective (Ideal.Quotient.mkₐ R (Ideal.span {edgeRel R π})) from
        Ideal.Quotient.mkₐ_surjective R _)
  haveI h2 : Algebra.FiniteType (edgeQuot R π) (chartERing R π q) := inferInstance
  exact Algebra.FiniteType.trans h1 h2

theorem isReduced_chartERing_zero (K : Type) [CommRing K] (hK : IsField K) (q : ℕ) :
    IsReduced (chartERing K 0 q) := by
  have hmax : (Ideal.span ({(0 : K)} : Set K)).IsMaximal := by
    rw [Ideal.span_singleton_zero, Ideal.Quotient.maximal_ideal_iff_isField_quotient]
    exact MulEquiv.isField hK (RingEquiv.quotientBot K).toMulEquiv
  haveI hq := CerednikDrinfeld.FormalOmega.chartERing.isReduced_quotient_level_zero K 0 q hmax
  have hI : Ideal.span {(algebraMap K (chartERing K 0 q) 0) ^ (0 + 1)} = ⊥ := by
    rw [map_zero, zero_add, pow_one, Ideal.span_singleton_zero]
  exact isReduced_of_injective
    (Ideal.Quotient.mk (Ideal.span {(algebraMap K (chartERing K 0 q) 0) ^ (0 + 1)}))
    ((RingHom.injective_iff_ker_eq_bot _).mpr (by rw [Ideal.mk_ker, hI]))

theorem isReduced_chartERing_of_eq_zero (K : Type) [CommRing K] (hK : IsField K) (π : K) (hπ : π = 0) (q : ℕ) :
    IsReduced (chartERing K π q) := by
  subst hπ
  exact isReduced_chartERing_zero K hK q

end OmegaRingSol

open OmegaRingSol in
theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    [Algebra ℤ_[p] (WittVector p k ⧸ CerednikDrinfeld.SpecialFormal.pIdeal p (WittVector p k))] :
    Algebra.FiniteType (WittVector p k ⧸ CerednikDrinfeld.SpecialFormal.pIdeal p (WittVector p k))
        ((WittVector p k ⧸ CerednikDrinfeld.SpecialFormal.pIdeal p (WittVector p k)) ⊗[ℤ_[p]]
          chartERing ℤ_[p] (p : ℤ_[p]) p) ∧
      IsReduced ((WittVector p k ⧸ CerednikDrinfeld.SpecialFormal.pIdeal p (WittVector p k)) ⊗[ℤ_[p]]
          chartERing ℤ_[p] (p : ℤ_[p]) p) := by

  let K0 : Type := WittVector p k ⧸ CerednikDrinfeld.SpecialFormal.pIdeal p (WittVector p k)
  haveI : Algebra.FiniteType ℤ_[p] (chartERing ℤ_[p] (p : ℤ_[p]) p) := finiteType_chartERing ℤ_[p] _ p
  refine ⟨Algebra.FiniteType.baseChange _, ?_⟩

  haveI : PerfectRing k p := PerfectField.toPerfectRing p
  obtain ⟨e0⟩ := WittVector.nonempty_ringEquiv_quotient_pIdeal_of_perfectRing p k
  have hF : IsField K0 := MulEquiv.isField (Field.toIsField k) e0.symm.toMulEquiv

  have hπ : algebraMap ℤ_[p] K0 (p : ℤ_[p]) = 0 := by
    rw [map_natCast]
    show ((p : ℕ) : WittVector p k ⧸ CerednikDrinfeld.SpecialFormal.pIdeal p (WittVector p k)) = 0
    rw [← map_natCast (Ideal.Quotient.mk (CerednikDrinfeld.SpecialFormal.pIdeal p (WittVector p k))) p,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _

  haveI hred : IsReduced (chartERing K0 (algebraMap ℤ_[p] K0 (p : ℤ_[p])) p) :=
    isReduced_chartERing_of_eq_zero K0 hF _ hπ p

  obtain ⟨φ, -, -, -, hpush, -⟩ :=
    CerednikDrinfeld.FormalOmega.chartERing.existsUnique_isPushout_baseChange ℤ_[p] (p : ℤ_[p]) p K0
  let iso := hpush.isColimit.coconePointUniqueUpToIso
    (CommRingCat.pushoutCoconeIsColimit ℤ_[p] K0 (chartERing ℤ_[p] (p : ℤ_[p]) p))
  let e : chartERing K0 (algebraMap ℤ_[p] K0 (p : ℤ_[p])) p ≃+* K0 ⊗[ℤ_[p]] chartERing ℤ_[p] (p : ℤ_[p]) p :=
    iso.commRingCatIsoToRingEquiv
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective

end S_CerednikDrinfeld_FormalOmega_finiteType_and_isReduced_tensorProduct_chartERing_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_finiteType_and_isReduced_tensorProduct_chartERing_of_isAlgClosed (solution)
