-- Prove2me | solution 1 for CerednikDrinfeld.EdgeFamily.isReduced_edgeRingCharP_wittVector_quotient_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/d6ea5f5a-a8d1-53a2-a86e-e7a86c8dd2df

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_EdgeFamily_isReduced_edgeRingCharP_wittVector_quotient_of_isAlgClosed

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k] :
    IsReduced (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) := by
  classical

  have hmax : (pIdeal p (WittVector p k)).IsMaximal := by
    have h := (WittVector.irreducible p (k := k)).maximalIdeal_eq
    rw [pIdeal, ← h]
    exact IsLocalRing.maximalIdeal.isMaximal (WittVector p k)
  letI hF : Field (WittVector p k ⧸ pIdeal p (WittVector p k)) := @Ideal.Quotient.field _ _ (pIdeal p (WittVector p k)) hmax

  have hrel : FormalOmega.edgeRel (WittVector p k ⧸ pIdeal p (WittVector p k)) (0 : (WittVector p k ⧸ pIdeal p (WittVector p k))) =
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) (WittVector p k ⧸ pIdeal p (WittVector p k))) * MvPolynomial.X 1 := by
    simp [FormalOmega.edgeRel]
  have hX0 : Prime (MvPolynomial.X (R := (WittVector p k ⧸ pIdeal p (WittVector p k))) (0 : Fin 2)) := MvPolynomial.X_prime
  have hX1 : Prime (MvPolynomial.X (R := (WittVector p k ⧸ pIdeal p (WittVector p k))) (1 : Fin 2)) := MvPolynomial.X_prime
  have hI : Ideal.span {FormalOmega.edgeRel (WittVector p k ⧸ pIdeal p (WittVector p k)) (0 : (WittVector p k ⧸ pIdeal p (WittVector p k)))} =
      Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) (WittVector p k ⧸ pIdeal p (WittVector p k)))} ⊓ Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) (WittVector p k ⧸ pIdeal p (WittVector p k)))} := by
    rw [hrel]
    apply le_antisymm
    · rw [Ideal.span_singleton_le_iff_mem, Submodule.mem_inf, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
      exact ⟨dvd_mul_right _ _, dvd_mul_left _ _⟩
    · intro f hf
      rw [Submodule.mem_inf, Ideal.mem_span_singleton, Ideal.mem_span_singleton] at hf
      obtain ⟨h0, h1⟩ := hf
      rw [Ideal.mem_span_singleton]
      obtain ⟨g, rfl⟩ := h1
      rcases hX0.dvd_or_dvd h0 with h | h
      · exfalso
        rw [MvPolynomial.X_dvd_X] at h
        exact absurd h (by decide)
      · have h2 := mul_dvd_mul_left (MvPolynomial.X (R := (WittVector p k ⧸ pIdeal p (WittVector p k))) (1 : Fin 2)) h
        rwa [mul_comm (MvPolynomial.X (R := (WittVector p k ⧸ pIdeal p (WittVector p k))) (1 : Fin 2)) (MvPolynomial.X 0)] at h2
  have hrad : (Ideal.span {FormalOmega.edgeRel (WittVector p k ⧸ pIdeal p (WittVector p k)) (0 : (WittVector p k ⧸ pIdeal p (WittVector p k)))}).IsRadical := by
    rw [hI]
    exact (Ideal.IsPrime.isRadical ((Ideal.span_singleton_prime hX0.ne_zero).mpr hX0)).inf
      (Ideal.IsPrime.isRadical ((Ideal.span_singleton_prime hX1.ne_zero).mpr hX1))
  haveI : IsReduced (FormalOmega.edgeQuot (WittVector p k ⧸ pIdeal p (WittVector p k)) (0 : (WittVector p k ⧸ pIdeal p (WittVector p k)))) := by
    unfold FormalOmega.edgeQuot
    exact (Ideal.isRadical_iff_quotient_reduced _).mp hrad
  exact inferInstance

end S_CerednikDrinfeld_EdgeFamily_isReduced_edgeRingCharP_wittVector_quotient_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_EdgeFamily_isReduced_edgeRingCharP_wittVector_quotient_of_isAlgClosed (solution)
