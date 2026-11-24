-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_lowerTriIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:51:53.815484+00:00
-- url     : https://prove2.me/submissions/978d82ca-24b7-43d8-8683-072029cb6f51

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCassemLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnInterlacedLowerTri
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_interlaced_lowerTri
import Theorems.Thm_Formalism_GradedWeylDivisibility_lcassem_sub_lt
import Theorems.Thm_Formalism_GradedWeylDivisibility_leadInterlaced
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_sSBasis
import Theorems.Thm_Formalism_GradedWeylDivisibility_span_map_weightBasis_eq_dualWeyl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
open scoped MonomialOrder
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution : LowerTriIntegral := by
  classical
  intro r n ν
  haveI := (colLex r n).wellFoundedLT_syn
  obtain ⟨b, hbB, hbdeg⟩ := sSBasis ℤ r n ν
  have hBmem : ∀ i, intQ r n (b i) ∈ dualWeyl ℚ r n ν := by
    intro i
    rw [← span_map_weightBasis_eq_dualWeyl (K := ℚ) hbB]
    apply Submodule.subset_span
    exact ⟨i, by rw [algebraMap_int_eq]; rfl⟩
  suffices H : ∀ s : (colLex r n).syn, ∀ Q : MvPolynomial (Fin r × Fin n) ℚ,
      (colLex r n).toSyn ((colLex r n).degree Q) = s → Q ∈ dualWeyl ℚ r n ν →
      (∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → ∃ z : ℤ, coeff e Q = z) →
      ∃ Q' : MvPolynomial (Fin r × Fin n) ℤ, Q = intQ r n Q' by
    intro Q hQ hint
    exact H _ Q rfl hQ hint
  intro s
  induction s using WellFoundedLT.induction with
  | ind s ih =>
    intro Q hs hQ hint
    by_cases hQ0 : Q = 0
    · exact ⟨0, by rw [hQ0, map_zero]⟩
    set m := (colLex r n).degree Q with hm
    have hInt : Interlaced m := leadInterlaced ℚ r n ν Q hQ hQ0
    have hLT : LowerTri m := qn_interlaced_lowerTri m hInt
    have hcol : ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t := by
      have hhom : IsWeightedHomogeneous (colW r n) Q ν :=
        (mem_weightedHomogeneousSubmodule _ _ _ _).1 (Submodule.mem_inf.1 hQ).1
      have hw : Finsupp.weight (colW r n) m = ν :=
        hhom ((colLex r n).leadingCoeff_ne_zero_iff.2 hQ0)
      intro t
      rw [← hw]
      simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_prod_type, colW, Pi.single_apply]
    let mi : ssIdx r n ν := ⟨m, hInt, hcol⟩
    obtain ⟨hbd, hblc, -⟩ := hbdeg mi
    set B := intQ r n (b mi) with hB
    have hBmap : B = map (Int.castRingHom ℚ) (b mi) := rfl
    have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
    have hBsupp : B.support = (b mi).support := by
      rw [hBmap]
      exact support_map_of_injective _ hinj
    have hBdeg : (colLex r n).degree B = m := by
      have h1 : (colLex r n).degree (b mi) = m := hbd
      rw [← h1]
      unfold MonomialOrder.degree
      rw [hBsupp]
    have hBlc : (colLex r n).leadingCoeff B = 1 := by
      unfold MonomialOrder.leadingCoeff
      rw [hBdeg, hBmap, coeff_map]
      have h1 : (colLex r n).degree (b mi) = m := hbd
      have h2 : (b mi).coeff ((colLex r n).degree (b mi)) = 1 := hblc
      rw [h1] at h2
      rw [h2, map_one]
    obtain ⟨z, hz⟩ := hint m hLT
    have hlcQ : (colLex r n).leadingCoeff Q = (z : ℚ) := hz
    set Q1 := Q - (colLex r n).leadingCoeff Q • B with hQ1
    have hQ1mem : Q1 ∈ dualWeyl ℚ r n ν :=
      Submodule.sub_mem _ hQ (Submodule.smul_mem _ _ (hBmem mi))
    have hQ1int : ∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → ∃ z' : ℤ, coeff e Q1 = z' := by
      intro e he
      obtain ⟨w, hw⟩ := hint e he
      refine ⟨w - z * (b mi).coeff e, ?_⟩
      rw [hQ1, coeff_sub, coeff_smul, hw, hlcQ, hBmap, coeff_map]
      push_cast
      simp [smul_eq_mul]
    have hfinal : ∀ Q1' : MvPolynomial (Fin r × Fin n) ℤ, Q1 = intQ r n Q1' →
        ∃ Q' : MvPolynomial (Fin r × Fin n) ℤ, Q = intQ r n Q' := by
      intro Q1' h
      refine ⟨Q1' + z • b mi, ?_⟩
      rw [map_add, map_zsmul, ← h, ← hB, hQ1, hlcQ, Int.cast_smul_eq_zsmul]
      abel
    by_cases hQ10 : Q1 = 0
    · exact hfinal 0 (by rw [hQ10, map_zero])
    · have hlt := lcassem_sub_lt (colLex r n) (hBdeg.trans hm) hBlc hQ10
      obtain ⟨Q1', h⟩ := ih _ (by rw [← hs]; exact hlt) Q1 rfl hQ1mem hQ1int
      exact hfinal Q1' h
end Formalism.InvariantFactorPaths.ColumnFamilies
