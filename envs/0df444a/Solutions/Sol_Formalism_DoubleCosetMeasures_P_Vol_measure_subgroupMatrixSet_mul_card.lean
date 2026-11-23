-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Vol.measure_subgroupMatrixSet_mul_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:12.869467+00:00
-- url     : https://prove2.me/submissions/b9272be6-616e-4275-a0f3-f99f43be3412

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MeasureUniformizerMatrixSetMulCard
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_mem_piece
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_sub_mem_iff
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_mul_cong_mem_piece
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_piece_sub_mul_cong
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_measurableAdd_mat
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_meas_piece
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_measure_piece
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_measure_uniformizerMatrixSet_mul_card
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_coset_eq_of_mem_piece

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Vol
variable {F : Type} [Field F]
variable [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F] [BorelSpace F]
namespace Formalism.DoubleCosetMeasures.P.Vol
theorem _root_.solution (O : Subring F) (hO : IsOpen (O : Set F)) (ϖ : F) (hϖ : ϖ ∈ O)
    (hϖ0 : ϖ ≠ 0) (hloc : IsLocalAt O ϖ) [Finite (kF O ϖ hϖ)] (a : ℕ)
    (ν : Measure (Matrix (Fin a) (Fin a) F)) [ν.IsAddLeftInvariant]
    (J' : Subgroup (GL (Fin a) F)) (hK : congSub O ϖ a ≤ J') (hJ : J' ≤ GLint O a) :
    ν (Jset J') * (Nat.card (kF O ϖ hϖ) : ENNReal) ^ (a * a) =
      (Nat.card (J' ⧸ (congSub O ϖ a).subgroupOf J') : ENNReal) * ν (intMat O a a) := by
  classical
  haveI := measurableAdd_mat (F := F) a a
  haveI : Fintype (kF O ϖ hϖ) := Fintype.ofFinite _
  set K := (congSub O ϖ a).subgroupOf J' with hKdef
  have hoI : ∀ q : J' ⧸ K, ((Quotient.out q : J') : GL (Fin a) F) ∈ GLint O a :=
    fun q => hJ (Quotient.out q).2
  have hcos : ∀ q q' : J' ⧸ K,
      (((Quotient.out q' : J') : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) ∈
        piece O ϖ (((Quotient.out q : J') : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) → q = q' := by
    intro q q' h
    have h1 := coset_eq_of_mem_piece O ϖ hϖ hϖ0 hloc hJ _ _ h
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h1
  have hfinQ : Finite (J' ⧸ K) := by
    let f : J' ⧸ K → Fin a → Fin a → kF O ϖ hϖ := fun q i j =>
      Ideal.Quotient.mk _
        ⟨(((Quotient.out q : J') : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) i j, (hoI q).1 i j⟩
    refine Finite.of_injective f ?_
    intro q q' hqq
    apply hcos
    rw [mem_piece]
    intro i j
    exact (sub_mem_iff hϖ _ _).mpr (congrFun (congrFun hqq i) j).symm
  haveI : Fintype (J' ⧸ K) := Fintype.ofFinite _
  have hU : Jset J' = ⋃ q : J' ⧸ K,
      piece O ϖ (((Quotient.out q : J') : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) := by
    ext m
    simp only [Jset, Set.mem_image, Set.mem_iUnion, SetLike.mem_coe]
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨((⟨j, hj⟩ : J') : J' ⧸ K), ?_⟩
      have hq : ((Quotient.out ((⟨j, hj⟩ : J') : J' ⧸ K) : J') : J' ⧸ K) =
          ((⟨j, hj⟩ : J') : J' ⧸ K) := QuotientGroup.out_eq' _
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hq
      have e : ((Quotient.out ((⟨j, hj⟩ : J') : J' ⧸ K) : J') : GL (Fin a) F) *
          (((Quotient.out ((⟨j, hj⟩ : J') : J' ⧸ K) : J') : GL (Fin a) F)⁻¹ * j) = j :=
        mul_inv_cancel_left _ _
      have h1 := mul_cong_mem_piece O ϖ hϖ0 (hoI _)
        (g := ((Quotient.out ((⟨j, hj⟩ : J') : J' ⧸ K) : J') : GL (Fin a) F))
        (k := ((Quotient.out ((⟨j, hj⟩ : J') : J' ⧸ K) : J') : GL (Fin a) F)⁻¹ * j)
        (by simpa using hq)
      rwa [e] at h1
    · rintro ⟨q, hm⟩
      obtain ⟨k, hk, hkm⟩ := piece_sub_mul_cong O ϖ hϖ hϖ0 hloc (hoI q) hm
      exact ⟨_, J'.mul_mem (Quotient.out q).2 (hK hk), hkm⟩
  have hdisj : Pairwise (Function.onFun Disjoint (fun q : J' ⧸ K =>
      piece O ϖ (((Quotient.out q : J') : GL (Fin a) F) : Matrix (Fin a) (Fin a) F))) := by
    intro q q' hne
    rw [Function.onFun, Set.disjoint_left]
    intro y h1 h2
    apply hne
    apply hcos
    rw [mem_piece] at h1 h2 ⊢
    intro i j
    obtain ⟨o, ho, e⟩ := h1 i j
    obtain ⟨o', ho', e'⟩ := h2 i j
    exact ⟨o - o', O.sub_mem ho ho', by linear_combination e - e'⟩
  have hJ' : ν (Jset J') = (Nat.card (J' ⧸ K) : ENNReal) * ν (IIset O ϖ) := by
    rw [hU, measure_iUnion hdisj (fun q => meas_piece O hO ϖ hϖ0 _), tsum_fintype]
    simp only [measure_piece]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  rw [hJ', mul_assoc, measure_uniformizerMatrixSet_mul_card O hO ϖ hϖ hϖ0 a a ν]
end Formalism.DoubleCosetMeasures.P.Vol
