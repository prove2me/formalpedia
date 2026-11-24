-- Prove2me | solution 1 for Formalism.MainNotions.FormalGroupSystem.Pf.Gen.jp_subst_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:40:08.01614+00:00
-- url     : https://prove2.me/submissions/d35367ce-b6b0-4f7b-9d5c-8fbdb8a5487e

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_CoeffProdRename
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_JpSubstExpand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.FormalGroupSystem.Pf Formalism.MainNotions.FormalGroupSystem.Pf.Gen
open Finset
namespace Formalism.MainNotions.FormalGroupSystem.Pf.Gen
theorem _root_.solution {K A σ τ : Type} [CommRing K] [CommRing A] [Algebra K A] (Q : MvPolynomial σ A)
    (F : MvPowerSeries σ K) (a : τ → MvPowerSeries σ K) (ha : MvPowerSeries.HasSubst a) (U : MvPowerSeries τ K) :
    ∃ B : Finset (τ →₀ ℕ), jp Q (F * MvPowerSeries.subst a U) =
      ∑ β ∈ B, MvPowerSeries.coeff β U • jp Q (F * β.prod fun s e => a s ^ e) := by
  classical
  refine ⟨Q.support.biUnion fun κ => (Finset.HasAntidiagonal.antidiagonal κ).biUnion fun pq =>
    (MvPowerSeries.coeff_subst_finite ha U pq.2).toFinset, ?_⟩
  set B := Q.support.biUnion fun κ => (Finset.HasAntidiagonal.antidiagonal κ).biUnion fun pq =>
    (MvPowerSeries.coeff_subst_finite ha U pq.2).toFinset with hB
  have hq : ∀ κ ∈ Q.support, ∀ pq ∈ Finset.HasAntidiagonal.antidiagonal κ,
      MvPowerSeries.coeff pq.2 (MvPowerSeries.subst a U) =
        ∑ β ∈ B, MvPowerSeries.coeff β U * MvPowerSeries.coeff pq.2 (β.prod fun s e => a s ^ e) := by
    intro κ hκ pq hpq
    rw [MvPowerSeries.coeff_subst ha, finsum_eq_sum_of_support_subset (s := B)]
    · simp only [smul_eq_mul]
    · intro β hβ
      rw [Finset.mem_coe, hB, Finset.mem_biUnion]
      exact ⟨κ, hκ, Finset.mem_biUnion.mpr ⟨pq, hpq,
        (MvPowerSeries.coeff_subst_finite ha U pq.2).mem_toFinset.mpr hβ⟩⟩
  have hκ : ∀ κ ∈ Q.support, MvPowerSeries.coeff κ (F * MvPowerSeries.subst a U) =
      ∑ β ∈ B, MvPowerSeries.coeff β U * MvPowerSeries.coeff κ (F * β.prod fun s e => a s ^ e) := by
    intro κ hκ
    rw [MvPowerSeries.coeff_mul]
    simp_rw [MvPowerSeries.coeff_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun pq hpq => ?_
    rw [hq κ hκ pq hpq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  unfold jp
  have hL : ∑ κ ∈ Q.support, (((fac κ : ℕ) : K) * MvPowerSeries.coeff κ (F * MvPowerSeries.subst a U)) •
        MvPolynomial.coeff κ Q =
      ∑ κ ∈ Q.support, ∑ β ∈ B, (((fac κ : ℕ) : K) * (MvPowerSeries.coeff β U *
        MvPowerSeries.coeff κ (F * β.prod fun s e => a s ^ e))) • MvPolynomial.coeff κ Q := by
    refine Finset.sum_congr rfl fun κ hκ' => ?_
    rw [hκ κ hκ', Finset.mul_sum, Finset.sum_smul]
  rw [hL, Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [smul_smul]
  congr 1
  ring
end Formalism.MainNotions.FormalGroupSystem.Pf.Gen
