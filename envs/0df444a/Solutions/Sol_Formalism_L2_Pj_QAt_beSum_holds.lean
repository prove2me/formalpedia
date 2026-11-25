-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.beSum_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:15:42.794345+00:00
-- url     : https://prove2.me/submissions/0d3e48c2-f637-4495-ac10-e8c1a99f5a82

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinitePlaceArcs_BeSumStatement
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinitePlaceArcs_BeSumPf
import Theorems.Thm_Formalism_L2_Pj_QAt_BeSumPf_vla_ne_zero_iff
import Theorems.Thm_Formalism_L2_Pj_QAt_BeSumPf_sum_vla_log_fin
import Theorems.Thm_Formalism_L2_Pj_QAt_BeSumPf_absNorm_span_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
open NumberField IsDedekindDomain
open BeSumPf
namespace Formalism.L2.Pj.QAt
theorem _root_.solution : BeSumStatement := by
  intro E K _ _ _ _ n' A hn
  have hspan : ∀ k : ℕ, k ≠ 0 → Ideal.span {(k : 𝓞 K)} ≠ 0 := by
    intro k hk
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hk
  have hd0 : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero E)
  have hI1 : discAt E K ≠ 0 := hspan _ hd0
  have hI2 : Ideal.span {(n' : 𝓞 K)} ≠ 0 := hspan _ hn.ne'
  have hfin := (Ideal.finite_factors hI1).union (Ideal.finite_factors hI2)
  have hsupp : Function.support (beOf E (K := K) n' A) ⊆
      {v | v.asIdeal ∣ discAt E K} ∪ {v | v.asIdeal ∣ Ideal.span {(n' : 𝓞 K)}} := by
    intro v hv
    rw [Function.mem_support] at hv
    by_contra hc
    apply hv
    have h1 : vla v (discAt E K) = 0 := by
      by_contra h
      exact hc (Or.inl ((vla_ne_zero_iff v hI1).mp h))
    have h2 : vla v (Ideal.span {(n' : 𝓞 K)}) = 0 := by
      by_contra h
      exact hc (Or.inr ((vla_ne_zero_iff v hI2).mp h))
    simp [beOf, mOf, h1, h2]
  refine ⟨hfin.subset hsupp, ?_⟩
  have hs1 : ∀ v, vla v (discAt E K) ≠ 0 → v ∈ hfin.toFinset := fun v h => by
    rw [Set.Finite.mem_toFinset]
    exact Or.inl ((vla_ne_zero_iff v hI1).mp h)
  have hs2 : ∀ v, vla v (Ideal.span {(n' : 𝓞 K)}) ≠ 0 → v ∈ hfin.toFinset := fun v h => by
    rw [Set.Finite.mem_toFinset]
    exact Or.inr ((vla_ne_zero_iff v hI2).mp h)
  have hsum : ∑ᶠ la, beOf E (K := K) n' A la * Real.log (Ideal.absNorm la.asIdeal : ℝ) =
      ∑ la ∈ hfin.toFinset, beOf E (K := K) n' A la * Real.log (Ideal.absNorm la.asIdeal : ℝ) := by
    apply finsum_eq_sum_of_support_subset
    intro v hv
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    apply hsupp
    rw [Function.mem_support] at hv ⊢
    intro h
    apply hv
    rw [h, zero_mul]
  rw [hsum]
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  rw [div_le_iff₀ hK]
  have hle : ∑ la ∈ hfin.toFinset, beOf E (K := K) n' A la * Real.log (Ideal.absNorm la.asIdeal : ℝ) ≤
      (A : ℝ) * (∑ la ∈ hfin.toFinset, (vla la (discAt E K) : ℝ) * Real.log (Ideal.absNorm la.asIdeal : ℝ) +
        ∑ la ∈ hfin.toFinset, (vla la (Ideal.span {(n' : 𝓞 K)}) : ℝ) *
          Real.log (Ideal.absNorm la.asIdeal : ℝ)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum (fun v _ => ?_)
    have hl : 0 ≤ Real.log (Ideal.absNorm v.asIdeal : ℝ) := Real.log_natCast_nonneg _
    have hm : (mOf E n' v : ℝ) ≤ (vla v (discAt E K) : ℝ) + (vla v (Ideal.span {(n' : 𝓞 K)}) : ℝ) := by
      unfold mOf
      push_cast
      exact max_le_add_of_nonneg (by positivity) (by positivity)
    unfold beOf
    calc (A : ℝ) * (mOf E n' v : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ)
        ≤ (A : ℝ) * ((vla v (discAt E K) : ℝ) + (vla v (Ideal.span {(n' : 𝓞 K)}) : ℝ)) *
            Real.log (Ideal.absNorm v.asIdeal : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg A)) hl
      _ = _ := by ring
  refine hle.trans (le_of_eq ?_)
  rw [sum_vla_log_fin _ hI1 _ hs1, sum_vla_log_fin _ hI2 _ hs2]
  have e1 : Ideal.absNorm (discAt E K) = (discr E).natAbs ^ Module.finrank ℚ K :=
    absNorm_span_nat (discr E).natAbs
  rw [e1, absNorm_span_nat n', Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow]
  have e2 : (((discr E).natAbs : ℕ) : ℝ) = |((discr E : ℤ) : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [e2]
  ring
end Formalism.L2.Pj.QAt
