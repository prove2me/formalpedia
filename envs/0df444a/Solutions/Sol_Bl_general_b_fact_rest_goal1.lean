-- Prove2me | solution 1 for Bl.general_b_fact_rest.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:59.485049+00:00
-- url     : https://prove2.me/submissions/9f5f6388-fa62-42f4-8bdb-13d84e00fc0d

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRest_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open Bl Bl.general_b_fact_rest
namespace Bl.general_b_fact_rest
theorem _root_.solution :
  ∀ {R : Type u_1} [inst : CommRing.{u_1} R] [inst_1 : IsLocalRing.{u_1} R] [IsNoetherianRing.{u_1} R] {M : Type u_2}
  [inst_3 : AddCommGroup.{u_2} M] [inst_4 : Module.{u_1, u_2} R M] [Module.Finite.{u_1, u_2} R M] {p : Ideal.{u_1} R},
  Membership.mem.{u_1, u_1} (associatedPrimes.{u_1, u_2} R M) p →
    ∀ {x : R},
      Membership.mem.{u_1, u_1} (IsLocalRing.maximalIdeal.{u_1} R) x →
        IsSMulRegular.{u_1, u_2} M x →
          Exists.{u_1 + 1} fun (q : Ideal.{u_1} R) ↦
            And (Membership.mem.{u_1, u_1} (associatedPrimes.{u_1, u_2} R (QuotSMulTop.{u_2, u_1} x M)) q)
              (And (LT.lt.{u_1} p q) (And (Membership.mem.{u_1, u_1} q x) (Not (Membership.mem.{u_1, u_1} p x)))) := by
  intro R _ _ _ M _ _ _ p hp x hx hreg
  open Pointwise in
  · rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hp
    obtain ⟨hpp, m0, rfl⟩ := hp
    have hm0 : m0 ≠ 0 := by
      rintro rfl
      apply hpp.ne_top
      rw [Ideal.eq_top_iff_one, Submodule.mem_colon_singleton, smul_zero]
      exact Submodule.zero_mem _
    have hxp : x ∉ (⊥ : Submodule R M).colon {m0} := by
      intro h
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at h
      exact hm0 (hreg (h.trans (smul_zero x).symm))
    set N : Submodule R M := Submodule.torsionBySet R M ((⊥ : Submodule R M).colon {m0} : Set R) with hN
    have hNmem : ∀ n, n ∈ N ↔ ∀ r ∈ (⊥ : Submodule R M).colon {m0}, r • n = 0 := by
      intro n
      rw [hN, Submodule.mem_torsionBySet_iff]
      exact ⟨fun h r hr => h ⟨r, hr⟩, fun h a => h a.1 a.2⟩
    have hm0N : m0 ∈ N := by
      rw [hNmem]
      intro r hr
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hr
      exact hr
    have hex : ∃ n ∈ N, n ∉ x • (⊤ : Submodule R M) := by
      by_contra hcon
      push Not at hcon
      have hle : N ≤ Ideal.span {x} • N := by
        intro n hn
        obtain ⟨m', -, hm'⟩ := (Submodule.mem_smul_pointwise_iff_exists n x ⊤).1 (hcon n hn)
        have hm'N : m' ∈ N := by
          rw [hNmem] at hn ⊢
          intro r hr
          apply hreg
          show x • (r • m') = x • 0
          rw [smul_comm, hm', hn r hr, smul_zero]
        rw [← hm']
        exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) hm'N
      have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) N
        (IsNoetherian.noetherian N) hle
        (((Ideal.span_singleton_le_iff_mem _).2 hx).trans (IsLocalRing.maximalIdeal_le_jacobson _))
      apply hm0
      rw [hbot] at hm0N
      exact (Submodule.mem_bot R).1 hm0N
    obtain ⟨n, hnN, hnx⟩ := hex
    set z : QuotSMulTop x M := Submodule.Quotient.mk n with hz
    have hz0 : z ≠ 0 := by
      rw [hz, Ne, Submodule.Quotient.mk_eq_zero]
      exact hnx
    obtain ⟨q, hq, hqle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R z hz0
    have hxq : x ∈ q := by
      apply hqle
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot, hz, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_pointwise_smul n x ⊤ trivial
    have hpq : (⊥ : Submodule R M).colon {m0} ≤ q := by
      intro r hr
      apply hqle
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot, hz, ← Submodule.Quotient.mk_smul,
        (hNmem n).1 hnN r hr, Submodule.Quotient.mk_zero]
    exact ⟨q, hq, lt_of_le_of_ne hpq (fun h => hxp (h ▸ hxq)), hxq, hxp⟩
end Bl.general_b_fact_rest
