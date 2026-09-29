-- Prove2me | solution 1 for GaloisRepAdic.exists_basis_iSup_range_sub_one_eq_span_of_isOrdinaryAt_of_detIsCyclotomic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/597f1dcc-4ed8-5968-b46f-059f9d58d1e9

import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_exists_basis_iSup_range_sub_one_eq_span_of_isOrdinaryAt_of_detIsCyclotomic

set_option autoImplicit false

open IsLocalRing

theorem solution
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ρ : GaloisRepAdic k) (hdet : ρ.DetIsCyclotomic p) (hord : ρ.IsOrdinaryAt p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) :
    ∃ b : Module.Basis (Fin 2) k ρ.V,
      (⨆ σ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρ.ρ σ - LinearMap.id)) = k ∙ b 0 ∧
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : ℕ,
        (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) → ρ.ρ σ (b 0) = (a : k) • b 0 := by
  have hp : p.Prime := Fact.out
  obtain ⟨L, ⟨b, rfl⟩, hD, hI⟩ := hord P hP
  have hp0 : (p : k) = 0 := by
    have h1 := hdet.1
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not] at h1
  have key : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : ℕ,
      (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) → ρ.ρ σ (b 0) = (a : k) • b 0 := by
    intro σ hσ a hμ
    have h0 : ρ.ρ σ (b 0) ∈ k ∙ b 0 := by
      have h1 := hI σ hσ (b 0)
      have hb : b 0 ∈ k ∙ b 0 := Submodule.mem_span_singleton_self _
      simpa using Submodule.add_mem _ h1 hb
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h0
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp (hI σ hσ (b 1))
    have e1 : ρ.ρ σ (b 1) = d • b 0 + b 1 := by rw [hd]; abel
    have hdetc : LinearMap.det (ρ.ρ σ) = c := by
      rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
      simp only [LinearMap.toMatrix_apply, ← hc, e1, map_smul, map_add, Module.Basis.repr_self,
        Finsupp.smul_apply, Finsupp.add_apply, Finsupp.single_apply]
      simp
    have hmem := hdet.2 1 σ a (fun μ hμ' => hμ μ (by simpa using hμ'))
    have hbot : Ideal.span {((p ^ 1 : ℕ) : k)} = ⊥ := Ideal.span_singleton_eq_bot.mpr (by simp [hp0])
    rw [hbot, Ideal.mem_bot, sub_eq_zero, hdetc] at hmem
    rw [← hc, hmem]
  refine ⟨b, le_antisymm ?_ ?_, key⟩
  · refine iSup₂_le fun σ hσ => ?_
    rintro _ ⟨v, rfl⟩
    simpa using hI σ hσ v
  · have h2p : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
    have hcop : Nat.Coprime 2 (p ^ 1) := by
      rw [pow_one]; exact (Nat.coprime_primes Nat.prime_two hp).mpr (ne_of_lt h2p)
    obtain ⟨σ₀, hσ₀, hσ₀μ⟩ :=
      ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one P hp hP 1
        (ZMod.unitOfCoprime 2 hcop)
    have hval : ((ZMod.unitOfCoprime 2 hcop : (ZMod (p ^ 1))ˣ) : ZMod (p ^ 1)).val = 2 := by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, pow_one]
      exact Nat.mod_eq_of_lt h2p
    have h2 := key σ₀ hσ₀ 2 (fun μ hμ => by
      have h3 := hσ₀μ μ (by simpa using hμ)
      rwa [hval] at h3)
    refine (Submodule.span_singleton_le_iff_mem _ _).mpr ?_
    refine Submodule.mem_iSup_of_mem σ₀ (Submodule.mem_iSup_of_mem hσ₀ ⟨b 0, ?_⟩)
    simp only [LinearMap.sub_apply, LinearMap.id_apply, h2, Nat.cast_ofNat, two_smul,
      add_sub_cancel_right]

end S_GaloisRepAdic_exists_basis_iSup_range_sub_one_eq_span_of_isOrdinaryAt_of_detIsCyclotomic
end P2MW
export P2MW.S_GaloisRepAdic_exists_basis_iSup_range_sub_one_eq_span_of_isOrdinaryAt_of_detIsCyclotomic (solution)
