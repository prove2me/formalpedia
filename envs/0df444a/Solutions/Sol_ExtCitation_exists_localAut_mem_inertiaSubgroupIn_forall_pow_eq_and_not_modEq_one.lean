-- Prove2me | solution 1 for ExtCitation.exists_localAut_mem_inertiaSubgroupIn_forall_pow_eq_and_not_modEq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/ee557ac9-7d12-5739-a89f-12c888b5e3be

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_exists_localAut_mem_inertiaSubgroupIn_forall_pow_eq_and_not_modEq_one

set_option autoImplicit false
set_option maxHeartbeats 800000

open ExtCitation Polynomial

theorem solution (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ σ : primeLocalGaloisGroup (pPrime p),
      ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] ∧
      ∃ c : ℕ, (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → ResidualGaloisRep.localAut p σ ζ = ζ ^ c) ∧
        (c : ZMod p) ≠ 1 := by
  classical
  have hp : p.Prime := Fact.out

  obtain ⟨σ, hσI, hσ⟩ :=
    ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one
      (primeLocalPlace (pPrime p)) hp (liesOverPrime_primeLocalPlace (pPrime p)) 1 (-1)
  set c : ℕ := ((-1 : (ZMod (p ^ 1))ˣ) : ZMod (p ^ 1)).val with hc

  have hσI' : σ ∈ (padicPlace p).inertiaSubgroupIn ℚ := hσI
  obtain ⟨τ, hτI, hτσ⟩ :=
    ValuationSubring.exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq p σ hσI'

  haveI : NeZero ((p : ℕ) : AlgebraicClosure ℚ) := NeZero.charZero
  obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀ : AlgebraicClosure ℚ, IsPrimitiveRoot μ₀ p := by
    obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_root (cyclotomic p (AlgebraicClosure ℚ)) (by
      rw [degree_cyclotomic, Nat.totient_prime hp]
      exact_mod_cast Nat.sub_ne_zero_of_lt hp.one_lt)
    exact ⟨μ, (isRoot_cyclotomic_iff).mp hμ⟩
  have hinj : Function.Injective (padicEmbedding p) := (padicEmbedding p).toRingHom.injective
  set ζ₀ : PadicAlgCl p := padicEmbedding p μ₀ with hζ₀def
  have hζ₀ : IsPrimitiveRoot ζ₀ p := hμ₀.map_of_injective hinj
  have hσμ₀ : σ μ₀ = μ₀ ^ c := hσ μ₀ (by rw [pow_one]; exact hμ₀.pow_eq_one)

  have hτζ₀ : τ ζ₀ = ζ₀ ^ c := by
    have h1 : τ ζ₀ = padicEmbedding p (localGaloisToGlobal p τ μ₀) :=
      (padicEmbedding_localGaloisToGlobal p τ μ₀).symm
    have h2 : localGaloisToGlobal p τ μ₀ = μ₀ ^ c := by
      have h3 := hσμ₀
      rw [← hτσ] at h3
      exact h3
    calc τ ζ₀ = padicEmbedding p (localGaloisToGlobal p τ μ₀) := h1
      _ = padicEmbedding p (μ₀ ^ c) := congrArg (padicEmbedding p) h2
      _ = ζ₀ ^ c := map_pow (padicEmbedding p) μ₀ c
  refine ⟨τ, hτI, c, ?_, ?_⟩
  · intro ζ hζ
    obtain ⟨i, -, rfl⟩ := hζ₀.eq_pow_of_pow_eq_one hζ
    show τ (ζ₀ ^ i) = (ζ₀ ^ i) ^ c
    rw [map_pow, hτζ₀, ← pow_mul, ← pow_mul, mul_comm]
  ·
    haveI : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
    have hcast : (c : ZMod p) = -1 := by
      have h1 : ((c : ZMod (p ^ 1)) : ZMod (p ^ 1)) = -1 := by
        rw [hc, ZMod.natCast_zmod_val, Units.val_neg, Units.val_one]
      have h2 := congrArg (ZMod.castHom (dvd_pow_self p one_ne_zero) (ZMod p)) h1
      rwa [map_natCast, map_neg, map_one] at h2
    rw [hcast]
    exact ZMod.neg_one_ne_one

end S_ExtCitation_exists_localAut_mem_inertiaSubgroupIn_forall_pow_eq_and_not_modEq_one
end P2MW
export P2MW.S_ExtCitation_exists_localAut_mem_inertiaSubgroupIn_forall_pow_eq_and_not_modEq_one (solution)
