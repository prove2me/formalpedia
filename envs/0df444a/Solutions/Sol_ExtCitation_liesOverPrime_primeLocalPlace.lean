-- Prove2me | solution 1 for ExtCitation.liesOverPrime_primeLocalPlace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/20761b93-a213-517e-a797-d8e4c72ce569

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_liesOverPrime_primeLocalPlace

set_option autoImplicit false

open ExtCitation

namespace P2mS17LOP

theorem mem_nonunits_comap {K L : Type*} [Field K] [Field L] {B : ValuationSubring L} {f : K →+* L} {x : K} :
    x ∈ (B.comap f).nonunits ↔ f x ∈ B.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap, map_inv₀]
  constructor
  · rintro (rfl | h)
    · exact Or.inl (map_zero f)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ((map_eq_zero f).mp h)
    · exact Or.inr h

open scoped NNReal in
theorem padicPlace_liesOverPrime (q : ℕ) [Fact q.Prime] : (padicPlace q).LiesOverPrime q := by
  have hq : Valued.v ((q : ℕ) : PadicAlgCl q) = 1 / (q : ℝ≥0) := PadicAlgCl.valuation_p q
  have hq2 : (2 : ℕ) ≤ q := (Fact.out : q.Prime).two_le
  rw [ValuationSubring.LiesOverPrime, padicPlace, mem_nonunits_comap, ValuationSubring.mem_nonunits_iff,
    ← (Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one]
  change Valued.v ((padicEmbedding q) (q : AlgebraicClosure ℚ)) < 1
  rw [map_natCast, hq, div_lt_one (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hq2)]
  exact_mod_cast Nat.lt_of_lt_of_le Nat.one_lt_two hq2

end P2mS17LOP

theorem solution (q : Nat.Primes) : (primeLocalPlace q).LiesOverPrime q := by
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  exact P2mS17LOP.padicPlace_liesOverPrime q

end S_ExtCitation_liesOverPrime_primeLocalPlace
end P2MW
export P2MW.S_ExtCitation_liesOverPrime_primeLocalPlace (solution)
