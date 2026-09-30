-- Prove2me | solution 1 for FractionalIdeal.finprod_unitOfPrime_zpow_count
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:15:31.934754+00:00
-- url     : https://prove2.me/submissions/c90b6845-c702-4fa0-970d-af8d52d532b0

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Factorization
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Complements on Dedekind-domain factorization

Facts about `Associates.count` and `FractionalIdeal.count` that Mathlib does not carry, together
with unit-level factorization of invertible fractional ideals.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.le_count_associates_iff_le_pow`: the multiplicity of `v` in
  a nonzero `J` is at least `k` exactly when `v ^ k` contains `J`. The multiplicity here is
  `Associates.count`, not `FractionalIdeal.count` — hence the `associates` token, matching
  Mathlib's `Ideal.count_associates_factors_eq` for the same expression. Mathlib reads that
  multiplicity as divisibility of `Associates`; a consumer comparing two multiplicities across a
  ring extension wants a containment of *ideals*, and shows the two ideals contain the same prime
  powers.
* `FractionalIdeal.count_div`: the multiplicity of `I / J` is the difference of the multiplicities
  of `I` and `J`. Mathlib's `count` API has `count_mul`, `count_inv`, `count_pow` and `count_zpow`
  but no division form, so every consumer that clears a denominator repeats the same rewrites.
* `FractionalIdeal.count_spanSingleton_div`: the same on principal fractional ideals. This is the
  one the `S`-integer class-group computation in
  `TauCeti/RingTheory/DedekindDomain/SInteger/ClassGroup.lean` uses, at both `R` and `𝒪_S` — which
  is why the ring is a variable rather than fixed — advancing
  `TauCetiRoadmap/EllipticCurves/README.md` §Layer 6 (Mordell–Weil), whose weak-Mordell–Weil
  argument needs the `S`-class group to be finite. It is also the step that carries
  `count_toPrincipalIdeal_eq_neg_log_valuation` below. `count_div` is its general form and has no
  consumer in this repository yet.
* `FractionalIdeal.count_toPrincipalIdeal_eq_neg_log_valuation`: the multiplicity at `v` of the
  principal fractional ideal of a nonzero rational function `u : Kˣ` is
  `-WithZero.log (v.valuation K u)`. This is the passage between the two ways this library measures
  a principal ideal at a height one prime — Mathlib's `count` and the adic valuation.
* `Ideal.hasFiniteMulSupport_asIdeal_pow_of_le_count`: a family of prime powers whose exponents
  are bounded by the multiplicities of a fixed nonzero ideal has finite multiplicative support.
  Mathlib's `Ideal.hasFiniteMulSupport` is the case of the multiplicities themselves; a consumer
  defining an ideal as `∏ᵥ 𝔭ᵥ ^ e v` for exponents it only knows to be dominated by an actual
  factorisation — as the minimal discriminant ideal of an elliptic curve is dominated by the
  discriminant of any integral model — needs the bounded form to see that the product is finite.
* `IsDedekindDomain.HeightOneSpectrum.unitOfPrime`: a height-one prime regarded as an invertible
  fractional ideal.
* `FractionalIdeal.hasFiniteMulSupport_zpow_count`: a family of powers indexed by the height one
  primes, with the multiplicities of a fixed fractional ideal as exponents, has finite
  multiplicative support. The bases are an arbitrary family in an arbitrary `DivInvMonoid`, since
  nothing but the vanishing of almost all exponents is at stake; the unit-level factorization below
  is the case of the primes themselves.
* `FractionalIdeal.finprod_unitOfPrime_zpow_count`: unique factorization of an invertible
  fractional ideal, transported along `Units.coeHom`.

All these declarations are general facts about an arbitrary Dedekind domain, mentioning no
particular ring extension.

`le_count_associates_iff_le_pow` is adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/Basic.lean:381` at the
roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll); following this repository's convention
for adapted material, the upstream authorship is credited here rather than in the copyright header.
**`count_div` and `count_spanSingleton_div` are new here** — they have no counterpart in that
source. `count_toPrincipalIdeal_eq_neg_log_valuation` is this repository's own, relocated here
from `TauCeti/AlgebraicGeometry/WeilDivisor/Dedekind/Basic.lean`: nothing in its statement or
proof mentions a Weil divisor, and stating it under `TauCeti.AlgebraicGeometry` put it out of
reach of the `RingTheory` consumers that need it, which is exactly the boundary
`TauCeti/RingTheory/ClassGroup/HeightOneSpectrum.lean` records in its module docstring.

The unit-level prime factorization `FractionalIdeal.finprod_unitOfPrime_zpow_count` is adapted
from Michael Stoll's `EllipticCurves/Mathlib/FractionalIdeal.lean` at commit `66889eada51a` of the
`MichaelStollBayreuth/EllipticCurves` repository (Apache 2.0).
-/
 section

namespace IsDedekindDomain.HeightOneSpectrum
end IsDedekindDomain.HeightOneSpectrum
section IsDedekindDomain.HeightOneSpectrum
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R]



/-- The fractional ideal underlying `v.unitOfPrime K` is `v.asIdeal`. -/
@[simp]
theorem IsDedekindDomain.HeightOneSpectrum.coe_unitOfPrime (v : _root_.IsDedekindDomain.HeightOneSpectrum R) (K : Type*) [_root_.Field K] [_root_.Algebra R K]
  [_root_.IsFractionRing R K] :
    (v.unitOfPrime K : _root_.FractionalIdeal R⁰ K) = v.asIdeal := by
  rw [_root_.IsDedekindDomain.HeightOneSpectrum.unitOfPrime]
  exact _root_.Units.val_mk0 _



end IsDedekindDomain.HeightOneSpectrum

namespace Ideal
end Ideal
section Ideal
open Ideal

-- `Ideal.IsDedekindDomain` also exists, so the root namespace has to be named explicitly.
open _root_.IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]



end Ideal

namespace FractionalIdeal
end FractionalIdeal
section FractionalIdeal
open FractionalIdeal

open IsDedekindDomain

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]



/-- Only finitely many factors in the unit-level prime factorization are nontrivial. -/
lemma FractionalIdeal.hasFiniteMulSupport_unitOfPrime_zpow (I : (_root_.FractionalIdeal R⁰ K)ˣ) :
    (_root_.Function.mulSupport fun v : _root_.IsDedekindDomain.HeightOneSpectrum R ↦
      v.unitOfPrime K ^ _root_.FractionalIdeal.count K v (I : _root_.FractionalIdeal R⁰ K)).Finite :=
  _root_.FractionalIdeal.hasFiniteMulSupport_zpow_count (I : _root_.FractionalIdeal R⁰ K) (fun v ↦ v.unitOfPrime K)

/-- Unique factorization of an invertible fractional ideal as a product of prime powers. -/
theorem solution (I : (_root_.FractionalIdeal R⁰ K)ˣ) :
    I = ∏ᶠ v : _root_.IsDedekindDomain.HeightOneSpectrum R,
      v.unitOfPrime K ^ _root_.FractionalIdeal.count K v (I : _root_.FractionalIdeal R⁰ K) := by
  -- State the map equation separately: rewriting would also affect the coercion inside `count`.
  have hmap : ((∏ᶠ v : _root_.IsDedekindDomain.HeightOneSpectrum R,
        v.unitOfPrime K ^ _root_.FractionalIdeal.count K v (I : _root_.FractionalIdeal R⁰ K)) :
        (_root_.FractionalIdeal R⁰ K)ˣ) =
      ∏ᶠ v : _root_.IsDedekindDomain.HeightOneSpectrum R,
        ((v.unitOfPrime K ^ _root_.FractionalIdeal.count K v (I : _root_.FractionalIdeal R⁰ K) :
          (_root_.FractionalIdeal R⁰ K)ˣ) : _root_.FractionalIdeal R⁰ K) :=
    _root_.MonoidHom.map_finprod (_root_.Units.coeHom (_root_.FractionalIdeal R⁰ K))
      (_root_.FractionalIdeal.hasFiniteMulSupport_unitOfPrime_zpow I)
  refine _root_.Units.ext ?_
  rw [hmap]
  simp only [_root_.Units.val_zpow_eq_zpow_val, _root_.IsDedekindDomain.HeightOneSpectrum.coe_unitOfPrime]
  exact (_root_.FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K)
    (I := (I : _root_.FractionalIdeal R⁰ K)) (_root_.Units.ne_zero I)).symm





section PrincipalIdeal

variable {A : Type*} [CommRing A] [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
  [IsFractionRing A K]





end PrincipalIdeal

end FractionalIdeal

end

end
