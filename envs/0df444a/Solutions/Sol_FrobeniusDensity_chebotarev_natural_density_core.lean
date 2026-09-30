-- Prove2me | solution 1 for FrobeniusDensity.chebotarev_natural_density_core
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T22:21:19.538456+00:00
-- url     : https://prove2.me/submissions/9639cf49-be9f-4cb2-90c0-d8621019258a

/- Chebotarev proof reused from the Tau Ceti contributors (Apache-2.0).
   Source: https://github.com/TauCetiProject/TauCeti/tree/948fe4751b1fe528b6d580c522ca5d743d47f185
   The rational-prime interface, cutoff transport, and finite-exclusion
   argument adapt that proof to the Prove2Me target. -/
import Definitions.Def_LanglandsTunnell_TowerCounting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_FrobeniusPrimeSet
import Definitions.Def_TauCeti_NumberTheory_NumberField_ArtinSymbol
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Definitions.Def_TauCeti_Order_Northcott_Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real
import Theorems.Thm_NumberField_Chebotarev_hasNaturalDensity_frobeniusPrimeSet

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The absolute ideal norm under a ring isomorphism, and congruences of norms

Identifying two rings along an isomorphism identifies their ideals, and the absolute norm is
insensitive to that identification.

In a ring that is free of finite rank over `ℤ`, elements congruent modulo `(m)` have norms
congruent modulo `m`; for principal ideals whose generators have norms with nonnegative product,
the congruence passes to the absolute norms.

## Main results

* `Ideal.absNorm_comap_of_ringEquiv`, `Ideal.absNorm_map_of_ringEquiv`: the absolute norm of an
  ideal is unchanged by transporting it along a ring isomorphism, in either direction.
* `Algebra.intCast_norm_eq_of_sub_mem_span_natCast`: elements congruent modulo `(m)` have norms
  congruent modulo `m`.
* `Ideal.span_singleton_natCast_eq_top_iff`: the ideal `(m)` is the unit ideal only for `m = 1`.
* `Ideal.natCast_absNorm_span_singleton_eq_of_sub_mem`: congruent elements whose norms have
  nonnegative product generate ideals with absolute norms congruent modulo `m`.
-/

 section

namespace Ideal

variable {R R' : Type*} [CommRing R] [CommRing R'] [IsDedekindDomain R] [IsDedekindDomain R']
  [Module.Free ℤ R] [Module.Free ℤ R']

/-- The absolute norm is invariant under transporting an ideal backwards along an isomorphism of
Dedekind domains.  Use this to move a norm computation to whichever of two identified rings it is
easier to carry out in. -/
@[simp]
theorem absNorm_comap_of_ringEquiv [Infinite R] [Infinite R'] (e : R ≃+* R') (I : Ideal R') :
    absNorm (Ideal.comap e I) = absNorm I := by
  rw [absNorm_apply, absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv _ _ e (Ideal.map_comap_eq_self_of_equiv e I).symm)

/-- The absolute norm is invariant under transporting an ideal forwards along an isomorphism of
Dedekind domains.  This is the form to use when the ideal is given on the source side. -/
@[simp]
theorem absNorm_map_of_ringEquiv [Infinite R] [Infinite R'] (e : R ≃+* R') (I : Ideal R) :
    absNorm (I.map e) = absNorm I := by
  rw [← Ideal.comap_symm]
  exact absNorm_comap_of_ringEquiv e.symm I

end Ideal

section Congruence

variable {S : Type*} [CommRing S] [Module.Free ℤ S] [Module.Finite ℤ S]







end Congruence


end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Finite real-cutoff carriers for Northcott functions

This file packages the finite carrier selected by a real cutoff for a natural-valued Northcott
function, together with generic summatory functions over that carrier. The carrier depends only
on the integer part of the cutoff, and for a nonnegative cutoff it agrees with the one selected by
its natural floor.
-/

 section

namespace TauCeti

open Filter
open scoped Topology

variable {ι : Type*} (N : ι → ℕ) [Northcott N]





/-- An index belongs to `normLE N x` exactly when its `N`-value is at most the inclusive
real cutoff `x`. -/
@[simp, grind =]
theorem mem_normLE {i : ι} {x : ℝ} : i ∈ normLE N x ↔ (N i : ℝ) ≤ x := by
  simp [normLE]

















/-! ### Generic summatory functions -/



/-- Evaluating `summatory N w` at `x` gives the finite sum of `w` over `normLE N x`. -/
theorem summatory_apply {M : Type*} [AddCommMonoid M] (w : ι → M) (x : ℝ) :
    summatory N w x = ∑ i ∈ normLE N x, w i := by
  rw [summatory]





























end TauCeti

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Counting carriers for ideals and prime ideals

Every estimate in the arithmetic-Dirichlet-series roadmap counts objects whose absolute norm does
not exceed a *real* cutoff `x`, and always inclusively: an object of norm exactly `x` is counted.
This file fixes that convention once.

The common core is Mathlib's `Northcott` property: a function `N : ι → ℕ` is Northcott when each
set `{i | N i ≤ B}` is finite.  For such an `N`:

* `TauCeti.normLE N x` is the finite set of indices with `(N i : ℝ) ≤ x`;
* `TauCeti.summatory N w x` is the inclusive sum of a weight `w` over `TauCeti.normLE N x`.

Two instances of this core carry the arithmetic content, `TauCeti.idealsLE` for the nonzero
integral ideals of `𝓞 K` and `TauCeti.primesLE` for the height-one primes, with
`TauCeti.idealSummatory`, `TauCeti.primeSummatory`, and `TauCeti.primePowerSummatory` the associated
summatory functions.  The
weighted prime counts of the roadmap are the two named specializations
`TauCeti.primeTheta`, the logarithmically weighted count, and `TauCeti.primeCount`, the
unweighted one; both are restricted to a set `S` of height-one primes through `Set.indicator`,
so no decidability hypothesis is needed on `S`.

A prime-power ideal is `𝔭 ^ k` for a unique height-one prime `𝔭` and a unique `k ≥ 1`;
`TauCeti.primePowerBase` and `TauCeti.primePowerExponent` name that pair, and
`TauCeti.idealPrimePower_eq_of_base_eq_of_exponent_eq` records that it determines the ideal.  The
exponent is `1` exactly on the primes themselves, which is `TauCeti.primePowerExponent_eq_one_iff`;
`TauCeti.IdealPrimePower.ofPrime` is the resulting inclusion of the prime carrier into the
prime-power carrier, and `TauCeti.primePowerSummatory_eq_primeSummatory` uses it to read a
prime-power sum concentrated on the exponent-one part as a sum over primes.

`TauCeti.idealsLE_filter_dvd` identifies the ideals below a cutoff divisible by a fixed nonzero
ideal `P` with the multiples of `P`, and `TauCeti.idealSummatory_ite_dvd` reads the corresponding
part of a summatory function at the rescaled cutoff `x / N(P)`.

Two lemmas move a summatory function between the three carriers.
`TauCeti.idealSummatory_eq_primePowerSummatory` reads an ideal weight vanishing off the prime
powers as a prime-power weight, and `TauCeti.idealSummatory_eq_sum_range_normFiber` regroups an
ideal summatory function into the partial sum, over `n ≤ ⌊x⌋₊`, of the total mass on the norm
fibre at `n`; `TauCeti.idealSummatory_eq_sum_Icc_normCoeff` writes the same regrouping as a
partial sum of `TauCeti.normCoeff`.  Together they present a sum over prime powers as a partial
sum of an `ArithmeticFunction`, which is the shape a Tauberian theorem consumes.

For `0 ≤ x`, a real cutoff and its floor select the same indices, so
`TauCeti.normLE_eq_normLE_natFloor` and `TauCeti.summatory_eq_summatory_natFloor` convert between
the real and natural conventions. The small-cutoff cases are degenerate for a reason worth
recording: a nonzero ideal has absolute norm at least `1`, and a height-one prime at least `2`, so
`TauCeti.idealsLE_one` isolates the unit ideal and `TauCeti.primesLE_eq_empty_of_lt_two` empties the
prime carrier below `2`.

Modifying a weight on a finite set, or a prime set on a finite symmetric difference, changes a
summatory function by a quantity that is eventually the *constant* total discrepancy; this is
`TauCeti.eventually_summatory_sub_eq` and its two prime specializations. Layer 7 uses these to
show that finite changes do not affect a density. In the same spirit,
`TauCeti.primeTheta_isLittleO_of_finite` records that a finite set of primes contributes an
eventually constant amount to `ϑ_K`, hence `o(x)`: an exceptional set can be discarded from a
counting argument outright, not merely from a density. Its `ψ` companion is
`TauCeti.primePsi_isLittleO_of_finite`.

## Roadmap role

This is Layer **4** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`: the finite cutoff
carriers of 4.1, the generic summatory functions on ideals, primes, and prime powers of 4.2, and the
weighted prime counts `primeTheta` and `primeCount` of 4.3. Layer 5 supplies the actual size
estimates for these counts, and consumes the prime base and exponent of a prime-power ideal to
fibre those estimates over the primes.

## References

* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters I--II.
* H. Davenport, *Multiplicative Number Theory*, Chapters 1 and 7.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

 section

namespace TauCeti

open Filter
open scoped nonZeroDivisors NumberField
open IsDedekindDomain

/-! ### Ideals and height-one primes of bounded absolute norm -/



variable (K : Type*) [Field K] [NumberField K]













variable {K}







/-! ### The prime base and the exponent of a prime-power ideal -/



























































variable (K)

/-! ### Summatory functions over ideals and over primes -/











/-- A prime summatory function is the sum of its weight over the inclusive cutoff carrier. -/
theorem primeSummatory_apply {M : Type*} [AddCommMonoid M]
    (w : HeightOneSpectrum (𝓞 K) → M) (x : ℝ) :
    primeSummatory K w x = ∑ v ∈ primesLE K x, w v :=
  summatory_apply _ w x





















variable {K}

namespace MultiplicativeIdealWeight

variable (χ : MultiplicativeIdealWeight K)



end MultiplicativeIdealWeight

variable (K)









/-! ### The weighted prime counts -/





variable {K}
variable {S T : Set (HeightOneSpectrum (𝓞 K))} {x : ℝ}



/-- The unweighted prime count as an explicit sum over the inclusive carrier. -/
theorem primeCount_apply (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primeCount K S x = ∑ v ∈ primesLE K x, S.indicator 1 v := by
  rw [primeCount, primeSummatory_apply]

/-- The count of `S` really is the cardinality of the set of primes of `S` below the cutoff. -/
theorem primeCount_eq_card (S : Set (HeightOneSpectrum (𝓞 K))) [DecidablePred (· ∈ S)] (x : ℝ) :
    primeCount K S x = ((primesLE K x).filter (· ∈ S)).card := by
  rw [primeCount_apply]
  simp [Set.indicator_apply, Finset.sum_boole]



















































end TauCeti

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Unramifiedness at a prime transports along an isomorphism of algebras

`Algebra.IsUnramifiedAt R q` says that the localization of the ambient algebra at `q` is formally
unramified over `R`. An isomorphism `ψ : A ≃ₐ[R] B` of `R`-algebras matches the prime complement
of `q` with that of `q.comap ψ`, so it induces an isomorphism of the two localizations over `R`
and carries unramifiedness from `q` to `q.comap ψ`.

## Main results

* `AlgEquiv.isUnramifiedAt_of_eq_comap`: if `B` is unramified at `q` over `R`, then `A` is
  unramified at any prime equal to `q.comap ψ`.
-/

 section

namespace AlgEquiv

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- **Unramifiedness transports along an isomorphism of `R`-algebras.** If `B` is unramified over
`R` at a prime `q`, then `A` is unramified over `R` at the corresponding prime `q.comap ψ`, stated
for any prime `p` of `A` equal to it. -/
theorem isUnramifiedAt_of_eq_comap (ψ : A ≃ₐ[R] B) {q : Ideal B} [q.IsPrime]
    {p : Ideal A} [p.IsPrime] (hp : p = q.comap ψ) [Algebra.IsUnramifiedAt R q] :
    Algebra.IsUnramifiedAt R p := by
  -- The transported prime is the parameter `p` with the equation `hp`, not the term `q.comap ψ`
  -- itself: `Algebra.IsUnramifiedAt` takes the primality of its ideal as an instance argument, so
  -- `rw` cannot turn a conclusion about `q.comap ψ` into one about `p`, while `subst` can.
  subst hp
  exact Algebra.FormallyUnramified.of_equiv (IsLocalization.algEquivOfAlgEquiv
    (Localization.AtPrime (q.comap ψ)) (Localization.AtPrime q) ψ
      (Ideal.map_primeCompl_comap_of_surjective ψ ψ.surjective q)).symm

end AlgEquiv

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Ramification and inertia counting criteria

This file records Galois consequences of the fundamental identity for primes in finite
extensions of domains. First, in a Galois extension the number of primes above a prime ideal is
maximal exactly when the common ramification index and inertia degree are both `1`. Second, the
cardinality of the inertia subgroup of a prime `P` upstairs is the ramification index of `P`
itself over the base, rather than the `Ideal.ramificationIdxIn` of the prime below it.

The rest of the file is about how inertia subgroups vary with the prime. Translating a prime by
`σ` conjugates its inertia subgroup by `σ`, since `τ • x - x ∈ σ • P` says exactly
`(σ⁻¹ τ σ) • y - y ∈ P` after the substitution `x = σ • y`. Because the Galois group acts
transitively on the primes above a fixed prime of the base, a *commutative* Galois group therefore
has one inertia subgroup per prime of the base, not one per prime upstairs. That uniformity is
what lets a statement about ramification in an intermediate field be tested at a single prime
upstairs.

## Main results

* `TauCeti.RamificationInertia.ncard_primesOver_eq_natCard_iff_of_isGaloisGroup`:
  the domain/flat Galois counting criterion.
* `Ideal.card_inertia_eq_ramificationIdx`: the un-`In` form of the inertia count.
* `Ideal.mem_inertia_pointwise_smul_iff`: translation conjugates inertia subgroups.
* `Ideal.inertia_pointwise_smul`: for a commutative Galois group, translation leaves the inertia
  subgroup unchanged.
* `Ideal.inertia_eq_of_liesOver`: for a commutative Galois group, all the primes above a fixed
  prime of the base have the same inertia subgroup.
* `Ideal.isUnramifiedAt_pointwise_smul_iff`: unramifiedness is invariant under translation by
  an algebra automorphism.
* `Ideal.isUnramifiedAt_of_isUnramifiedAt_of_isGaloisGroup`: unramifiedness transfers between
  primes above the same base prime in a Galois extension.

## Provenance

Built directly on Mathlib's unramifiedness transport
(`AlgEquiv.isUnramifiedAt_of_eq_comap`), on its Galois fundamental identity
(`Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`), on its inertia count
(`Ideal.card_inertia_eq_ramificationIdxIn`), and on its transitivity statement
(`Ideal.exists_smul_eq_of_isGaloisGroup`).
-/

 section

open Ideal Module

namespace Ideal

open scoped Pointwise

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]

/-- **Unramifiedness is invariant under algebra automorphisms.** Translating a prime by an
`R`-algebra action automorphism preserves unramifiedness over `R`. -/
@[simp]
theorem isUnramifiedAt_pointwise_smul_iff (Q : Ideal S) [Q.IsPrime] (g : G) :
    Algebra.IsUnramifiedAt R (g • Q) ↔ Algebra.IsUnramifiedAt R Q := by
  constructor
  · intro h
    let _ : Algebra.IsUnramifiedAt R (g • Q) := h
    apply (MulSemiringAction.toAlgEquiv R S g).isUnramifiedAt_of_eq_comap (q := g • Q)
    rw [Ideal.pointwise_smul_eq_comap]
    exact (Ideal.comap_of_equiv (MulSemiringAction.toRingEquiv G S g)).symm
  · intro h
    let _ : Algebra.IsUnramifiedAt R Q := h
    apply (MulSemiringAction.toAlgEquiv R S g).symm.isUnramifiedAt_of_eq_comap (q := Q)
    exact Ideal.pointwise_smul_eq_comap Q

/-- Unramifiedness at one prime above `p` implies unramifiedness at every prime above `p`
when the Galois group acts transitively on them. -/
theorem isUnramifiedAt_of_isUnramifiedAt_of_isGaloisGroup
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (p : Ideal A) (P Q : Ideal B) [P.IsPrime] [P.LiesOver p]
    [Q.IsPrime] [Q.LiesOver p] (G : Type*) [Group G] [Finite G]
    [MulSemiringAction G B] [IsGaloisGroup G A B]
    [Algebra.IsUnramifiedAt A P] : Algebra.IsUnramifiedAt A Q := by
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup p P Q G
  exact (isUnramifiedAt_pointwise_smul_iff P σ).mpr inferInstance

end Ideal

namespace Ideal

/-- The cardinality of the inertia subgroup of `P` is the ramification index of `P` over `R`.
This is `Ideal.card_inertia_eq_ramificationIdxIn` stated with the ramification index of `P`
itself rather than with `Ideal.ramificationIdxIn` of the ideal below it. -/
theorem card_inertia_eq_ramificationIdx (R : Type*) {S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsDomain R] [IsDomain S] [Module.Finite R S] [Module.Flat R S] (G : Type*)
    [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S] (P : Ideal S) [P.IsPrime]
    [PerfectField (P.under R).ResidueField] :
    Nat.card (P.inertia G) = P.ramificationIdx R :=
  (card_inertia_eq_ramificationIdxIn (G := G) (P.under R) P).trans
    (ramificationIdxIn_eq_ramificationIdx (P.under R) P G)

end Ideal

namespace TauCeti.RamificationInertia



end TauCeti.RamificationInertia

namespace Ideal

section Inertia

open scoped Pointwise

variable {S : Type*} [CommRing S] {G : Type*} [Group G] [MulSemiringAction G S]



variable (σ : G) (P : Ideal S)



end Inertia

section InertiaOver

open scoped Pointwise

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : Ideal A) (P Q : Ideal B)
  [P.IsPrime] [P.LiesOver p] [Q.IsPrime] [Q.LiesOver p] (G : Type*) [Group G] [Finite G]
  [IsMulCommutative G] [MulSemiringAction G B] [IsGaloisGroup G A B]



end InertiaOver

end Ideal

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The Frobenius, the inertia subgroup, and the decomposition group

Let `L / K` be a finite Galois extension of number fields with Galois group `G = Gal(L/K)`, and
let `Q` be a nonzero prime of `𝓞 L` lying over `𝔭 = Q ∩ 𝓞 K`. Mathlib's `IsArithFrobAt`
expresses that an element `σ ∈ G` satisfies `σ x ≡ x ^ #(𝓞 K ⧸ 𝔭) (mod Q)`. Tau Ceti's
`NumberField.exists_isArithFrobAt` supplies such an element, and
`NumberField.isArithFrobAt_eq_of_isUnramifiedAt` proves it unique when `L / K` is unramified at
`Q`. This file identifies what that element is. In general, a Frobenius at `Q` together with the
inertia subgroup of `Q` generates the decomposition group of `Q`; at an unramified prime the
inertia subgroup is trivial, and the Frobenius alone generates the decomposition group, mapping
to the Frobenius automorphism of the residue extension.

The link is Mathlib's `Ideal.Quotient.stabilizerHom`, the action of the decomposition group
`MulAction.stabilizer G Q` on the residue extension `(𝓞 L ⧸ Q) / (𝓞 K ⧸ 𝔭)`. Its kernel is the
inertia subgroup, which is trivial exactly when `Q` is unramified, because the cardinality of the
inertia subgroup is the ramification index (`Ideal.card_inertia_eq_ramificationIdx`). So at an
unramified prime the decomposition group embeds in the residue Galois group, and a Frobenius
element is precisely a preimage of the residue Frobenius `x ↦ x ^ #(𝓞 K ⧸ 𝔭)`. Counting through
that embedding turns the classical facts about finite fields into facts about `G`:

* the order of a Frobenius element is the inertia degree `f(Q/𝔭)`;
* the decomposition group has cardinality `f(Q/𝔭)` as well, so the embedding is an isomorphism;
* consequently the decomposition group is `⟨σ⟩`, and it is cyclic.

The last section transports these statements along the action of `G` on the primes above `𝔭`.
Unramifiedness is invariant under that action, and the Frobenius at `τ • Q` is the conjugate
`τ σ τ⁻¹`: Mathlib's `IsArithFrobAt.conj` gives one inclusion and uniqueness at the unramified
prime `τ • Q` gives the other.

## Main results

* `Ideal.isUnramifiedAt_iff_inertia_eq_bot`: unramifiedness at `Q` is triviality of the
  inertia subgroup of `Q` in `Gal(L/K)`.
* `Ideal.stabilizerHom_eq_frobeniusAlgEquivOfAlgebraic`: a Frobenius element at `Q` acts on
  the residue field `𝓞 L ⧸ Q` as the residue Frobenius.
* `Ideal.orderOf_eq_inertiaDeg_of_isArithFrobAt`: a Frobenius element at an unramified `Q`
  has order the inertia degree of `Q` over `𝓞 K`.
* `Ideal.zpowers_eq_stabilizer_of_isArithFrobAt`: a Frobenius element at an unramified `Q`
  generates the decomposition group of `Q`.
* `Ideal.card_stabilizer_eq_inertiaDeg_of_isUnramifiedAt`: the decomposition group of an
  unramified `Q` has order the inertia degree of `Q` over `𝓞 K`.
* `Ideal.stabilizerEquivResidueAut`: the decomposition group of an unramified prime is
  isomorphic to the automorphism group of the residue extension.
* `Ideal.isCyclic_stabilizer_of_isUnramifiedAt`: the decomposition group of an unramified
  prime is cyclic.
* `Ideal.zpowers_sup_inertia_eq_stabilizer_of_isArithFrobAt`: at any nonzero prime `Q`, a
  Frobenius element together with the inertia subgroup generates the decomposition group.
* `Ideal.orbit_stabilizer_eq_orbit_zpowers_of_isArithFrobAt`: on a set where the inertia
  subgroup acts trivially, the orbits of the decomposition group are those of any Frobenius.
* `Ideal.isArithFrobAt_pointwise_smul_iff_eq_conj`: the Frobenius elements at `τ • Q` are
  exactly the conjugates `τ σ τ⁻¹` of the Frobenius elements `σ` at an unramified `Q`.

## Implementation notes

`FiniteField.frobeniusAlgEquivOfAlgebraic` is stated for a `Fintype` base field, so the residue
identification supplies that instance internally through `Fintype.ofFinite`. Residue rings are
made into fields by the local instance `Ideal.Quotient.field`, following Mathlib's own
ramification files.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9.
-/

 section

open Ideal Module

open scoped NumberField Pointwise

namespace Ideal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-! ### Unramifiedness and the inertia subgroup -/

/-- **Unramified means trivial inertia.** For a finite Galois extension `L / K` of number fields,
`L / K` is unramified at a prime `Q` of `𝓞 L` exactly when the inertia subgroup of `Q` in
`Gal(L/K)` is trivial.

This is the group-theoretic reading of `Ideal.card_inertia_eq_ramificationIdx`: the inertia
subgroup has as many elements as the ramification index of `Q` over `𝓞 K`. -/
theorem isUnramifiedAt_iff_inertia_eq_bot (Q : Ideal (𝓞 L)) [Q.IsPrime] :
    Algebra.IsUnramifiedAt (𝓞 K) Q ↔ Q.inertia (L ≃ₐ[K] L) = ⊥ := by
  rw [← Ideal.ramificationIdx_eq_one_iff (R := 𝓞 K) (q := Q),
    ← Ideal.card_inertia_eq_ramificationIdx (𝓞 K) (L ≃ₐ[K] L) Q]
  exact ⟨Subgroup.eq_bot_of_card_eq _, fun h ↦ by rw [h]; simp⟩

/-! ### The decomposition group at an unramified prime -/









attribute [local instance] Ideal.Quotient.field











/-! ### The decomposition group at a possibly ramified prime -/







/-! ### Conjugation along the fibre -/



end Ideal

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Local invariants over `ℤ` and over `𝓞 ℚ`

The ring of integers of `ℚ` is `ℤ` (`Rat.ringOfIntegersEquiv`), but the two are different
types, and the local invariants of a prime `P` of a number field `E` can be taken relative to
either base ring: the residue degree `P.inertiaDeg ℤ` or `P.inertiaDeg (𝓞 ℚ)`, the ramification
index `P.ramificationIdx ℤ` or `P.ramificationIdx (𝓞 ℚ)`, and the arithmetic Frobenius condition
`IsArithFrobAt ℤ σ P` or `IsArithFrobAt (𝓞 ℚ) σ P`. Statements about number fields over `ℚ` as
a base *field* naturally produce the `𝓞 ℚ` versions, while statements about rational primes
produce the `ℤ` versions. This file proves that they agree.

The residue degrees are compared through the absolute norm, `absNorm (P.under R) ^ f = absNorm P`
for both base rings, since the ideal of `𝓞 ℚ` below `P` is the image of the ideal of `ℤ` below
`P` under the structure map. The ramification indices are compared as multiplicities of `P` in
the extension of the prime below, and the Frobenius conditions only involve the size of the
residue field below `P`. The comparison lemmas are `simp` lemmas oriented towards the `ℤ` forms.

## Main results

* `Ideal.under_ringOfIntegers_rat_eq_map`: the ideal of `𝓞 ℚ` below `P` is the image of the ideal
  of `ℤ` below `P`.
* `Ideal.inertiaDeg_ringOfIntegers_rat_eq_int`: the residue degrees over `𝓞 ℚ` and over `ℤ`
  agree.
* `Ideal.ramificationIdx_ringOfIntegers_rat_eq_int`: the ramification indices over `𝓞 ℚ` and over
  `ℤ` agree.
* `Ideal.isArithFrobAt_ringOfIntegers_rat_iff`: the Frobenius conditions over `𝓞 ℚ` and over `ℤ`
  agree.
* `Ideal.inertiaDeg_eq_orderOf` and
  `Ideal.ncard_primesOver_mul_inertiaDeg_eq_finrank_of_isUnramifiedAt`:
  the unramified Frobenius order and prime-count formulas over `ℤ`.
* `Ideal.primesOver_under_ringOfIntegers_rat_eq`: for a prime `Q` above the rational prime `p`,
  the primes of a subfield above `Q ∩ 𝓞 ℚ` are the primes above `p`.
* `Rat.HeightOneSpectrum.absNorm_asIdeal`: the absolute norm of a height-one prime of `𝓞 ℚ` is
  the rational prime it corresponds to, and `Rat.HeightOneSpectrum.exists_absNorm_eq` shows
  every rational prime arises this way.
-/

 section

open scoped NumberField

namespace Ideal

variable {E : Type*} [Field E] [NumberField E]

/-- The structure map `ℤ → 𝓞 ℚ` is the inverse of `Rat.ringOfIntegersEquiv`. -/
theorem _root_.Rat.algebraMap_int_ringOfIntegers_eq :
    algebraMap ℤ (𝓞 ℚ) = (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) :=
  (RingHom.eq_intCast' _).trans (RingHom.eq_intCast' _).symm

/-- The ideal of `𝓞 ℚ` below an ideal `P` of `𝓞 E` is the image of the ideal of `ℤ` below `P`. -/
-- Not a `simp` lemma: it would rewrite the left-hand sides of `absNorm_under_ringOfIntegers_rat`
-- and `card_quot_under_ringOfIntegers_rat` out of simp normal form (`simpNF`).
theorem under_ringOfIntegers_rat_eq_map (P : Ideal (𝓞 E)) :
    P.under (𝓞 ℚ) = (P.under ℤ).map (algebraMap ℤ (𝓞 ℚ)) := by
  have : IsScalarTower ℤ (𝓞 ℚ) (𝓞 E) :=
    IsScalarTower.of_algebraMap_eq' ((RingHom.eq_intCast' _).trans (RingHom.eq_intCast' _).symm)
  rw [← under_under (A := ℤ) (B := 𝓞 ℚ) P]
  exact (map_comap_of_surjective _
    (Rat.algebraMap_int_ringOfIntegers_eq ▸ Rat.ringOfIntegersEquiv.symm.surjective) _).symm

/-- The absolute norm of the ideal of `𝓞 ℚ` below `P` is that of the ideal of `ℤ` below `P`. -/
@[simp]
theorem absNorm_under_ringOfIntegers_rat (P : Ideal (𝓞 E)) :
    absNorm (P.under (𝓞 ℚ)) = absNorm (P.under ℤ) := by
  rw [under_ringOfIntegers_rat_eq_map, Rat.algebraMap_int_ringOfIntegers_eq]
  exact absNorm_map_of_ringEquiv Rat.ringOfIntegersEquiv.symm _

/-- The residue rings of `𝓞 ℚ` and of `ℤ` below `P` have the same number of elements. -/
@[simp]
theorem card_quot_under_ringOfIntegers_rat (P : Ideal (𝓞 E)) :
    Nat.card (𝓞 ℚ ⧸ P.under (𝓞 ℚ)) = Nat.card (ℤ ⧸ P.under ℤ) := by
  rw [← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply, ← absNorm_apply, ← absNorm_apply,
    absNorm_under_ringOfIntegers_rat]

/-- **Frobenius elements over `𝓞 ℚ` and over `ℤ` are the same.** An element `σ` is an arithmetic
Frobenius at `Q` relative to the base ring `𝓞 ℚ` exactly when it is one relative to `ℤ`: the
defining congruence only involves the size of the residue field below `Q`, which is the same
for both base rings. -/
@[simp]
theorem isArithFrobAt_ringOfIntegers_rat_iff {G : Type*} [Group G] [MulSemiringAction G (𝓞 E)]
    [SMulCommClass G ℤ (𝓞 E)] [SMulCommClass G (𝓞 ℚ) (𝓞 E)] (σ : G) (Q : Ideal (𝓞 E)) :
    IsArithFrobAt (𝓞 ℚ) σ Q ↔ IsArithFrobAt ℤ σ Q := by
  simp only [IsArithFrobAt, AlgHom.IsArithFrobAt, MulSemiringAction.toAlgHom_apply,
    card_quot_under_ringOfIntegers_rat]







end Ideal

namespace Rat.HeightOneSpectrum

open IsDedekindDomain

/-- The absolute norm of a height-one prime of `𝓞 ℚ` is the rational prime generating its image
in `ℤ`. -/
@[simp]
theorem absNorm_asIdeal (v : HeightOneSpectrum (𝓞 ℚ)) :
    Ideal.absNorm v.asIdeal = natGenerator v := by
  rw [← Ideal.absNorm_map_of_ringEquiv (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)),
    ← span_natGenerator, Ideal.absNorm_span_singleton]
  simp





end Rat.HeightOneSpectrum

namespace Ideal

open Module MulAction
open scoped NumberField Pointwise

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]





end Ideal

end
end

section
set_option autoImplicit false
noncomputable section

open Filter Topology

namespace FrobeniusDensity

/-- The number of primes in `range X` tends to infinity. -/
theorem tendsto_card_filter_prime_range :
    Tendsto (fun X : ℕ ↦ (((Finset.range X).filter Nat.Prime).card : ℝ)) atTop atTop := by
  simpa only [Function.comp_def, Nat.primeCounting', Nat.count_eq_card_filter_range] using
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp Nat.tendsto_primeCounting'

/-- Once a finite exceptional set is contained in the range, deleting it subtracts a constant. -/
theorem filter_range_card_not_mem_finset (P : ℕ → Prop) [DecidablePred P]
    (S : Finset ℕ) {X : ℕ} (hX : S ⊆ Finset.range X) :
    (((Finset.range X).filter fun n ↦ n ∉ S ∧ P n).card : ℝ) =
      (((Finset.range X).filter P).card : ℝ) - ((S.filter P).card : ℝ) := by
  have hd : (Finset.range X).filter (fun n ↦ n ∉ S ∧ P n) =
      ((Finset.range X).filter P) \ S := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have hi : ((Finset.range X).filter P) ∩ S = S.filter P := by
    ext n
    simp only [Finset.mem_inter, Finset.mem_filter]
    exact ⟨fun ⟨⟨_, hp⟩, hs⟩ ↦ ⟨hs, hp⟩, fun ⟨hs, hp⟩ ↦ ⟨⟨hX hs, hp⟩, hs⟩⟩
  apply eq_sub_of_add_eq
  rw [hd, ← hi, ← Nat.cast_add, Finset.card_sdiff_add_card_inter]

/-- Deleting finitely many integers does not change a density measured relative to the primes. -/
theorem tendsto_filter_not_mem_finset_div_primeCount
    (P : ℕ → Prop) [DecidablePred P] (S : Finset ℕ) {δ : ℝ}
    (hP : Tendsto (fun X : ℕ ↦
      (((Finset.range X).filter P).card : ℝ) /
        (((Finset.range X).filter Nat.Prime).card : ℝ)) atTop (𝓝 δ)) :
    Tendsto (fun X : ℕ ↦
      (((Finset.range X).filter fun n ↦ n ∉ S ∧ P n).card : ℝ) /
        (((Finset.range X).filter Nat.Prime).card : ℝ)) atTop (𝓝 δ) := by
  have hzero : Tendsto (fun X : ℕ ↦ ((S.filter P).card : ℝ) /
      (((Finset.range X).filter Nat.Prime).card : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_card_filter_prime_range
  have hlim := hP.sub hzero
  simp only [sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (S.sup id + 1)] with X hX
  have hsub : S ⊆ Finset.range X := by
    intro n hn
    exact Finset.mem_range.mpr <|
      lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)) hX
  rw [filter_range_card_not_mem_finset P S hsub, sub_div]

end FrobeniusDensity

end
end

section
/-!
# The mission's rational-prime indicator and Tau Ceti's Frobenius fibres

This interface uses the Frobenius and unramifiedness APIs of the Tau Ceti contributors,
from https://github.com/TauCetiProject/TauCeti, revision
`948fe4751b1fe528b6d580c522ca5d743d47f185`. The deep natural-density theorem is supplied by
Tau Ceti; the declarations here only identify its prime-set interface with the mission's.
-/

set_option autoImplicit false

open NumberField Ideal IsDedekindDomain
open NumberField.Chebotarev

namespace FrobeniusDensity

/-- The ideal in `ℤ` associated to a rational height-one prime is generated by its prime norm. -/
theorem ratPrimeIdeal_natGenerator_eq_under (v : HeightOneSpectrum (𝓞 ℚ)) :
    ratPrimeIdeal (Rat.HeightOneSpectrum.natGenerator v) = v.asIdeal.under ℤ := by
  rw [ratPrimeIdeal, Rat.HeightOneSpectrum.span_natGenerator, Ideal.under_def]
  have he : ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm : ℤ →+* 𝓞 ℚ) =
      algebraMap ℤ (𝓞 ℚ) :=
    (RingHom.eq_intCast' _).trans (RingHom.eq_intCast' _).symm
  rw [← he]
  exact (Ideal.comap_symm (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))).symm

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]

omit [IsGalois ℚ L] in
/-- Lying over the rational prime and over its height-one ideal in `𝓞 ℚ` agree. -/
theorem liesOver_ratPrimeIdeal_natGenerator_iff (v : HeightOneSpectrum (𝓞 ℚ))
    (Q : Ideal (𝓞 L)) :
    Q.LiesOver (ratPrimeIdeal (Rat.HeightOneSpectrum.natGenerator v)) ↔
      Q.LiesOver v.asIdeal := by
  have : IsScalarTower ℤ (𝓞 ℚ) (𝓞 L) :=
    IsScalarTower.of_algebraMap_eq' ((RingHom.eq_intCast' _).trans
      (RingHom.eq_intCast' _).symm)
  constructor
  · intro h
    refine ⟨?_⟩
    rw [Ideal.under_ringOfIntegers_rat_eq_map, ← h.over,
      ratPrimeIdeal_natGenerator_eq_under, Ideal.under_def]
    exact (Ideal.map_comap_of_surjective _
      (Rat.algebraMap_int_ringOfIntegers_eq ▸ Rat.ringOfIntegersEquiv.symm.surjective)
      v.asIdeal).symm
  · intro h
    refine ⟨?_⟩
    rw [ratPrimeIdeal_natGenerator_eq_under, h.over, Ideal.under_under]

/-- The mission's arithmetic Frobenius indicator is exactly Tau Ceti's Frobenius fibre. -/
theorem classIndicator_natGenerator_eq_one_iff (σ : L ≃ₐ[ℚ] L)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    LanglandsTunnell.classIndicator σ (Rat.HeightOneSpectrum.natGenerator v) = 1 ↔
      v ∈ frobeniusPrimeSet ℚ L (ConjClasses.mk σ) := by
  classical
  simp only [LanglandsTunnell.classIndicator, ite_eq_left_iff, zero_ne_one, imp_false,
    not_not]
  constructor
  · rintro ⟨hp, Q, hQ, hQP, hi, hc⟩
    have : Q.IsPrime := hQ
    have : Q.LiesOver v.asIdeal := (liesOver_ratPrimeIdeal_natGenerator_iff v Q).mp hQP
    have : Finite (𝓞 L ⧸ Q) :=
      finite_quotient_of_ne_bot (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q)
    have : Algebra.IsUnramifiedAt (𝓞 ℚ) Q :=
      (Ideal.isUnramifiedAt_iff_inertia_eq_bot (K := ℚ) Q).mpr hi
    have hur : ∀ (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver v.asIdeal],
        Algebra.IsUnramifiedAt (𝓞 ℚ) P := fun P _ _ ↦
      Ideal.isUnramifiedAt_of_isUnramifiedAt_of_isGaloisGroup v.asIdeal Q P (L ≃ₐ[ℚ] L)
    refine ⟨hur, ?_⟩
    exact (artinSymbol_eq_mk_of_isArithFrobAt v.asIdeal hur Q _
      ((Ideal.isArithFrobAt_ringOfIntegers_rat_iff _ Q).mpr
        (IsArithFrobAt.arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q))).trans
      (ConjClasses.mk_eq_mk_iff_isConj.mpr hc).symm
  · rintro ⟨hur, hc⟩
    let Q : v.asIdeal.primesOver (𝓞 L) := Classical.choice inferInstance
    have : Q.1.IsPrime := Q.2.1
    have : Q.1.LiesOver v.asIdeal := Q.2.2
    have : Finite (𝓞 L ⧸ Q.1) :=
      finite_quotient_of_ne_bot (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q.1)
    refine ⟨Rat.HeightOneSpectrum.prime_natGenerator v, Q.1, inferInstance,
      (liesOver_ratPrimeIdeal_natGenerator_iff v Q.1).mpr inferInstance,
      (Ideal.isUnramifiedAt_iff_inertia_eq_bot (K := ℚ) Q.1).mp (hur Q.1), ?_⟩
    apply ConjClasses.mk_eq_mk_iff_isConj.mp
    exact hc.symm.trans (artinSymbol_eq_mk_of_isArithFrobAt v.asIdeal hur Q.1 _
      ((Ideal.isArithFrobAt_ringOfIntegers_rat_iff _ Q.1).mpr
        (IsArithFrobAt.arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q.1)))

end FrobeniusDensity

end

section
/-!
# Transporting Tau Ceti's rational prime counts to the mission

Tau Ceti counts height-one prime ideals using inclusive real norm cutoffs. The mission counts
rational primes in `Finset.range X`. The prime correspondence and the cutoff `X - 1` identify
these counts exactly. Together with finite-exclusion invariance, this transports Tau Ceti's
natural-density Chebotarev theorem without any further analytic input.

The prime-counting definitions and Frobenius interface are due to the Tau Ceti contributors:
https://github.com/TauCetiProject/TauCeti, revision `948fe4751b1fe528b6d580c522ca5d743d47f185`.
-/

set_option autoImplicit false

open NumberField Ideal IsDedekindDomain Filter Topology
open NumberField.Chebotarev

namespace FrobeniusDensity

/-- An inclusive norm cutoff at `X - 1` corresponds to the strict rational-prime cutoff `X`. -/
theorem mem_primesLE_rat_sub_one_iff (X : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    v ∈ TauCeti.primesLE ℚ ((X : ℝ) - 1) ↔ Rat.HeightOneSpectrum.natGenerator v < X := by
  rw [TauCeti.mem_normLE, Rat.HeightOneSpectrum.absNorm_asIdeal, le_sub_iff_add_le]
  exact_mod_cast (Nat.add_one_le_iff :
    Rat.HeightOneSpectrum.natGenerator v + 1 ≤ X ↔ Rat.HeightOneSpectrum.natGenerator v < X)

/-- Corresponding rational primes and height-one primes give the same finite counts. -/
theorem tauCeti_primeCount_rat_eq_filter_range
    (S : Set (HeightOneSpectrum (𝓞 ℚ))) (P : ℕ → Prop) [DecidablePred P]
    (hprime : ∀ n, P n → n.Prime)
    (hS : ∀ v, v ∈ S ↔ P (Rat.HeightOneSpectrum.natGenerator v)) (X : ℕ) :
    TauCeti.primeCount ℚ S ((X : ℝ) - 1) = (((Finset.range X).filter P).card : ℝ) := by
  classical
  rw [TauCeti.primeCount_eq_card]
  congr 1
  refine Finset.card_bij (fun v _ ↦ Rat.HeightOneSpectrum.natGenerator v) ?_ ?_ ?_
  · intro v hv
    rcases Finset.mem_filter.mp hv with ⟨hvX, hvS⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      ((mem_primesLE_rat_sub_one_iff X v).mp hvX), (hS v).mp hvS⟩
  · intro v hv w hw hvw
    exact (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective (Subtype.ext hvw)
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnX, hnP⟩
    let v := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨n, hprime n hnP⟩
    have hvn : Rat.HeightOneSpectrum.natGenerator v = n :=
      congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply
        ⟨n, hprime n hnP⟩)
    refine ⟨v, Finset.mem_filter.mpr ⟨?_, ?_⟩, hvn⟩
    · exact (mem_primesLE_rat_sub_one_iff X v).mpr (hvn ▸ Finset.mem_range.mp hnX)
    · exact (hS v).mpr (hvn ▸ hnP)

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]

/-- The mission's class indicator vanishes away from rational primes. -/
theorem prime_of_classIndicator_eq_one (σ : L ≃ₐ[ℚ] L) {n : ℕ}
    (h : LanglandsTunnell.classIndicator σ n = 1) : n.Prime := by
  classical
  unfold LanglandsTunnell.classIndicator at h
  split_ifs at h with hn
  exact hn.choose

/-- Tau Ceti's Frobenius prime count agrees with the mission's strict rational-prime count. -/
theorem tauCeti_frobeniusPrimeCount_eq_filter_range (σ : L ≃ₐ[ℚ] L) (X : ℕ) :
    TauCeti.primeCount ℚ (frobeniusPrimeSet ℚ L (ConjClasses.mk σ)) ((X : ℝ) - 1) =
      (((Finset.range X).filter fun n ↦ LanglandsTunnell.classIndicator σ n = 1).card : ℝ) := by
  classical
  exact tauCeti_primeCount_rat_eq_filter_range _ _
    (fun n hn ↦ prime_of_classIndicator_eq_one σ hn)
    (fun v ↦ (classIndicator_natGenerator_eq_one_iff σ v).symm) X

/-- The denominator in Tau Ceti's density over `ℚ` is the mission's rational-prime count. -/
theorem tauCeti_primeCount_rat_univ_eq_filter_range (X : ℕ) :
    TauCeti.primeCount ℚ Set.univ ((X : ℝ) - 1) =
      (((Finset.range X).filter Nat.Prime).card : ℝ) :=
  tauCeti_primeCount_rat_eq_filter_range _ _ (fun _ hn ↦ hn)
    (fun v ↦ iff_of_true (Set.mem_univ v) (Rat.HeightOneSpectrum.prime_natGenerator v)) X

/-- The defining ratio of Tau Ceti's natural density transports to strict rational-prime counts. -/
theorem tendsto_classIndicator_div_primeCount_of_tauCeti (σ : L ≃ₐ[ℚ] L) {δ : ℝ}
    (h : Tendsto (fun x : ℝ ↦
      TauCeti.primeCount ℚ (frobeniusPrimeSet ℚ L (ConjClasses.mk σ)) x /
        TauCeti.primeCount ℚ Set.univ x) atTop (𝓝 δ)) :
    Tendsto (fun X : ℕ ↦
      (((Finset.range X).filter fun n ↦ LanglandsTunnell.classIndicator σ n = 1).card : ℝ) /
        (((Finset.range X).filter Nat.Prime).card : ℝ)) atTop (𝓝 δ) := by
  have hcut : Tendsto (fun X : ℕ ↦ (X : ℝ) - 1) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def, tauCeti_frobeniusPrimeCount_eq_filter_range,
    tauCeti_primeCount_rat_univ_eq_filter_range] using h.comp hcut

/-- The complete mission density statement follows from Tau Ceti's natural-density ratio. -/
theorem tendsto_classIndicator_not_mem_div_primeCount_of_tauCeti
    (σ : L ≃ₐ[ℚ] L) (S : Finset ℕ) {δ : ℝ}
    (h : Tendsto (fun x : ℝ ↦
      TauCeti.primeCount ℚ (frobeniusPrimeSet ℚ L (ConjClasses.mk σ)) x /
        TauCeti.primeCount ℚ Set.univ x) atTop (𝓝 δ)) :
    Tendsto (fun X : ℕ ↦
      (((Finset.range X).filter fun n ↦ n ∉ S ∧
        LanglandsTunnell.classIndicator σ n = 1).card : ℝ) /
        (((Finset.range X).filter Nat.Prime).card : ℝ)) atTop (𝓝 δ) := by
  classical
  exact tendsto_filter_not_mem_finset_div_primeCount _ S
    (tendsto_classIndicator_div_primeCount_of_tauCeti σ h)

end FrobeniusDensity

end

section
/-!
This proof reuses the formal Chebotarev natural-density theorem by the Tau Ceti
contributors (Apache-2.0), adapted from:
https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/PrimeCounting/FrobeniusPrimeCount.lean

The mathematical Chebotarev proof is from Tau Ceti. The new interface identifies
its prime ideals over ℚ with this mission's rational-prime Frobenius indicator,
translates the cutoff, and removes a finite exceptional set.
-/

set_option autoImplicit false
open NumberField Ideal Filter Topology

theorem solution
    (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (σ : L ≃ₐ[ℚ] L) (S : Finset ℕ) :
    Tendsto
      (fun X : ℕ =>
        (((Finset.range X).filter fun ℓ =>
            ℓ ∉ S ∧ LanglandsTunnell.classIndicator σ ℓ = 1).card : ℝ) /
          (((Finset.range X).filter Nat.Prime).card : ℝ))
      atTop
      (𝓝 ((Nat.card {τ : L ≃ₐ[ℚ] L | IsConj σ τ} : ℝ) /
        (Nat.card (L ≃ₐ[ℚ] L) : ℝ))) := by
  exact FrobeniusDensity.tendsto_classIndicator_not_mem_div_primeCount_of_tauCeti σ S
    (NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet ℚ L (ConjClasses.mk σ))

end
