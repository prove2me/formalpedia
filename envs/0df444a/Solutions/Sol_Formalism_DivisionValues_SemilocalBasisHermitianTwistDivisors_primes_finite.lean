-- Prove2me | solution 1 for Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors.primes_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:39.664795+00:00
-- url     : https://prove2.me/submissions/146dfc40-4657-4e8b-9972-e82797b13556

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Theorems.Thm_Formalism_DivisionValues_SemilocalBasisHermitianTwistDivisors_mem_hcompl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) :
    {P : Ideal (A w) | P.IsPrime}.Finite := by
  apply ((({⊥, w.asIdeal, (conjPl w).asIdeal} : Set (Ideal (𝓞 K))).toFinite.image
    (Ideal.map (algebraMap (𝓞 K) (A w))))).subset
  intro P hP
  have hP' : P.IsPrime := hP
  obtain ⟨hQ, hdisj⟩ :=
    (IsLocalization.isPrime_iff_isPrime_disjoint (Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal) (A w) P).mp hP'
  refine ⟨P.comap (algebraMap (𝓞 K) (A w)), ?_,
    IsLocalization.map_under (Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal) (A w) P⟩
  set Q := P.comap (algebraMap (𝓞 K) (A w))
  have hsub : (Q : Set (𝓞 K)) ⊆ (w.asIdeal : Set (𝓞 K)) ∪ ((conjPl w).asIdeal : Set (𝓞 K)) := by
    intro x hx
    by_contra hn
    simp only [Set.mem_union, SetLike.mem_coe, not_or] at hn
    exact Set.disjoint_left.mp hdisj (mem_hcompl w x hn.1 hn.2) hx
  by_cases hb : Q = ⊥
  · exact Or.inl hb
  have hmax : Q.IsMaximal := hQ.isMaximal hb
  rcases Ideal.subset_union.mp hsub with h | h
  · exact Or.inr (Or.inl (hmax.eq_of_le w.isPrime.ne_top h))
  · exact Or.inr (Or.inr (hmax.eq_of_le (conjPl w).isPrime.ne_top h))
end Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors
