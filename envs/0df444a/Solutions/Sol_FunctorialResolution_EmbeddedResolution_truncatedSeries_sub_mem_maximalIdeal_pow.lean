-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.truncatedSeries_sub_mem_maximalIdeal_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:01:27.440502+00:00
-- url     : https://prove2.me/submissions/a44ddc5d-cfb0-4f8d-a689-ce0ab368c026

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansionComparison
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_TaylorExpansion_truncatedSeriesRingHom_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_TaylorExpansion_truncatedSeries_one
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_TaylorExpansion_truncatedSeries_sub_mem_span_singleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.TaylorExpansion.truncatedSeriesRingHom_apply


section
namespace FunctorialResolution.EmbeddedResolution
section
variable {k S : Type*} [CommRing k] [CommRing S] [Algebra k S]
end
section
variable {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra ℚ S]
end
section
open IsLocalRing
private theorem derivation_apply_eq_zero_of_formallyUnramified {P R : Type*} [CommRing P]
    [CommRing R] [Algebra P R] [Algebra.FormallyUnramified P R] {M : Type*} [AddCommGroup M]
    [Module P M] [Module R M] [IsScalarTower P R M] (d : Derivation P R M) (x : R) : d x = 0 := by
  have h0 : KaehlerDifferential.D P R x = 0 := Subsingleton.elim _ _
  have h1 : (Derivation.liftKaehlerDifferential d) (KaehlerDifferential.D P R x) = d x :=
    Derivation.liftKaehlerDifferential_comp_D d x
  rw [h0, map_zero] at h1
  exact h1.symm
private theorem sub_mem_pow_succ_of_sub_mem_pow (P : Type*) {R B : Type*} [CommRing P] [CommRing R]
    [CommRing B] [Algebra P R] [Algebra.FormallyUnramified P R]
    (φ' : R →+* B) (m : Ideal B) (T : R → B) (k : ℕ) (hk : 1 ≤ k)
    (hadd : ∀ x y : R, T (x + y) = T x + T y)
    (hone : T 1 = 1)
    (hmul : ∀ x y : R, T (x * y) - T x * T y ∈ m ^ (k + 1))
    (hP : ∀ x : P, T (algebraMap P R x) - φ' (algebraMap P R x) ∈ m ^ (k + 1))
    (hind : ∀ x : R, T x - φ' x ∈ m ^ k) (x : R) :
    T x - φ' x ∈ m ^ (k + 1) := by
  let _ : Algebra R B := φ'.toAlgebra
  let _ : Algebra P B := (φ'.comp (algebraMap P R)).toAlgebra
  have : IsScalarTower P R B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower P R (B ⧸ m ^ (k + 1)) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hleib : ∀ a b : R,
      T (a * b) - φ' (a * b) - (φ' a * (T b - φ' b) + φ' b * (T a - φ' a)) ∈ m ^ (k + 1) := by
    intro a b
    have h1 : T (a * b) - T a * T b ∈ m ^ (k + 1) := hmul a b
    have h2 : (T a - φ' a) * (T b - φ' b) ∈ m ^ (k + 1) := by
      have h3 : (T a - φ' a) * (T b - φ' b) ∈ m ^ k * m ^ k :=
        Ideal.mul_mem_mul (hind a) (hind b)
      have h4 : m ^ k * m ^ k ≤ m ^ (k + 1) := by
        rw [← pow_add]
        exact Ideal.pow_le_pow_right (by omega)
      exact h4 h3
    have heq : T (a * b) - φ' (a * b) - (φ' a * (T b - φ' b) + φ' b * (T a - φ' a))
        = T (a * b) - T a * T b + (T a - φ' a) * (T b - φ' b) := by
      rw [map_mul]
      ring
    rw [heq]
    exact Ideal.add_mem _ h1 h2
  let d : Derivation P R (B ⧸ m ^ (k + 1)) :=
    { toFun := fun y => Ideal.Quotient.mk (m ^ (k + 1)) (T y - φ' y)
      map_add' := by
        intro a b
        show Ideal.Quotient.mk (m ^ (k + 1)) (T (a + b) - φ' (a + b))
            = Ideal.Quotient.mk (m ^ (k + 1)) (T a - φ' a)
              + Ideal.Quotient.mk (m ^ (k + 1)) (T b - φ' b)
        have harg : T (a + b) - φ' (a + b) = T a - φ' a + (T b - φ' b) := by
          rw [hadd, map_add]
          ring
        rw [harg, map_add]
      map_smul' := by
        intro p a
        show Ideal.Quotient.mk (m ^ (k + 1)) (T (p • a) - φ' (p • a))
            = p • Ideal.Quotient.mk (m ^ (k + 1)) (T a - φ' a)
        simp only [Algebra.smul_def]
        have halg : (algebraMap P (B ⧸ m ^ (k + 1))) p
            = Ideal.Quotient.mk (m ^ (k + 1)) (φ' (algebraMap P R p)) := rfl
        rw [halg, ← map_mul]
        refine Ideal.Quotient.eq.mpr ?_
        have h1 := hleib (algebraMap P R p) a
        have h2 : φ' a * (T (algebraMap P R p) - φ' (algebraMap P R p)) ∈ m ^ (k + 1) :=
          Ideal.mul_mem_left _ _ (hP p)
        have h3 := Ideal.add_mem _ h1 h2
        have heq : T (algebraMap P R p * a) - φ' (algebraMap P R p * a)
              - (φ' (algebraMap P R p) * (T a - φ' a)
                + φ' a * (T (algebraMap P R p) - φ' (algebraMap P R p)))
              + φ' a * (T (algebraMap P R p) - φ' (algebraMap P R p))
            = T (algebraMap P R p * a) - φ' (algebraMap P R p * a)
              - φ' (algebraMap P R p) * (T a - φ' a) := by
          ring
        rw [heq] at h3
        exact h3
      map_one_eq_zero' := by
        show Ideal.Quotient.mk (m ^ (k + 1)) (T 1 - φ' 1) = 0
        rw [hone, map_one, sub_self, map_zero]
      leibniz' := by
        intro a b
        show Ideal.Quotient.mk (m ^ (k + 1)) (T (a * b) - φ' (a * b))
            = a • Ideal.Quotient.mk (m ^ (k + 1)) (T b - φ' b)
              + b • Ideal.Quotient.mk (m ^ (k + 1)) (T a - φ' a)
        simp only [Algebra.smul_def]
        have halg : ∀ y : R, (algebraMap R (B ⧸ m ^ (k + 1))) y
            = Ideal.Quotient.mk (m ^ (k + 1)) (φ' y) := fun _ => rfl
        rw [halg a, halg b, ← map_mul, ← map_mul, ← map_add]
        exact Ideal.Quotient.eq.mpr (hleib a b) }
  have hdx : Ideal.Quotient.mk (m ^ (k + 1)) (T x - φ' x) = 0 :=
    derivation_apply_eq_zero_of_formallyUnramified d x
  exact Ideal.Quotient.eq_zero_iff_mem.mp hdx
end
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open IsLocalRing
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (P : Type*) [CommRing P] {A R B : Type*}
    [CommRing A] [CommRing R] [CommRing B] [Algebra P R] [Algebra A R]
    [Algebra.FormallyUnramified P R] [IsLocalRing B] [Algebra ℚ B]
    (φ φ' : R →+* B) (D : Derivation A R R) (β : B)
    (hcong : ∀ f : R, φ f - φ' f ∈ maximalIdeal B)
    (hβ : β ∈ maximalIdeal B)
    (hrep : IsTaylorExpansionOn P φ φ' D β)
    (N : ℕ) (hN : 1 ≤ N) (f : R) :
    TaylorExpansion.truncatedSeries φ D β N f - φ' f ∈ maximalIdeal B ^ N := by
  have hβN : β ^ N ∈ maximalIdeal B ^ N := Ideal.pow_mem_pow hβ N
  have hmulN : ∀ x y : R,
      TaylorExpansion.truncatedSeries φ D β N (x * y)
        - TaylorExpansion.truncatedSeries φ D β N x * TaylorExpansion.truncatedSeries φ D β N y
        ∈ maximalIdeal B ^ N :=
    fun x y => TaylorExpansion.truncatedSeries_mul_sub_mem φ D β N (maximalIdeal B ^ N) hβN x y
  have hbound : ∀ x : P,
      TaylorExpansion.truncatedSeries φ D β N (algebraMap P R x) - φ' (algebraMap P R x)
        ∈ maximalIdeal B ^ N := fun x => hrep N hN x
  have hbase : ∀ x : R, TaylorExpansion.truncatedSeries φ D β N x - φ' x ∈ maximalIdeal B ^ 1 := by
    intro x
    rw [pow_one]
    have h1 : TaylorExpansion.truncatedSeries φ D β N x - φ x ∈ Ideal.span ({β} : Set B) :=
      TaylorExpansion.truncatedSeries_sub_mem_span_singleton φ D β N hN x
    have h2 : Ideal.span ({β} : Set B) ≤ maximalIdeal B := by
      rw [Ideal.span_le]
      simpa using hβ
    have h4 : TaylorExpansion.truncatedSeries φ D β N x - φ' x
        = TaylorExpansion.truncatedSeries φ D β N x - φ x + (φ x - φ' x) := by ring
    rw [h4]
    exact Ideal.add_mem _ (h2 h1) (hcong x)
  have key : ∀ k : ℕ, 1 ≤ k → k ≤ N →
      ∀ x : R, TaylorExpansion.truncatedSeries φ D β N x - φ' x ∈ maximalIdeal B ^ k := by
    intro k
    induction k with
    | zero => intro h; exact absurd h (by omega)
    | succ k ih =>
      intro _ hkN
      rcases Nat.eq_zero_or_pos k with hk0 | hk1
      · subst hk0
        exact hbase
      · have hk1' : 1 ≤ k := hk1
        have hkle : maximalIdeal B ^ N ≤ maximalIdeal B ^ (k + 1) :=
          Ideal.pow_le_pow_right hkN
        exact fun x =>
          sub_mem_pow_succ_of_sub_mem_pow P φ' (maximalIdeal B) (TaylorExpansion.truncatedSeries φ D β N) k hk1'
            (fun a b => TaylorExpansion.truncatedSeries_add φ D β N a b)
            (TaylorExpansion.truncatedSeries_one φ D β N hN)
            (fun a b => hkle (hmulN a b))
            (fun p => hkle (hbound p))
            (ih hk1' (by omega)) x
  exact key N hN le_rfl f
end FunctorialResolution.EmbeddedResolution
