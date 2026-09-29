-- Prove2me | solution 1 for Deformation.map_coeff_mem_span_of_forall_coeff_ghostComponent_eq_logCovector
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/23e083db-04ba-5389-a895-c791095a9e3c

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_MvFormalGroup_natCast_mul_coeff_add_single_mem_span_pow_degree_of_subst_rescale_eq_add
import Theorems.Thm_MvFormalGroup_coeff_mem_span_sup_pow_of_forall_coeff_ghostComponent_eq_logCovector_of_slope
import Theorems.Thm_MvFormalGroup_exists_coeff_mem_span_pow_sub_log_of_isNilpotent_hasseWitt
import Theorems.Thm_MvFormalGroup_isNilpotent_hasseWittMatrix_nthSeries_of_isLocalRing_cartierDual
import Theorems.Thm_WittVector_coeff_mem_span_of_ghostComponent_mem_span_pow_of_isReduced
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_map_coeff_mem_span_of_forall_coeff_ghostComponent_eq_logCovector

set_option autoImplicit false

open scoped TensorProduct
open MvPowerSeries

universe u v

namespace S17C1

section PS
variable {𝓞 : Type u} [CommRing 𝓞] {σ : Type v}

theorem exists_le_degree_eq [DecidableEq σ] : ∀ (E : ℕ) (μ : σ →₀ ℕ), E ≤ μ.degree → ∃ ν : σ →₀ ℕ, ν ≤ μ ∧ ν.degree = E
  | 0, μ, _ => ⟨0, by simp, by simp⟩
  | E + 1, μ, h => by
    obtain ⟨ν, hν, hνE⟩ := exists_le_degree_eq E μ (Nat.le_of_succ_le h)

    have hne : μ - ν ≠ 0 := by
      intro h0
      have : μ = ν := le_antisymm (tsub_eq_zero_iff_le.1 h0) hν
      rw [this, hνE] at h
      omega
    obtain ⟨t, ht⟩ : ∃ t, (μ - ν) t ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (Finsupp.ext hall)
    refine ⟨ν + Finsupp.single t 1, ?_, ?_⟩
    · intro s
      simp only [Finsupp.coe_add, Pi.add_apply]
      have h1 := hν s
      have h2 : (μ - ν) t = μ t - ν t := Finsupp.tsub_apply _ _ _
      by_cases hst : t = s
      · subst hst
        rw [Finsupp.single_eq_same]
        omega
      · rw [Finsupp.single_apply, if_neg hst, add_zero]
        exact h1
    · rw [map_add, hνE, Finsupp.degree_single]

theorem monomial_mem_pow (ν : σ →₀ ℕ) :
    (monomial ν (1 : 𝓞) : MvPowerSeries σ 𝓞) ∈ (Ideal.span (Set.range (X : σ → MvPowerSeries σ 𝓞))) ^ ν.degree := by
  classical
  induction ν using Finsupp.induction with
  | zero => simp
  | single_add t n ν ht hn ih =>
    rw [show (monomial (Finsupp.single t n + ν) (1 : 𝓞) : MvPowerSeries σ 𝓞) =
        monomial (Finsupp.single t n) 1 * monomial ν 1 by rw [monomial_mul_monomial, one_mul],
      map_add, Finsupp.degree_single, pow_add]
    refine Ideal.mul_mem_mul ?_ ih
    rw [show (monomial (Finsupp.single t n) (1 : 𝓞) : MvPowerSeries σ 𝓞) = X t ^ n by
      rw [X_pow_eq]]
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self t)) n

theorem mem_pow_of_forall_le_degree [Fintype σ] [DecidableEq σ] (E : ℕ) (f : MvPowerSeries σ 𝓞)
    (hf : ∀ μ : σ →₀ ℕ, coeff μ f ≠ 0 → E ≤ μ.degree) :
    f ∈ (Ideal.span (Set.range (X : σ → MvPowerSeries σ 𝓞))) ^ E := by
  classical

  let fl : (σ →₀ ℕ) → (σ →₀ ℕ) := fun μ =>
    if h : E ≤ μ.degree then Classical.choose (exists_le_degree_eq (σ := σ) E μ h) else 0
  have hfl : ∀ μ, E ≤ μ.degree → fl μ ≤ μ ∧ (fl μ).degree = E := fun μ h => by
    simp only [fl, dif_pos h]; exact Classical.choose_spec (exists_le_degree_eq (σ := σ) E μ h)

  let g : (σ →₀ ℕ) → MvPowerSeries σ 𝓞 := fun ν κ => if fl (κ + ν) = ν then coeff (κ + ν) f else 0
  let S : Finset (σ →₀ ℕ) := (Finset.univ : Finset σ).finsuppAntidiag E
  have hS : ∀ ν : σ →₀ ℕ, ν ∈ S ↔ ν.degree = E := fun ν => by
    show ν ∈ (Finset.univ : Finset σ).finsuppAntidiag E ↔ _
    have hsum : ∑ i ∈ ν.support, ν i = ∑ i, ν i :=
      Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simpa using hi)
    rw [Finset.mem_finsuppAntidiag, Finsupp.degree_apply, hsum]
    simp
  have hdec : f = ∑ ν ∈ S, monomial ν (1 : 𝓞) * g ν := by
    ext κ
    rw [map_sum]
    simp only [coeff_monomial_mul, one_mul]
    by_cases hκ : E ≤ κ.degree
    · obtain ⟨hle, hdeg⟩ := hfl κ hκ
      rw [Finset.sum_eq_single (fl κ)]
      · rw [if_pos hle]
        show coeff κ f = (if fl (κ - fl κ + fl κ) = fl κ then coeff (κ - fl κ + fl κ) f else 0)
        rw [tsub_add_cancel_of_le hle, if_pos rfl]
      · intro ν hν hne
        split_ifs with hνκ
        · show (if fl (κ - ν + ν) = ν then coeff (κ - ν + ν) f else 0) = 0
          rw [tsub_add_cancel_of_le hνκ, if_neg (Ne.symm hne)]
        · rfl
      · intro hnot
        exact absurd ((hS _).2 hdeg) hnot
    · have h0 : coeff κ f = 0 := by
        by_contra hne; exact hκ (hf κ hne)
      rw [h0, eq_comm]
      refine Finset.sum_eq_zero fun ν hν => ?_
      split_ifs with hνκ
      · show (if fl (κ - ν + ν) = ν then coeff (κ - ν + ν) f else 0) = 0
        rw [tsub_add_cancel_of_le hνκ]
        split_ifs
        · exact h0
        · rfl
      · rfl
  rw [hdec]
  refine Ideal.sum_mem _ fun ν hν => ?_
  have := monomial_mem_pow (𝓞 := 𝓞) ν
  rw [(hS ν).1 hν] at this
  exact Ideal.mul_mem_right _ _ this

end PS

variable (p : ℕ) [Fact p.Prime] in

theorem ghostComponent_map {R : Type v} {S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (x : WittVector p R) (n : ℕ) :
    WittVector.ghostComponent n (WittVector.map f x) = f (WittVector.ghostComponent n x) := by
  rw [WittVector.ghostComponent_apply, WittVector.ghostComponent_apply, MvPolynomial.aeval_def,
    MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

theorem main
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1)
    (hφT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
    (v : ℕ) (R : Type v) [CommRing R] [HopfAlgebra 𝓞 R] [Module.Free 𝓞 R] [Module.Finite 𝓞 R]
    [IsAdicComplete (Ideal.span {(p : R)}) R]
    [IsAdicComplete (Ideal.span {(p : R ⊗[𝓞] R)}) (R ⊗[𝓞] R)]
    (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R) (hπ : Function.Surjective π)
    (hπX : ∀ i, π (X i) ∈ (Ideal.span {(p : R)}).radical)
    (hπeval : ∀ G : MvPowerSeries (Fin d) 𝓞,
      π G = MvFormalGroup.adicEval (Ideal.span {(p : R)}) (fun i => π (X i)) G)
    (hkerπ : RingHom.ker π = Ideal.span (Set.range (F.nthSeries (p ^ v))))
    (hπΔ : ∀ i, Coalgebra.comul (R := 𝓞) (π (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : R ⊗[𝓞] R)})
        (Sum.elim (fun j => π (X j) ⊗ₜ[𝓞] (1 : R)) (fun j => (1 : R) ⊗ₜ[𝓞] π (X j)))
        (F.toPowerSeries i))
    (hunip : IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) R))) :
    ∃ n₀ : ℕ, ∀ (M : ℕ) (i : Fin d) (c : (Fin d →₀ ℕ) → 𝓞),
        (∀ m : Fin d →₀ ℕ,
          (m.degree ≤ M → c m = (p : 𝓞) ^ (M - m.degree) * (φ i).coeff m) ∧
          (M < m.degree → c m * (p : 𝓞) ^ (m.degree - M) = (φ i).coeff m ∨
            (c m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - M) ∣ (φ i).coeff m))) →
        ∀ ℓ : WittVector p (MvPowerSeries (Fin d) 𝓞),
          (∀ n : ℕ, n < M → ∀ m' : Fin d →₀ ℕ,
            (WittVector.ghostComponent n ℓ).coeff m' = c (p ^ (M - 1 - n) • m')) →
          ∀ n : ℕ, n₀ ≤ n → n < M → π (ℓ.coeff (M - 1 - n)) ∈ Ideal.span {(p : R)} := by
  classical

  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : ℕ, (Ideal.span (Set.range fun j : Fin d => π (X j))) ^ E₀ ≤ Ideal.span {(p : R)} :=
    Ideal.exists_pow_le_of_le_radical_of_fg (Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hπX j))
      ⟨(Finset.univ.image fun j : Fin d => π (X j)), by simp⟩
  have hπpow : ∀ f : MvPowerSeries (Fin d) 𝓞,
      f ∈ Ideal.span {(p : MvPowerSeries (Fin d) 𝓞)} ⊔
        (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) 𝓞))) ^ E₀ →
      π f ∈ Ideal.span {(p : R)} := by
    intro f hf
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
    rw [map_add]
    refine Ideal.add_mem _ ?_ ?_
    · obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul, map_natCast]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · have : Ideal.map π ((Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) 𝓞))) ^ E₀) ≤
          Ideal.span {(p : R)} := by
        rw [Ideal.map_pow, Ideal.map_span]
        refine le_trans (Ideal.pow_right_mono ?_ E₀) hE₀
        refine Ideal.span_le.2 ?_
        rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
        exact Ideal.subset_span ⟨j, rfl⟩
      exact this (Ideal.mem_map_of_mem π hb)

  have hφint : ∀ (i j : Fin d) (m : Fin d →₀ ℕ),
      ((m j + 1 : ℕ) : 𝓞) * (φ i).coeff (m + Finsupp.single j 1) ∈ Ideal.span {(p : 𝓞) ^ m.degree} :=
    fun i j m => MvFormalGroup.natCast_mul_coeff_add_single_mem_span_pow_degree_of_subst_rescale_eq_add
      p hp F Fp hFp hFp0 φ hφ0 hφ1 hφF i j m

  rcases Nat.eq_zero_or_pos v with hv0 | hv
  ·

    subst hv0
    have hX0 : ∀ j, π (X j) = 0 := by
      intro j
      have : (X j : MvPowerSeries (Fin d) 𝓞) ∈ RingHom.ker π := by
        rw [hkerπ]
        refine Ideal.subset_span ⟨j, ?_⟩
        show F.nthSeries (p ^ 0) j = X j
        rw [pow_zero, show (1 : ℕ) = 0 + 1 from rfl, MvFormalGroup.nthSeries_succ, MvFormalGroup.nthSeries_zero]
        exact MvFormalGroup.subst_elim_zero_X F j
      exact this
    refine ⟨0, fun M i c hc ℓ hℓ n hn hnM => ?_⟩
    set f := ℓ.coeff (M - 1 - n) with hf

    have hsplit : f - C (constantCoeff f) ∈ Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) 𝓞)) := by
      have := mem_pow_of_forall_le_degree (𝓞 := 𝓞) 1 (f - C (constantCoeff f)) (fun μ hμ => ?_)
      · simpa using this
      · rw [Nat.one_le_iff_ne_zero]
        intro h0
        rw [Finsupp.degree_eq_zero_iff] at h0
        subst h0
        apply hμ
        rw [map_sub, coeff_C, if_pos rfl, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, sub_self]
    have hπg : π (f - C (constantCoeff f)) = 0 := by
      have hle : Ideal.map π (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) 𝓞))) = ⊥ := by
        rw [Ideal.map_span, Ideal.span_eq_bot]
        rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
        exact hX0 j
      have := Ideal.mem_map_of_mem π hsplit
      rwa [hle, Ideal.mem_bot] at this

    have hconst : constantCoeff f ∈ Ideal.span {(p : 𝓞)} := by
      have hred𝓞 : IsReduced (𝓞 ⧸ Ideal.span {(p : 𝓞)}) := by
        have hsurj : Function.Surjective (algebraMap 𝓞 (ZMod p)) := ZMod.ringHom_surjective _
        let e : 𝓞 ⧸ Ideal.span {(p : 𝓞)} ≃+* ZMod p :=
          (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
        exact isReduced_of_injective e e.injective
      have key := WittVector.coeff_mem_span_of_ghostComponent_mem_span_pow_of_isReduced p hp hred𝓞
        (WittVector.map (constantCoeff : MvPowerSeries (Fin d) 𝓞 →+* 𝓞) ℓ) M ?_ (M - 1 - n) (by omega)
      · simpa [WittVector.map_coeff] using key
      · rw [ghostComponent_map]
        have h0 : constantCoeff (WittVector.ghostComponent (M - 1) ℓ) = 0 := by
          rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hℓ (M - 1) (by omega) 0, smul_zero,
            (hc 0).1 (by simp), MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ0, mul_zero]
        rw [h0]
        exact Ideal.zero_mem _
    rw [show f = (f - C (constantCoeff f)) + C (constantCoeff f) by ring, map_add, hπg, zero_add]
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hconst
    rw [← ht, map_mul, map_natCast, map_mul, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

  have hHW := MvFormalGroup.isNilpotent_hasseWittMatrix_nthSeries_of_isLocalRing_cartierDual p hp hker F v hv R π
    hπ hπX hπeval hkerπ hπΔ hunip
  obtain ⟨A, B, C, hAB, hslope⟩ :=
    MvFormalGroup.exists_coeff_mem_span_pow_sub_log_of_isNilpotent_hasseWitt p hp hker F Fp hFp hFp0 φ hφ0 hφ1
      hφF hHW
  choose n₂ hn₂ using fun i : Fin d =>
    MvFormalGroup.coeff_mem_span_sup_pow_of_forall_coeff_ghostComponent_eq_logCovector_of_slope p hp hker (φ i)
      (hφint i) A B C hAB (hslope i) E₀
  refine ⟨Finset.univ.sup n₂ + 1, fun M i c hc ℓ hℓ n hn hnM => ?_⟩
  apply hπpow
  refine hn₂ i M c hc ℓ hℓ (M - 1 - n) ?_
  have : n₂ i ≤ Finset.univ.sup n₂ := Finset.le_sup (Finset.mem_univ i)
  omega

end S17C1

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1)
    (hφT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
    (v : ℕ) (R : Type v) [CommRing R] [HopfAlgebra 𝓞 R] [Module.Free 𝓞 R] [Module.Finite 𝓞 R]
    [IsAdicComplete (Ideal.span {(p : R)}) R]
    [IsAdicComplete (Ideal.span {(p : R ⊗[𝓞] R)}) (R ⊗[𝓞] R)]
    (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R) (hπ : Function.Surjective π)
    (hπX : ∀ i, π (X i) ∈ (Ideal.span {(p : R)}).radical)
    (hπeval : ∀ G : MvPowerSeries (Fin d) 𝓞,
      π G = MvFormalGroup.adicEval (Ideal.span {(p : R)}) (fun i => π (X i)) G)
    (hkerπ : RingHom.ker π = Ideal.span (Set.range (F.nthSeries (p ^ v))))
    (hπΔ : ∀ i, Coalgebra.comul (R := 𝓞) (π (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : R ⊗[𝓞] R)})
        (Sum.elim (fun j => π (X j) ⊗ₜ[𝓞] (1 : R)) (fun j => (1 : R) ⊗ₜ[𝓞] π (X j)))
        (F.toPowerSeries i))
    (hunip : IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) R))) :
    ∃ n₀ : ℕ, ∀ (M : ℕ) (i : Fin d) (c : (Fin d →₀ ℕ) → 𝓞),
        (∀ m : Fin d →₀ ℕ,
          (m.degree ≤ M → c m = (p : 𝓞) ^ (M - m.degree) * (φ i).coeff m) ∧
          (M < m.degree → c m * (p : 𝓞) ^ (m.degree - M) = (φ i).coeff m ∨
            (c m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - M) ∣ (φ i).coeff m))) →
        ∀ ℓ : WittVector p (MvPowerSeries (Fin d) 𝓞),
          (∀ n : ℕ, n < M → ∀ m' : Fin d →₀ ℕ,
            (WittVector.ghostComponent n ℓ).coeff m' = c (p ^ (M - 1 - n) • m')) →
          ∀ n : ℕ, n₀ ≤ n → n < M → π (ℓ.coeff (M - 1 - n)) ∈ Ideal.span {(p : R)} :=
  S17C1.main p hp hker F Fp hFp hFp0 φ hφ0 hφ1 hφT hφF v R π hπ hπX hπeval hkerπ hπΔ hunip

end S_Deformation_map_coeff_mem_span_of_forall_coeff_ghostComponent_eq_logCovector
end P2MW
export P2MW.S_Deformation_map_coeff_mem_span_of_forall_coeff_ghostComponent_eq_logCovector (solution)
