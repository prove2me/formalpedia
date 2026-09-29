-- Prove2me | solution 1 for FrobeniusDensity.card_setOf_isConj_mul_card_centralizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/a1826b3d-2d73-56fd-a638-0e2400a5a459

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FrobeniusDensity_card_setOf_isConj_mul_card_centralizer

set_option autoImplicit false

open scoped Classical

namespace FltWs24
namespace RationalClass

variable {G : Type*} [Group G]

theorem coprime_mod_iff {k n : ℕ} : (k % n).Coprime n ↔ k.Coprime n := by
  unfold Nat.Coprime
  rw [← Nat.gcd_rec, Nat.gcd_comm]

theorem card_filter_conj_eq [Fintype G] (a b : G) (h : IsConj a b) :
    (Finset.univ.filter (fun g : G => g * a * g⁻¹ = b)).card
      = Fintype.card (Subgroup.centralizer ({a} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have key : ∀ g : G, g * a * g⁻¹ = b ↔ c⁻¹ * g ∈ Subgroup.centralizer ({a} : Set G) := by
    intro g
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hg
      have h1 : g * a * g⁻¹ = c * a * c⁻¹ := by rw [hg, hc]
      have h2 : c⁻¹ * (g * a * g⁻¹) * c = a := by
        rw [h1]; group
      calc c⁻¹ * g * a = c⁻¹ * (g * a * g⁻¹) * c * (c⁻¹ * g) := by group
        _ = a * (c⁻¹ * g) := by rw [h2]
    · intro hg
      have h3 : g * a * g⁻¹ = c * (c⁻¹ * g * a) * g⁻¹ := by group
      rw [h3, hg, ← hc]; group
  rw [← Fintype.card_coe]
  refine Fintype.card_congr (Equiv.subtypeEquiv (Equiv.mulLeft c⁻¹) (fun g => ?_))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_mulLeft]
  exact key g

theorem card_filter_conj_eq_zero [Fintype G] (a b : G) (h : ¬ IsConj a b) :
    (Finset.univ.filter (fun g : G => g * a * g⁻¹ = b)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro g _ hg
  exact h (isConj_iff.mpr ⟨g, hg⟩)

theorem centralizer_pow_eq_of_coprime (σ : G) {k : ℕ} (hk : k.Coprime (orderOf σ)) :
    Subgroup.centralizer ({σ ^ k} : Set G) = Subgroup.centralizer ({σ} : Set G) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hk
    rw [← hm]
    exact (Commute.pow_right (show Commute g (σ ^ k) from h) m)
  · intro h
    exact (Commute.pow_right (show Commute g σ from h) k)

theorem ncard_conj_gen_eq_of_rational [Finite G] (σ τ : G)
    (hrat : ∀ k : ℕ, k.Coprime (orderOf σ) → IsConj σ (σ ^ k)) :
    {g : G | ∃ k : ℕ, k.Coprime (orderOf σ) ∧ g * σ ^ k * g⁻¹ = τ}.ncard
      = if IsConj σ τ then (orderOf σ).totient * Nat.card (Subgroup.centralizer ({σ} : Set G))
        else 0 := by
  haveI := Fintype.ofFinite G
  set n := orderOf σ with hn
  have hn0 : 0 < n := orderOf_pos σ
  set K : Finset ℕ := (Finset.range n).filter (fun k => n.Coprime k) with hK
  have hKcard : K.card = n.totient := (Nat.totient_eq_card_coprime n).symm
  set S : Set G := {g : G | ∃ k : ℕ, k.Coprime (orderOf σ) ∧ g * σ ^ k * g⁻¹ = τ} with hS
  set T : ℕ → Finset G := fun k => Finset.univ.filter (fun g : G => g * σ ^ k * g⁻¹ = τ) with hT
  have hST : S.toFinset = K.biUnion T := by
    ext g
    simp only [Set.mem_toFinset, hS, Set.mem_setOf_eq, Finset.mem_biUnion, hK, hT,
      Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, hk, hgk⟩
      refine ⟨k % n, ⟨Nat.mod_lt _ hn0, ?_⟩, ?_⟩
      · exact Nat.coprime_comm.mp (coprime_mod_iff.mpr hk)
      · rwa [pow_mod_orderOf]
    · rintro ⟨k, ⟨-, hk⟩, hgk⟩
      exact ⟨k, Nat.coprime_comm.mp hk, hgk⟩
  have hdisj : (K : Set ℕ).PairwiseDisjoint T := by
    intro k hk k' hk' hne
    simp only [Finset.coe_filter, hK, Set.mem_setOf_eq, Finset.mem_range] at hk hk'
    rw [Function.onFun, Finset.disjoint_left]
    intro g hg hg'
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hg hg'
    apply hne
    have hpow : σ ^ k = σ ^ k' := by
      have := hg.trans hg'.symm
      simpa using this
    exact pow_injOn_Iio_orderOf (Set.mem_Iio.mpr hk.1) (Set.mem_Iio.mpr hk'.1) hpow
  rw [Set.ncard_eq_toFinset_card' S, hST, Finset.card_biUnion hdisj]
  by_cases hc : IsConj σ τ
  · rw [if_pos hc]
    have hterm : ∀ k ∈ K, (T k).card = Nat.card (Subgroup.centralizer ({σ} : Set G)) := by
      intro k hk
      simp only [hK, Finset.mem_filter, Finset.mem_range] at hk
      have hk' : k.Coprime (orderOf σ) := Nat.coprime_comm.mp hk.2
      have hconj : IsConj (σ ^ k) τ := (hrat k hk').symm.trans hc
      rw [hT, card_filter_conj_eq _ _ hconj, centralizer_pow_eq_of_coprime σ hk',
        Nat.card_eq_fintype_card]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, hKcard]
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun k hk => ?_
    simp only [hK, Finset.mem_filter, Finset.mem_range] at hk
    have hk' : k.Coprime (orderOf σ) := Nat.coprime_comm.mp hk.2
    have hnc : ¬ IsConj (σ ^ k) τ := fun h => hc ((hrat k hk').trans h)
    exact card_filter_conj_eq_zero _ _ hnc

theorem setOf_isConj_eq_orbit_conjAct (σ : G) : {τ : G | IsConj σ τ} = MulAction.orbit (ConjAct G) σ := by
  ext τ
  rw [ConjAct.orbit_eq_carrier_conjClasses, Set.mem_setOf_eq, ConjClasses.mem_carrier_iff_mk_eq,
    ConjClasses.mk_eq_mk_iff_isConj]
  exact ⟨IsConj.symm, IsConj.symm⟩

theorem card_stabilizer_conjAct_eq_card_centralizer (σ : G) :
    Nat.card (MulAction.stabilizer (ConjAct G) σ) = Nat.card (Subgroup.centralizer ({σ} : Set G)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv ConjAct.ofConjAct.toEquiv fun g => ?_)
  show g ∈ MulAction.stabilizer (ConjAct G) σ ↔ ConjAct.ofConjAct g ∈ Subgroup.centralizer ({σ} : Set G)
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_centralizer_singleton_iff, ConjAct.smul_def]
  rw [mul_inv_eq_iff_eq_mul]

theorem card_setOf_isConj_mul_card_centralizer (σ : G) :
    Nat.card {τ : G | IsConj σ τ} * Nat.card (Subgroup.centralizer ({σ} : Set G)) = Nat.card G := by
  rw [setOf_isConj_eq_orbit_conjAct, ← card_stabilizer_conjAct_eq_card_centralizer,
    Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (ConjAct G) σ),
    ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  rfl

theorem sum_moebius_mul_eq_totient (n : ℕ) (hn : 0 < n) :
    ∑ f ∈ n.divisors, (ArithmeticFunction.moebius (n / f)) * (f : ℤ) = (Nat.totient n : ℤ) := by
  have key : ∀ m > 0, ∑ x ∈ m.divisorsAntidiagonal,
      (ArithmeticFunction.moebius x.fst : ℤ) * (x.snd : ℤ) = (Nat.totient m : ℤ) := by
    refine (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℤ)
      (f := fun k => (Nat.totient k : ℤ)) (g := fun k => (k : ℤ))).mp ?_
    intro m _
    exact_mod_cast Nat.sum_totient m
  rw [← key n hn]
  exact (Nat.sum_divisorsAntidiagonal' (fun a b => (ArithmeticFunction.moebius a : ℤ) * (b : ℤ))).symm

end FltWs24.RationalClass

theorem solution {G : Type*} [Group G] (σ : G) :
    Nat.card {τ : G | IsConj σ τ} * Nat.card (Subgroup.centralizer ({σ} : Set G)) = Nat.card G :=
  FltWs24.RationalClass.card_setOf_isConj_mul_card_centralizer σ

end S_FrobeniusDensity_card_setOf_isConj_mul_card_centralizer
end P2MW
export P2MW.S_FrobeniusDensity_card_setOf_isConj_mul_card_centralizer (solution)
