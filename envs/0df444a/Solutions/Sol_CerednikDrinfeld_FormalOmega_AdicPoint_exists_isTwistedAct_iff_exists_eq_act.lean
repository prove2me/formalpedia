-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.AdicPoint.exists_isTwistedAct_iff_exists_eq_act
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/90a4d671-1bf2-5763-94ab-8becb9e1d4a7

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Theorems.Thm_CerednikDrinfeld_FormalOmega_Omega_action_scalarGL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_exists_isTwistedAct_iff_exists_eq_act

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

namespace G7c13

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable (B : Type) [CommRing B] [Algebra 𝒪 B]

theorem isPullback_inv_iff (g : Matrix.GeneralLinearGroup (Fin 2) K) (d d' : DeligneDatum (K := K) π B) :
    DeligneDatum.IsPullback (K := K) (π := π) B g⁻¹ d d' ↔ d' = (Omega.action K π).act B g d := by
  constructor
  · intro h
    exact DeligneDatum.ext' (funext fun M => h M)
  · intro h M
    rw [h]
    rfl

theorem act_zpow_eq_self (z : Matrix.GeneralLinearGroup (Fin 2) K) (d : DeligneDatum (K := K) π B)
    (hz : (Omega.action K π).act B z d = d) (j : ℤ) : (Omega.action K π).act B (z ^ j) d = d := by
  have hnat : ∀ n : ℕ, (Omega.action K π).act B (z ^ n) d = d := by
    intro n
    induction n with
    | zero => rw [pow_zero]; exact (Omega.action K π).act_one B d
    | succ n ih => rw [pow_succ, (Omega.action K π).act_mul, hz, ih]
  rcases Int.eq_nat_or_neg j with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast]; exact hnat n
  · rw [zpow_neg, zpow_natCast]
    conv_lhs => rw [← hnat n]
    rw [← (Omega.action K π).act_mul, inv_mul_cancel, (Omega.action K π).act_one]

end G7c13

open G7c13 in
theorem solution

    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)

    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ : Subgroup G)
    (hcent : ∃ z ∈ Γ, ∃ c : K₀, ((σ z : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = c • (1 : Matrix (Fin 2) (Fin 2) K₀) ∧
      vdet (σ z) = Multiplicative.ofAdd (2 : ℤ))
    (hodd : ∃ w ∈ Γ, vdet (σ w) = Multiplicative.ofAdd (1 : ℤ))
    (Γ' : Subgroup G) (hΓ' : ∀ x : G, x ∈ Γ' ↔ x ∈ Γ ∧ Even (Multiplicative.toAdd (vdet (σ x))))

    (ρ : G →* PGL(2, K₀)) (hρ : ∀ g : G, ρ g = Matrix.ProjGenLinGroup.mk (σ g))
    (hdisc : ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, Set.Finite {g : PGL(2, K₀) | g ∈ Γ'.map ρ ∧ g • v = v})
    (hcocpt : ∃ S : Finset (LT.LatticeTree.Vertex 𝒪 K₀), ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, ∃ g ∈ Γ'.map ρ, g • v ∈ S)

    (R : Type) [CommRing R] [Algebra 𝒪 R] (hR : Nontrivial (modPow π R 0)) (ψ₀ : Onr →ₐ[𝒪] R)
    (x x' : AdicPoint K₀ π R) :
    (∃ γ ∈ Γ, ∀ n : ℕ, OmegaNr.IsTwistedAct π Onr Fr vdet (modPow π R n) (σ γ)
        (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x.pt n) (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x'.pt n)) ↔
      ∃ γ' ∈ Γ', x' = x.act (σ γ') := by
  classical

  have frobTwist_zero : ∀ {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B), frobTwist Onr Fr 0 ψ = ψ := by
    intro B _ _ ψ
    apply AlgHom.ext
    intro y
    show ψ ((Fr ^ (0 : ℤ)) y) = ψ y
    rw [zpow_zero, AlgEquiv.one_apply]

  obtain ⟨z, hzΓ, c, hzc, hzv⟩ := hcent
  have hc : c ≠ 0 := by
    intro hc0
    have h1 : ((σ z : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = 0 := by rw [hzc, hc0, zero_smul]
    have h2 := (σ z).mul_inv
    rw [h1, zero_mul] at h2
    exact zero_ne_one h2
  have hzs : σ z = LT.LatticeTree.scalarGL (Units.mk0 c hc) := Units.ext (by rw [hzc]; rfl)
  have hact_z : ∀ (n : ℕ) (d : DeligneDatum (K := K₀) π (modPow π R n)),
      (Omega.action K₀ π).act (modPow π R n) (σ z) d = d := fun n d => by
    rw [hzs]; exact CerednikDrinfeld.FormalOmega.Omega.action_scalarGL π (modPow π R n) _ d
  constructor
  ·
    rintro ⟨γ, hγ, hall⟩
    by_cases hv : Multiplicative.toAdd (vdet (σ γ)) = 0
    · refine ⟨γ, (hΓ' γ).2 ⟨hγ, by rw [hv]; exact ⟨0, rfl⟩⟩, ?_⟩
      apply AdicPoint.ext'
      funext n
      have h := (hall n).2
      rw [isPullback_inv_iff] at h
      exact h
    · exfalso

      let B0 : Type := modPow π R 0
      let ψ : Onr →ₐ[𝒪] B0 := (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)})).comp ψ₀
      have hψ : ψ = frobTwist Onr Fr (-Multiplicative.toAdd (vdet (σ γ))) ψ := (hall 0).1
      set m : ℤ := Multiplicative.toAdd (vdet (σ γ)) with hm
      have hm0 : m ≠ 0 := hv

      have hfix : ∀ x : Onr, ψ ((Fr ^ (-m)) x) = ψ x := fun x => by
        have h := congrArg (fun f : Onr →ₐ[𝒪] B0 => f x) hψ
        exact h.symm
      have hfix' : ∀ x : Onr, ψ ((Fr ^ m) x) = ψ x := fun x => by
        rw [← hfix ((Fr ^ m) x), ← AlgEquiv.mul_apply, zpow_neg, inv_mul_cancel, AlgEquiv.one_apply]

      set n : ℕ := m.natAbs with hn
      have hn0 : 0 < n := Int.natAbs_pos.mpr hm0
      have hfixn : ∀ x : Onr, ψ ((Fr ^ n) x) = ψ x := by
        intro x
        rw [← zpow_natCast]
        rcases Int.natAbs_eq_iff.mp hn.symm with h | h
        · have h2 := hfix' x
          rwa [h] at h2
        · have h2 := hfix x
          rwa [show -m = ((n : ℕ) : ℤ) by omega] at h2
      haveI : Nontrivial Onr := ⟨⟨0, 1, fun h => hOnr_max.ne_top
        ((Ideal.eq_top_iff_one _).2 (h ▸ (Ideal.span {algebraMap 𝒪 Onr π}).zero_mem))⟩⟩

      set 𝔪 : Ideal Onr := Ideal.span {algebraMap 𝒪 Onr π} with h𝔪
      have hcong : ∀ (k : ℕ) (x : Onr),
          Ideal.Quotient.mk 𝔪 ((Fr ^ k) x) = Ideal.Quotient.mk 𝔪 x ^ (r ^ k) := by
        intro k
        induction k with
        | zero => intro x; rw [pow_zero, pow_zero, pow_one, AlgEquiv.one_apply]
        | succ k ih =>
          intro x
          rw [pow_succ', AlgEquiv.mul_apply, pow_succ, pow_mul, ← ih]
          have h := hFr ((Fr ^ k) x)
          rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem] at h
          rw [h, map_pow]

      have hrn : 2 ≤ r ^ n := by
        calc 2 ≤ r := (Fact.out : r.Prime).two_le
          _ = r ^ 1 := (pow_one r).symm
          _ ≤ r ^ n := Nat.pow_le_pow_right (Fact.out : r.Prime).pos hn0
      have hdeglt' : (-(Polynomial.X : Polynomial Onr) + 1).natDegree < r ^ n :=
        calc (-(Polynomial.X : Polynomial Onr) + 1).natDegree ≤ 1 := by
              refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
              · rw [Polynomial.natDegree_neg]; exact Polynomial.natDegree_X_le
              · rw [Polynomial.natDegree_one]; exact zero_le_one
          _ < r ^ n := hrn
      have hdeglt : (-(Polynomial.X : Polynomial Onr) + 1).natDegree < ((Polynomial.X : Polynomial Onr) ^ (r ^ n)).natDegree := by
        rw [Polynomial.natDegree_X_pow]; exact hdeglt'
      have hmonic : ((Polynomial.X : Polynomial Onr) ^ (r ^ n) + (-Polynomial.X + 1)).Monic :=
        Polynomial.monic_X_pow_add (Polynomial.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.2 hdeglt'))
      have hdeg : 0 < ((Polynomial.X : Polynomial Onr) ^ (r ^ n) + (-Polynomial.X + 1)).natDegree := by
        rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hdeglt, Polynomial.natDegree_X_pow]; omega
      obtain ⟨ζ, hζ⟩ := hOnr_closed _ hmonic hdeg
      have hζ' : Ideal.Quotient.mk 𝔪 ζ ^ (r ^ n) - Ideal.Quotient.mk 𝔪 ζ + 1 = 0 := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_pow,
          Polynomial.eval_neg, Polynomial.eval_X, Polynomial.eval_one, map_add, map_add, map_pow, map_neg, map_one] at hζ
        linear_combination hζ

      have hu : (Fr ^ n) ζ - ζ ∉ 𝔪 := by
        intro hmem
        rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem, hcong] at hmem
        rw [hmem, sub_self, zero_add] at hζ'
        exact hOnr_max.ne_top ((Ideal.eq_top_iff_one 𝔪).2
          (Ideal.Quotient.eq_zero_iff_mem.mp ((map_one (Ideal.Quotient.mk 𝔪)).trans hζ')))
      haveI : 𝔪.IsMaximal := hOnr_max
      haveI : IsAdicComplete 𝔪 Onr := hOnr_complete
      haveI : IsLocalRing Onr := isLocalRing_of_isAdicComplete_maximal 𝔪
      have hunit : IsUnit ((Fr ^ n) ζ - ζ) := by
        rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.eq_maximalIdeal hOnr_max]; exact hu
      have hψu : ψ ((Fr ^ n) ζ - ζ) = 0 := by rw [map_sub, hfixn, sub_self]
      have hB : Subsingleton B0 := by
        have h0 : IsUnit (0 : B0) := by rw [← hψu]; exact hunit.map ψ
        exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp h0)
      haveI := hR
      exact false_of_nontrivial_of_subsingleton B0
  ·
    rintro ⟨γ', hγ', rfl⟩
    obtain ⟨hγ'Γ, ⟨k, hk⟩⟩ := (hΓ' γ').1 hγ'
    refine ⟨γ' * z ^ (-k), Γ.mul_mem hγ'Γ (Γ.zpow_mem hzΓ _), fun n => ⟨?_, ?_⟩⟩
    · have h0 : Multiplicative.toAdd (vdet (σ (γ' * z ^ (-k)))) = 0 := by
        rw [map_mul, map_mul, map_zpow, map_zpow, toAdd_mul, toAdd_zpow, hzv, toAdd_ofAdd, hk, smul_eq_mul]; ring
      show _ = frobTwist Onr Fr (-Multiplicative.toAdd (vdet (σ (γ' * z ^ (-k))))) _
      rw [h0, neg_zero, frobTwist_zero]
    · rw [isPullback_inv_iff]
      show (x.act (σ γ')).pt n = (Omega.action K₀ π).act (modPow π R n) (σ (γ' * z ^ (-k))) (x.pt n)
      rw [map_mul, (Omega.action K₀ π).act_mul, map_zpow, act_zpow_eq_self π (modPow π R n) (σ z) (x.pt n) (hact_z n (x.pt n))]
      rfl

end S_CerednikDrinfeld_FormalOmega_AdicPoint_exists_isTwistedAct_iff_exists_eq_act
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_exists_isTwistedAct_iff_exists_eq_act (solution)
