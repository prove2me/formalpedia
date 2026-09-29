-- Prove2me | solution 1 for CerednikDrinfeld.not_dvd_natCard_of_le_map_quaternion_units_of_prime_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/ccc0cb79-264d-50ef-a0e0-8b4f622ef231

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_not_dvd_natCard_of_le_map_quaternion_units_of_prime_of_five_le

set_option autoImplicit false

open scoped MatrixGroups Quaternion
open Polynomial

namespace CerednikDrinfeld
namespace TorsionOrderAux

theorem not_dvd_X_pow_sub_C {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {a : ℚ} (ha : a ≠ 0)
    {q : ℚ[X]} (hq : q.Monic) (hq2 : q.natDegree = 2) : ¬ q ∣ X ^ p - C a := by
  intro hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  have hq0 : q ≠ 0 := hq.ne_zero
  by_cases hpow : ∃ d : ℚ, d ^ p = a
  · obtain ⟨d, rfl⟩ := hpow
    have hd : d ≠ 0 := by
      rintro rfl
      exact ha (zero_pow hp.ne_zero)
    have hpodd : Odd p := hp.odd_of_ne_two (by omega)

    have hroot_eq : ∀ e : ℚ, q.IsRoot e → e = d := by
      intro e he
      have h1 : (X ^ p - C (d ^ p) : ℚ[X]).IsRoot e := he.dvd hdvd
      have h2 : e ^ p = d ^ p := by
        simpa [IsRoot, sub_eq_zero] using h1
      exact (Odd.strictMono_pow hpodd).injective h2
    by_cases hirr : Irreducible q
    ·
      haveI : Fact (Irreducible q) := ⟨hirr⟩
      have hfr : Module.finrank ℚ (AdjoinRoot q) = 2 := by
        rw [(AdjoinRoot.powerBasis hq0).finrank, AdjoinRoot.powerBasis_dim, hq2]
      set w : AdjoinRoot q := AdjoinRoot.root q with hw_def
      have hw : w ^ p = algebraMap ℚ (AdjoinRoot q) (d ^ p) := by
        have h0 : AdjoinRoot.mk q (X ^ p - C (d ^ p)) = 0 := AdjoinRoot.mk_eq_zero.2 hdvd
        rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h0
        rw [h0]; rfl
      have hdL : algebraMap ℚ (AdjoinRoot q) d ≠ 0 := by
        rw [Ne, map_eq_zero_iff _ (algebraMap ℚ (AdjoinRoot q)).injective]; exact hd
      set u : AdjoinRoot q := w * (algebraMap ℚ (AdjoinRoot q) d)⁻¹ with hu_def
      have hup : u ^ p = 1 := by
        rw [hu_def, mul_pow, hw, inv_pow, ← map_pow, mul_inv_cancel₀]
        rw [Ne, map_eq_zero_iff _ (algebraMap ℚ (AdjoinRoot q)).injective]; exact pow_ne_zero _ hd
      have hu1 : u ≠ 1 := by
        intro h1
        have hw' : w = algebraMap ℚ (AdjoinRoot q) d := by
          rw [hu_def] at h1
          exact (mul_inv_eq_one₀ hdL).1 h1
        have hqd : q.IsRoot d := by
          have h0 : aeval w q = 0 := by
            rw [hw_def]; exact (AdjoinRoot.aeval_eq (f := q) q).trans AdjoinRoot.mk_self
          rw [hw', aeval_algebraMap_apply, map_eq_zero_iff _ (algebraMap ℚ (AdjoinRoot q)).injective] at h0
          simpa using h0
        have hroots : q.roots = 0 :=
          (irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)).1 hirr
        have : d ∈ q.roots := (mem_roots hq0).2 hqd
        rw [hroots] at this
        simp at this
      have hprim : IsPrimitiveRoot u p := by
        have ho : orderOf u = p := orderOf_eq_prime hup hu1
        rw [← ho]; exact IsPrimitiveRoot.orderOf u
      have hmin : cyclotomic p ℚ = minpoly ℚ u := cyclotomic_eq_minpoly_rat hprim hp.pos
      have hle : (minpoly ℚ u).natDegree ≤ 2 := hfr ▸ minpoly.natDegree_le u
      rw [← hmin, natDegree_cyclotomic, Nat.totient_prime hp] at hle
      omega
    ·
      have hroots : q.roots ≠ 0 := fun h0 =>
        hirr ((irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)).2 h0)
      obtain ⟨e, he⟩ := Multiset.exists_mem_of_ne_zero hroots
      have he' : q.IsRoot e := (mem_roots hq0).1 he
      have hed : e = d := hroot_eq e he'
      rw [hed] at he'
      obtain ⟨r, hr⟩ := dvd_iff_isRoot.2 he'
      have hrm : r.Monic := by
        have : (X - C d : ℚ[X]).Monic := monic_X_sub_C d
        exact Monic.of_mul_monic_left this (hr ▸ hq)
      have hr1 : r.natDegree = 1 := by
        have := (monic_X_sub_C d).natDegree_mul hrm
        rw [← hr, hq2, natDegree_X_sub_C] at this
        omega

      have hrX : r = X + C (r.coeff 0) := hrm.eq_X_add_C hr1
      have hroot : q.IsRoot (-(r.coeff 0)) := by
        rw [hr, IsRoot, eval_mul, hrX]; simp
      have hcd : -(r.coeff 0) = d := hroot_eq _ hroot
      have hr_eq : r = X - C d := by
        rw [hrX, ← hcd, C_neg, sub_neg_eq_add]
      have hqsq : q = (X - C d) * (X - C d) := by rw [hr, hr_eq]
      have hsq : (X - C d) * (X - C d) ∣ (X ^ p - C (d ^ p) : ℚ[X]) := hqsq ▸ hdvd
      have hsep : (X ^ p - C (d ^ p) : ℚ[X]).Separable :=
        separable_X_pow_sub_C (d ^ p) (by exact_mod_cast hp.ne_zero) (pow_ne_zero _ hd)
      have hunit : IsUnit (X - C d : ℚ[X]) := hsep.squarefree _ hsq
      have := natDegree_eq_zero_of_isUnit hunit
      rw [natDegree_X_sub_C] at this
      exact one_ne_zero this
  · push Not at hpow
    have hirr : Irreducible (X ^ p - C a : ℚ[X]) := X_pow_sub_C_irreducible_of_prime hp hpow
    obtain ⟨s, hs⟩ := hdvd
    rcases hirr.isUnit_or_isUnit hs with hu | hu
    · have := natDegree_eq_zero_of_isUnit hu; omega
    · have h1 := natDegree_eq_zero_of_isUnit hu
      have h2 : (X ^ p - C a : ℚ[X]).natDegree = p := natDegree_X_pow_sub_C
      rw [hs, natDegree_mul hq0 hu.ne_zero, hq2, h1] at h2
      omega

end CerednikDrinfeld.TorsionOrderAux

namespace CerednikDrinfeld
namespace TorsionOrderAux

theorem exists_eq_smul_one_of_pow_eq_smul_one
    (K₀ : Type) [Field K₀] [Algebra ℚ K₀] {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (Y : Matrix (Fin 2) (Fin 2) K₀) (t n : ℚ)
    (hY : Y * Y = algebraMap ℚ K₀ t • Y - algebraMap ℚ K₀ n • 1)
    (c : K₀) (hc0 : c ≠ 0) (hc : Y ^ p = c • 1) :
    ∃ e : K₀, Y = e • 1 := by
  by_contra hns
  push Not at hns

  have hind : ∀ u v : K₀, u • (1 : Matrix (Fin 2) (Fin 2) K₀) + v • Y = 0 → u = 0 ∧ v = 0 := by
    intro u v h
    by_cases hv : v = 0
    · subst hv
      simp only [zero_smul, add_zero] at h
      refine ⟨?_, rfl⟩
      rcases smul_eq_zero.1 h with h0 | h0
      · exact h0
      · exact absurd h0 one_ne_zero
    · exfalso
      apply hns (-(v⁻¹ * u))
      have h' : v • Y = -(u • (1 : Matrix (Fin 2) (Fin 2) K₀)) := eq_neg_of_add_eq_zero_right h
      calc Y = v⁻¹ • (v • Y) := by rw [smul_smul, inv_mul_cancel₀ hv, one_smul]
        _ = -(v⁻¹ * u) • (1 : Matrix (Fin 2) (Fin 2) K₀) := by rw [h', smul_neg, smul_smul, neg_smul]
  have hAM : ∀ r : ℚ, algebraMap ℚ (Matrix (Fin 2) (Fin 2) K₀) r =
      (algebraMap ℚ K₀ r) • (1 : Matrix (Fin 2) (Fin 2) K₀) := by
    intro r; rw [Algebra.algebraMap_eq_smul_one, algebraMap_smul]

  set q : ℚ[X] := X ^ 2 - C t * X + C n with hq_def
  have hqm : q.Monic := by rw [hq_def]; monicity!
  have hq2 : q.natDegree = 2 := by rw [hq_def]; compute_degree!
  have hq_eval : aeval Y q = 0 := by
    rw [hq_def, map_add, map_sub, map_mul, aeval_C, map_pow, aeval_X, aeval_C, hAM, hAM, pow_two, hY,
      smul_one_mul]
    abel

  obtain ⟨r, hr_def⟩ : ∃ r : ℚ[X], r = (X ^ p : ℚ[X]) %ₘ q := ⟨_, rfl⟩
  have hdiv : r + q * ((X ^ p : ℚ[X]) /ₘ q) = X ^ p := by
    rw [hr_def]; exact modByMonic_add_div (X ^ p : ℚ[X]) q
  have hr1 : r.natDegree ≤ 1 := by
    have h : r.natDegree < q.natDegree := by
      rw [hr_def]
      exact natDegree_modByMonic_lt (X ^ p : ℚ[X]) hqm (by
        intro h1; rw [h1, natDegree_one] at hq2; exact absurd hq2 (by norm_num))
    rw [hq2] at h
    omega
  have hr : r = C (r.coeff 1) * X + C (r.coeff 0) := eq_X_add_C_of_natDegree_le_one hr1
  have hevr : aeval Y r = (algebraMap ℚ K₀ (r.coeff 0)) • (1 : Matrix (Fin 2) (Fin 2) K₀)
      + (algebraMap ℚ K₀ (r.coeff 1)) • Y := by
    conv_lhs => rw [hr]
    rw [map_add, map_mul, aeval_C, aeval_X, aeval_C, hAM, hAM, smul_one_mul, add_comm]
  have hevp : aeval Y (X ^ p : ℚ[X]) = aeval Y r := by
    conv_lhs => rw [← hdiv]
    rw [map_add, map_mul, hq_eval, zero_mul, add_zero]
  rw [map_pow, aeval_X, hc, hevr] at hevp

  have hcmp := hind (algebraMap ℚ K₀ (r.coeff 0) - c) (algebraMap ℚ K₀ (r.coeff 1)) (by
    rw [sub_smul, sub_add_eq_add_sub, ← hevp, sub_self])
  have hα : algebraMap ℚ K₀ (r.coeff 0) = c := sub_eq_zero.1 hcmp.1
  have hβ : r.coeff 1 = 0 := by
    have := hcmp.2
    rwa [map_eq_zero_iff _ (algebraMap ℚ K₀).injective] at this
  have hα0 : r.coeff 0 ≠ 0 := by
    intro h0; rw [h0, map_zero] at hα; exact hc0 hα.symm
  have hrC : r = C (r.coeff 0) := by
    conv_lhs => rw [hr]
    rw [hβ, C_0, zero_mul, zero_add]
  have hdvd : q ∣ X ^ p - C (r.coeff 0) := by
    refine ⟨(X ^ p : ℚ[X]) /ₘ q, ?_⟩
    rw [← hrC]
    linear_combination (-1 : ℚ[X]) * hdiv
  exact not_dvd_X_pow_sub_C hp h5 hα0 hqm hq2 hdvd

theorem coe_scalar (K₀ : Type) [Field K₀] (u : K₀ˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) =
      (u : K₀) • (1 : Matrix (Fin 2) (Fin 2) K₀) := by
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_one_eq_diagonal]

end CerednikDrinfeld.TorsionOrderAux

open CerednikDrinfeld.TorsionOrderAux in
theorem solution
    (K₀ : Type) [Field K₀] [Algebra ℚ K₀]
    {a b : ℚ} (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀)
    (ρ : (ℍ[ℚ, a, b])ˣ →* PGL(2, K₀))
    (hρ : ∀ x : (ℍ[ℚ, a, b])ˣ, ρ x = Matrix.ProjGenLinGroup.mk
      (Units.map (ι : ℍ[ℚ, a, b] →* Matrix (Fin 2) (Fin 2) K₀) x)) :
    ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ H : Subgroup PGL(2, K₀),
      H ≤ (⊤ : Subgroup (ℍ[ℚ, a, b])ˣ).map ρ → Finite H → ¬ p ∣ Nat.card H := by
  intro p hp h5 H hH hfin hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite H := hfin
  obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' (G := H) p hdvd
  have hord : orderOf (h : PGL(2, K₀)) = p := by rw [Subgroup.orderOf_coe]; exact hh
  obtain ⟨x, -, hx⟩ := Subgroup.mem_map.1 (hH h.2)
  rw [← hx, hρ] at hord
  set y : GL (Fin 2) K₀ := Units.map (ι : ℍ[ℚ, a, b] →* Matrix (Fin 2) (Fin 2) K₀) x with hy_def

  have hp1 : Matrix.ProjGenLinGroup.mk (y ^ p) = 1 := by
    rw [map_pow, ← hord, pow_orderOf_eq_one]
  rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hp1
  obtain ⟨u, hu⟩ := hp1

  have hne1 : Matrix.ProjGenLinGroup.mk y ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hord; omega

  set Y : Matrix (Fin 2) (Fin 2) K₀ := ι (x : ℍ[ℚ, a, b]) with hY_def
  have hYval : (y : Matrix (Fin 2) (Fin 2) K₀) = Y := by rw [hy_def, Units.coe_map]; rfl

  set t : ℚ := 2 * (x : ℍ[ℚ, a, b]).re + 0 * (x : ℍ[ℚ, a, b]).imI with ht_def
  set n : ℚ := (star (x : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b])).re with hn_def
  have hx1 : (x : ℍ[ℚ, a, b]) + star (x : ℍ[ℚ, a, b]) = (t : ℍ[ℚ, a, b]) :=
    QuaternionAlgebra.self_add_star' (x : ℍ[ℚ, a, b])
  have hx2 : star (x : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) = (n : ℍ[ℚ, a, b]) :=
    QuaternionAlgebra.star_mul_eq_coe (x : ℍ[ℚ, a, b])
  have hstar : star (x : ℍ[ℚ, a, b]) = (t : ℍ[ℚ, a, b]) - x := eq_sub_of_add_eq' hx1
  have hxx : (x : ℍ[ℚ, a, b]) * x = (t : ℍ[ℚ, a, b]) * x - (n : ℍ[ℚ, a, b]) := by
    rw [hstar, sub_mul] at hx2
    rw [← hx2]; abel
  have hY : Y * Y = algebraMap ℚ K₀ t • Y - algebraMap ℚ K₀ n • 1 := by
    have := congrArg ι hxx
    rw [map_mul, map_sub, map_mul] at this
    rw [hY_def, this]
    have hc : ∀ r : ℚ, ι (r : ℍ[ℚ, a, b]) = (algebraMap ℚ K₀ r) • (1 : Matrix (Fin 2) (Fin 2) K₀) := by
      intro r
      rw [← QuaternionAlgebra.coe_algebraMap]
      show ι (algebraMap ℚ ℍ[ℚ, a, b] r) = _
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, algebraMap_smul]
    rw [hc, hc, smul_one_mul]
  have hYp : Y ^ p = (u : K₀) • 1 := by
    rw [← hYval, ← Units.val_pow_eq_pow_val, ← hu, coe_scalar]
  obtain ⟨e, he⟩ := exists_eq_smul_one_of_pow_eq_smul_one K₀ hp h5 Y t n hY (u : K₀) u.ne_zero hYp
  have he0 : e ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at he
    have : IsUnit Y := hYval ▸ y.isUnit
    rw [he] at this
    exact not_isUnit_zero this
  apply hne1
  rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar]
  refine ⟨Units.mk0 e he0, ?_⟩
  ext1
  rw [coe_scalar, hYval, he]
  rfl

end S_CerednikDrinfeld_not_dvd_natCard_of_le_map_quaternion_units_of_prime_of_five_le
end P2MW
export P2MW.S_CerednikDrinfeld_not_dvd_natCard_of_le_map_quaternion_units_of_prime_of_five_le (solution)
