-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.charP_residue_and_forall_exists_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/5501b2b0-9d40-5160-8b40-1c8fb3c22b9b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_charP_residue_and_forall_exists_pow_eq

set_option autoImplicit false

theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π}) :
    CharP (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) r ∧
      ∀ a : Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}, ∃ b : Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}, b ^ r = a := by
  classical
  haveI hmaxI : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal := hOnr_max
  haveI : Nontrivial (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) :=
    Ideal.Quotient.nontrivial_iff.mpr hOnr_max.ne_top
  refine ⟨?_, ?_⟩
  · refine (CharP.charP_iff_prime_eq_zero Fact.out).mpr ?_
    have hr : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := by
      rw [← hunr]; exact Ideal.subset_span rfl
    have hmem : ((r : ℕ) : Onr) ∈ Ideal.span {algebraMap 𝒪 Onr π} := by
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hr
      have : algebraMap 𝒪 Onr (c * π) = ((r : ℕ) : Onr) := by rw [hc, map_natCast]
      rw [← this, map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})), Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  · intro a
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hr0 : r ≠ 0 := (Fact.out : r.Prime).ne_zero
    have hmonic : (Polynomial.X ^ r - Polynomial.C x : Polynomial Onr).Monic :=
      Polynomial.monic_X_pow_sub_C x hr0
    have hdeg : 0 < (Polynomial.X ^ r - Polynomial.C x : Polynomial Onr).natDegree := by
      rw [Polynomial.natDegree_X_pow_sub_C]; exact (Fact.out : r.Prime).pos
    obtain ⟨y, hy⟩ := hOnr_closed _ hmonic hdeg
    refine ⟨Ideal.Quotient.mk _ y, ?_⟩
    rw [← map_pow, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    simpa [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] using hy

end S_CerednikDrinfeld_FormalOmega_charP_residue_and_forall_exists_pow_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_charP_residue_and_forall_exists_pow_eq (solution)
