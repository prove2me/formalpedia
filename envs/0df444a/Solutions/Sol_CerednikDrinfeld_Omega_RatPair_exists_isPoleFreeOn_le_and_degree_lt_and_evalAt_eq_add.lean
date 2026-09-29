-- Prove2me | solution 1 for CerednikDrinfeld.Omega.RatPair.exists_isPoleFreeOn_le_and_degree_lt_and_evalAt_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/96a2a0ad-4611-5671-a19a-0c1ab4174c68

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_RatPair_exists_isPoleFreeOn_le_and_degree_lt_and_evalAt_eq_add

set_option autoImplicit false

open CerednikDrinfeld.Omega Polynomial

theorem solution
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (Q : RatPair K) (t₀ π₀ : K) (hπ₀ : π₀ ≠ 0) :
    ∃ A B : RatPair K,
      A.IsPoleFreeOn ({z | Q.den.eval z ≠ 0} ∪ {z | Valued.v π₀ ≤ Valued.v (z - t₀)}) ∧
      A.num.degree < A.den.degree ∧
      B.IsPoleFreeOn ({z | Q.den.eval z ≠ 0} ∪ {z | Valued.v (z - t₀) < Valued.v π₀}) ∧
      ∀ z : K, Q.den.eval z ≠ 0 → Q.evalAt z = A.evalAt z + B.evalAt z := by
  classical
  by_cases hden : Q.den = 0
  · refine ⟨RatPair.const 0, RatPair.const 0, RatPair.isPoleFreeOn_const _ _, ?_,
      RatPair.isPoleFreeOn_const _ _, ?_⟩
    · show (Polynomial.C (0 : K)).degree < (1 : K[X]).degree
      rw [map_zero, degree_zero, degree_one]; exact WithBot.bot_lt_coe 0
    · intro z hz
      exact absurd (by rw [hden, eval_zero]) hz

  obtain ⟨Din, hDin⟩ : ∃ Din : K[X],
      Din = ((Q.den.roots.filter fun c => Valued.v (c - t₀) < Valued.v π₀).map fun a => X - C a).prod := ⟨_, rfl⟩
  obtain ⟨Dout, hDout⟩ : ∃ Dout : K[X],
      Dout = C Q.den.leadingCoeff *
        ((Q.den.roots.filter fun c => ¬ Valued.v (c - t₀) < Valued.v π₀).map fun a => X - C a).prod := ⟨_, rfl⟩
  have hD : Q.den = Din * Dout := by
    have h := C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree (p := Q.den))
    rw [← Multiset.filter_add_not (fun c => Valued.v (c - t₀) < Valued.v π₀) Q.den.roots, Multiset.map_add,
      Multiset.prod_add] at h
    rw [hDin, hDout]
    calc Q.den = C Q.den.leadingCoeff *
          (((Q.den.roots.filter fun c => Valued.v (c - t₀) < Valued.v π₀).map fun a => X - C a).prod *
            ((Q.den.roots.filter fun a => ¬ Valued.v (a - t₀) < Valued.v π₀).map fun a => X - C a).prod) := h.symm
      _ = _ := by ring
  have hDin_monic : Din.Monic := by rw [hDin]; exact monic_multisetProd_X_sub_C _
  have hlc : Q.den.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hden
  have evprod : ∀ (s : Multiset K) (z : K), ((s.map fun a => X - C a).prod).eval z = (s.map fun a => z - a).prod := by
    intro s z
    rw [eval_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp
  have hDin_ne : ∀ z : K, Valued.v π₀ ≤ Valued.v (z - t₀) → Din.eval z ≠ 0 := by
    intro z hz
    rw [hDin, evprod, Ne, Multiset.prod_eq_zero_iff, Multiset.mem_map]
    rintro ⟨a, ha, h0⟩
    rw [Multiset.mem_filter] at ha
    have hza : z = a := (sub_eq_zero.mp h0)
    subst hza
    exact absurd ha.2 (not_lt.mpr hz)
  have hDout_ne : ∀ z : K, Valued.v (z - t₀) < Valued.v π₀ → Dout.eval z ≠ 0 := by
    intro z hz
    rw [hDout, eval_mul, eval_C, evprod]
    refine mul_ne_zero hlc ?_
    rw [Ne, Multiset.prod_eq_zero_iff, Multiset.mem_map]
    rintro ⟨a, ha, h0⟩
    rw [Multiset.mem_filter] at ha
    have hza : z = a := (sub_eq_zero.mp h0)
    subst hza
    exact ha.2 hz
  have hD_ne : ∀ z : K, Q.den.eval z ≠ 0 → Din.eval z ≠ 0 ∧ Dout.eval z ≠ 0 := by
    intro z h
    rw [hD, eval_mul] at h
    exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩

  have hcop : IsCoprime Din Dout := by
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := K) (K := K)]
    intro a
    simp only [coe_aeval_eq_eval]
    by_cases ha : Valued.v (a - t₀) < Valued.v π₀
    · exact Or.inr (hDout_ne a ha)
    · exact Or.inl (hDin_ne a (not_lt.mp ha))
  obtain ⟨U, W, hUW⟩ := hcop
  have hρq : (Q.num * W) %ₘ Din + Din * ((Q.num * W) /ₘ Din) = Q.num * W := modByMonic_add_div _ _
  refine ⟨⟨(Q.num * W) %ₘ Din, Din⟩, ⟨Q.num * U + (Q.num * W) /ₘ Din * Dout, Dout⟩, ?_, ?_, ?_, ?_⟩
  · rintro z (hz | hz)
    · exact (hD_ne z hz).1
    · exact hDin_ne z hz
  · exact degree_modByMonic_lt _ hDin_monic
  · rintro z (hz | hz)
    · exact (hD_ne z hz).2
    · exact hDout_ne z hz
  · intro z hz
    obtain ⟨h1, h2⟩ := hD_ne z hz
    have key : (Q.num * W) %ₘ Din * Dout + (Q.num * U + (Q.num * W) /ₘ Din * Dout) * Din = Q.num := by
      calc (Q.num * W) %ₘ Din * Dout + (Q.num * U + (Q.num * W) /ₘ Din * Dout) * Din
          = Dout * ((Q.num * W) %ₘ Din + Din * ((Q.num * W) /ₘ Din)) + Q.num * (U * Din) := by ring
        _ = Dout * (Q.num * W) + Q.num * (U * Din) := by rw [hρq]
        _ = Q.num * (U * Din + W * Dout) := by ring
        _ = Q.num := by rw [hUW, mul_one]
    have keyz := congrArg (eval z) key
    simp only [eval_add, eval_mul] at keyz
    have hdz : Q.den.eval z = Din.eval z * Dout.eval z := by rw [hD, eval_mul]
    simp only [RatPair.evalAt]
    rw [hdz, div_add_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) (mul_ne_zero h1 h2)]
    simp only [eval_add, eval_mul]
    linear_combination (-(Din.eval z * Dout.eval z)) * keyz

end S_CerednikDrinfeld_Omega_RatPair_exists_isPoleFreeOn_le_and_degree_lt_and_evalAt_eq_add
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_RatPair_exists_isPoleFreeOn_le_and_degree_lt_and_evalAt_eq_add (solution)
