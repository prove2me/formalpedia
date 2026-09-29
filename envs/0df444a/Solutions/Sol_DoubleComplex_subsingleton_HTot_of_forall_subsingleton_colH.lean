-- Prove2me | solution 1 for DoubleComplex.subsingleton_HTot_of_forall_subsingleton_colH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/953f10ba-945d-514c-a825-e657ff52a391

import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DoubleComplex_subsingleton_HTot_of_forall_subsingleton_colH

set_option autoImplicit false

universe u

namespace DoubleComplex
p2m_export "DoubleComplex" "Bounded Diag Tot dTot HTot dTot_apply_zero_succ dTot_apply_succ_zero dTot_apply_succ_succ dTot_comp_dTot colB colH"
p2m_open "DoubleComplex"

namespace Ws48ColAcyclic

variable {R : Type u} [CommRing R] (D : Bounded R)

theorem eq_zero_of_neg_one_pow_smul_eq_zero {M : Type u} [AddCommGroup M] (m : ℕ) (x : M)
    (hx : ((-1 : ℤ) ^ m) • x = 0) : x = 0 := by
  rcases neg_one_pow_eq_or ℤ m with h | h <;> rw [h] at hx <;> simpa using hx

theorem neg_one_pow_smul_neg_one_pow_smul {M : Type u} [AddCommGroup M] (m : ℕ) (x : M) :
    ((-1 : ℤ) ^ m) • (((-1 : ℤ) ^ m) • x) = x := by
  rw [smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]

open Classical in

theorem dTot_single_vert {n k q' : ℕ} (hk : k + q' = n) (w : D.C k q') (h : k + (q' + 1) = n + 1) :
    dTot D n (Pi.single (⟨(k, q'), hk⟩ : Diag n) w) ⟨(k, q' + 1), h⟩ = ((-1 : ℤ) ^ k) • D.dV k q' w := by
  cases k with
  | zero =>
    rw [dTot_apply_zero_succ, pow_zero, one_smul]
    congr 1
    exact Pi.single_eq_same _ _
  | succ k' =>
    rw [dTot_apply_succ_succ]
    have h1 : (Pi.single (⟨(k' + 1, q'), hk⟩ : Diag n) w : Tot D n) ⟨(k', q' + 1), by omega⟩ = 0 :=
      Pi.single_eq_of_ne (fun e => by
        have := congrArg (fun i : Diag n => i.1.1) e
        simp only at this
        omega) _
    have h2 : (Pi.single (⟨(k' + 1, q'), hk⟩ : Diag n) w : Tot D n) ⟨(k' + 1, q'), by omega⟩ = w :=
      Pi.single_eq_same _ _
    rw [h1, h2, map_zero, zero_add]

open Classical in

theorem dTot_single_eq_zero {n k q' : ℕ} (hk : k + q' = n) (w : D.C k q') (j : Diag (n + 1))
    (hj : j.1.1 ≤ k) (hj' : ¬ (j.1.1 = k ∧ j.1.2 = q' + 1)) :
    dTot D n (Pi.single (⟨(k, q'), hk⟩ : Diag n) w) j = 0 := by
  obtain ⟨⟨p, r⟩, hpr⟩ := j
  simp only at hj hj' hpr
  rcases p with _ | p' <;> rcases r with _ | r'
  · exfalso; omega
  · rw [dTot_apply_zero_succ]
    have e : (Pi.single (⟨(k, q'), hk⟩ : Diag n) w : Tot D n) ⟨(0, r'), by omega⟩ = 0 :=
      Pi.single_eq_of_ne (fun e => by
        have := congrArg Subtype.val e
        simp only [Prod.mk.injEq] at this
        omega) _
    rw [e, map_zero]
  · rw [dTot_apply_succ_zero]
    have e : (Pi.single (⟨(k, q'), hk⟩ : Diag n) w : Tot D n) ⟨(p', 0), by omega⟩ = 0 :=
      Pi.single_eq_of_ne (fun e => by
        have := congrArg Subtype.val e
        simp only [Prod.mk.injEq] at this
        omega) _
    rw [e, map_zero]
  · rw [dTot_apply_succ_succ]
    have e1 : (Pi.single (⟨(k, q'), hk⟩ : Diag n) w : Tot D n) ⟨(p', r' + 1), by omega⟩ = 0 :=
      Pi.single_eq_of_ne (fun e => by
        have := congrArg Subtype.val e
        simp only [Prod.mk.injEq] at this
        omega) _
    have e2 : (Pi.single (⟨(k, q'), hk⟩ : Diag n) w : Tot D n) ⟨(p' + 1, r'), by omega⟩ = 0 :=
      Pi.single_eq_of_ne (fun e => by
        have := congrArg Subtype.val e
        simp only [Prod.mk.injEq] at this
        omega) _
    rw [e1, e2, map_zero, map_zero, smul_zero, add_zero]

open Classical in

theorem stair (n : ℕ)
    (hcol0 : ∀ (p : ℕ) (z : D.C p 0), D.dV p 0 z = 0 → z = 0)
    (hcolS : ∀ (p q' : ℕ) (z : D.C p (q' + 1)), D.dV p (q' + 1) z = 0 → ∃ y, D.dV p q' y = z)
    (c : Tot D (n + 1)) (hc : dTot D (n + 1) c = 0) (k : ℕ) :
    ∃ b : Tot D n, ∀ i : Diag (n + 1), i.1.1 < k → (c - dTot D n b) i = 0 := by
  induction k with
  | zero => exact ⟨0, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨b, hb⟩ := ih
    by_cases hk : n + 1 < k
    · exact ⟨b, fun i hi => hb i (by have := i.2; omega)⟩
    obtain ⟨q, hq⟩ : ∃ q, k + q = n + 1 := ⟨n + 1 - k, by omega⟩
    have hcyc : dTot D (n + 1) (c - dTot D n b) = 0 := by
      rw [map_sub, hc, zero_sub, neg_eq_zero]
      simpa using LinearMap.congr_fun (dTot_comp_dTot D n) b
    have KV : D.dV k q ((c - dTot D n b) ⟨(k, q), hq⟩) = 0 := by
      cases k with
      | zero =>
        have e := congrFun hcyc ⟨(0, q + 1), by omega⟩
        rw [dTot_apply_zero_succ, Pi.zero_apply] at e
        exact e
      | succ k' =>
        have e := congrFun hcyc ⟨(k' + 1, q + 1), by omega⟩
        rw [dTot_apply_succ_succ, Pi.zero_apply, hb ⟨(k', q + 1), by omega⟩ (Nat.lt_succ_self _),
          map_zero, zero_add] at e
        exact eq_zero_of_neg_one_pow_smul_eq_zero _ _ e
    cases q with
    | zero =>
      refine ⟨b, fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | heq
      · exact hb i hlt
      · have hi2 : i = ⟨(k, 0), hq⟩ :=
          Subtype.ext (Prod.ext heq (by have h2 := i.2; dsimp only at h2 heq ⊢; omega))
        rw [hi2]
        exact hcol0 k _ KV
    | succ q' =>
      obtain ⟨y, hy⟩ := hcolS k q' _ KV
      refine ⟨b + Pi.single (⟨(k, q'), by omega⟩ : Diag n) (((-1 : ℤ) ^ k) • y), fun i hi => ?_⟩
      rw [map_add, ← sub_sub, Pi.sub_apply]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | heq
      · rw [hb i hlt, dTot_single_eq_zero D _ _ i hlt.le (fun h => by omega), sub_zero]
      · have hi2 : i = ⟨(k, q' + 1), hq⟩ :=
          Subtype.ext (Prod.ext heq (by have h2 := i.2; dsimp only at h2 heq ⊢; omega))
        rw [hi2, dTot_single_vert D, map_zsmul, neg_one_pow_smul_neg_one_pow_smul, hy, sub_self]

theorem subsingleton_HTot (h : ∀ p q : ℕ, Subsingleton (colH D p q)) (n : ℕ) :
    Subsingleton (HTot D n) := by
  classical
  have hcol : ∀ (p q : ℕ) (z : LinearMap.ker (D.dV p q)), z ∈ colB D p q := fun p q z =>
    (Submodule.Quotient.mk_eq_zero _).1 (Subsingleton.elim _ _)
  have hcol0 : ∀ (p : ℕ) (z : D.C p 0), D.dV p 0 z = 0 → z = 0 := fun p z hz => by
    have e := hcol p 0 ⟨z, LinearMap.mem_ker.2 hz⟩
    change _ ∈ (⊥ : Submodule R _) at e
    rw [Submodule.mem_bot] at e
    exact congrArg Subtype.val e
  have hcolS : ∀ (p q' : ℕ) (z : D.C p (q' + 1)), D.dV p (q' + 1) z = 0 → ∃ y, D.dV p q' y = z :=
    fun p q' z hz => by
    have e := hcol p (q' + 1) ⟨z, LinearMap.mem_ker.2 hz⟩
    change _ ∈ (LinearMap.range (D.dV p q')).comap (LinearMap.ker (D.dV p (q' + 1))).subtype at e
    rw [Submodule.mem_comap, LinearMap.mem_range] at e
    exact e
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  rintro ⟨c, hc⟩ -
  cases n with
  | zero =>
    change (⟨c, hc⟩ : LinearMap.ker (dTot D 0)) ∈ (⊥ : Submodule R _)
    rw [Submodule.mem_bot]
    apply Subtype.ext
    show c = 0
    funext i
    obtain ⟨⟨p, q⟩, hpq⟩ := i
    have hp : p = 0 := by simp only at hpq; omega
    have hq : q = 0 := by simp only at hpq; omega
    subst hp hq
    have e := congrFun (LinearMap.mem_ker.1 hc) ⟨(0, 1), by omega⟩
    rw [dTot_apply_zero_succ, Pi.zero_apply] at e
    exact hcol0 0 _ e
  | succ n =>
    obtain ⟨b, hb⟩ := stair D n hcol0 hcolS c (LinearMap.mem_ker.1 hc) (n + 2)
    change (⟨c, hc⟩ : LinearMap.ker (dTot D (n + 1))) ∈
      (LinearMap.range (dTot D n)).comap (LinearMap.ker (dTot D (n + 1))).subtype
    rw [Submodule.mem_comap, LinearMap.mem_range]
    refine ⟨b, ?_⟩
    show dTot D n b = c
    have e : c - dTot D n b = 0 := funext fun i => hb i (by have := i.2; omega)
    exact (sub_eq_zero.1 e).symm

end Ws48ColAcyclic

end DoubleComplex

theorem solution
    {R : Type u} [CommRing R] (D : DoubleComplex.Bounded R)
    (h : ∀ p q : ℕ, Subsingleton (DoubleComplex.colH D p q)) (n : ℕ) :
    Subsingleton (DoubleComplex.HTot D n) := by
  exact DoubleComplex.Ws48ColAcyclic.subsingleton_HTot D h n

end S_DoubleComplex_subsingleton_HTot_of_forall_subsingleton_colH
end P2MW
export P2MW.S_DoubleComplex_subsingleton_HTot_of_forall_subsingleton_colH (solution)
