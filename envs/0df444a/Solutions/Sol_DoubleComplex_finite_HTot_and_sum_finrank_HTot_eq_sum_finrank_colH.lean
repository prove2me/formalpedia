-- Prove2me | solution 1 for DoubleComplex.finite_HTot_and_sum_finrank_HTot_eq_sum_finrank_colH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/09c1ac75-a6c8-5ba8-862c-233c8cd34b07

import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Theorems.Thm_DoubleComplex_finite_HTot_and_sum_finrank_HTot_eq_sub_of_rowShift
import Theorems.Thm_DoubleComplex_nonempty_HTot_transpose_equiv
import Theorems.Thm_DoubleComplex_subsingleton_HTot_of_forall_subsingleton_colH
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DoubleComplex_finite_HTot_and_sum_finrank_HTot_eq_sum_finrank_colH

set_option autoImplicit false

universe u

namespace ChiCol

open DoubleComplex

variable {k : Type u} [Field k]

def up (D : Bounded k) : Bounded k :=
  { C := fun p q => D.C p (q + 1), dH := fun p q => D.dH p (q + 1), dV := fun p q => D.dV p (q + 1),
    dH_sq := fun p q => D.dH_sq p (q + 1), dV_sq := fun p q => D.dV_sq p (q + 1),
    dHV_comm := fun p q => D.dHV_comm p (q + 1), N := D.N,
    hBound := fun p q h => D.hBound p (q + 1) (h.imp id Nat.le_succ_of_le) }

theorem colH_subsingleton (X : Bounded k) (p q : ℕ) (h : Subsingleton (X.C p q)) :
    Subsingleton (colH X p q) := by
  haveI : Subsingleton (LinearMap.ker (X.dV p q)) := inferInstance
  exact (Submodule.mkQ_surjective (colB X p q)).subsingleton

theorem finrank_colH_eq_zero (X : Bounded k) (p q : ℕ) (h : Subsingleton (X.C p q)) :
    (Module.finrank k (colH X p q) : ℤ) = 0 := by
  haveI := colH_subsingleton X p q h
  rw [Module.finrank_zero_of_subsingleton, Nat.cast_zero]

theorem row_form (m : ℕ) : ∀ (D : Bounded k), (∀ p q, m ≤ q → Subsingleton (D.C p q)) →
    (∀ q p, Module.Finite k (colH (transpose D) q p)) →
    (∀ n, Module.Finite k (HTot D n)) ∧
      ∑ n ∈ Finset.range (2 * D.N), (-1 : ℤ) ^ n * (Module.finrank k (HTot D n) : ℤ) =
        ∑ q ∈ Finset.range D.N, ∑ p ∈ Finset.range D.N,
          (-1 : ℤ) ^ (q + p) * (Module.finrank k (colH (transpose D) q p) : ℤ) := by
  induction m with
  | zero =>
    intro D hz hfin
    have hC : ∀ p q, Subsingleton (D.C p q) := fun p q => hz p q (Nat.zero_le q)
    have hcolH : ∀ p q, Subsingleton (colH D p q) := fun p q => colH_subsingleton D p q (hC p q)
    have hHT : ∀ n, Subsingleton (HTot D n) := DoubleComplex.subsingleton_HTot_of_forall_subsingleton_colH D hcolH
    refine ⟨fun n => by haveI := hHT n; infer_instance, ?_⟩
    rw [Finset.sum_eq_zero (fun n _ => by
      haveI := hHT n; rw [Module.finrank_zero_of_subsingleton, Nat.cast_zero, mul_zero])]
    symm
    refine Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun p _ => ?_
    rw [finrank_colH_eq_zero (transpose D) q p (hC p q), mul_zero]
  | succ m ih =>
    intro D hz hfin
    have hupz : ∀ p q, m ≤ q → Subsingleton ((up D).C p q) := fun p q h => hz p (q + 1) (by omega)
    have hupfin : ∀ q p, Module.Finite k (colH (transpose (up D)) q p) := fun q p => hfin (q + 1) p
    obtain ⟨hupHT, hupsum⟩ := ih (up D) hupz hupfin
    obtain ⟨hHT, hpeel⟩ :=
      DoubleComplex.finite_HTot_and_sum_finrank_HTot_eq_sub_of_rowShift D hupHT (fun p => hfin 0 p)
    refine ⟨hHT, ?_⟩

    have hpeel' : ∑ n ∈ Finset.range (2 * D.N), (-1 : ℤ) ^ n * (Module.finrank k (HTot D n) : ℤ) =
        ∑ p ∈ Finset.range (2 * D.N), (-1 : ℤ) ^ p * (Module.finrank k (colH (transpose D) 0 p) : ℤ) -
          ∑ n ∈ Finset.range (2 * (up D).N), (-1 : ℤ) ^ n * (Module.finrank k (HTot (up D) n) : ℤ) := hpeel
    rw [hpeel', hupsum]

    have hre : ∀ q p, (Module.finrank k (colH (transpose (up D)) q p) : ℤ) =
        Module.finrank k (colH (transpose D) (q + 1) p) := fun _ _ => rfl
    simp only [hre]
    change ∑ p ∈ Finset.range (2 * D.N), (-1 : ℤ) ^ p * (Module.finrank k (colH (transpose D) 0 p) : ℤ) -
        ∑ q ∈ Finset.range D.N, ∑ p ∈ Finset.range D.N,
          (-1 : ℤ) ^ (q + p) * (Module.finrank k (colH (transpose D) (q + 1) p) : ℤ) = _

    have hvan_row : ∀ q p, D.N ≤ q → (Module.finrank k (colH (transpose D) q p) : ℤ) = 0 :=
      fun q p h => finrank_colH_eq_zero (transpose D) q p (D.hBound p q (Or.inr h))
    have hvan_col : ∀ q p, D.N ≤ p → (Module.finrank k (colH (transpose D) q p) : ℤ) = 0 :=
      fun q p h => finrank_colH_eq_zero (transpose D) q p (D.hBound p q (Or.inl h))

    have hrow0 : ∑ p ∈ Finset.range (2 * D.N), (-1 : ℤ) ^ p * (Module.finrank k (colH (transpose D) 0 p) : ℤ) =
        ∑ p ∈ Finset.range D.N, (-1 : ℤ) ^ p * (Module.finrank k (colH (transpose D) 0 p) : ℤ) := by
      rw [← Finset.sum_range_add_sum_Ico _ (show D.N ≤ 2 * D.N by omega)]
      rw [Finset.sum_eq_zero (s := Finset.Ico D.N (2 * D.N)) (fun p hp => by
        rw [hvan_col 0 p (Finset.mem_Ico.mp hp).1, mul_zero]), add_zero]
    rw [hrow0]
    rcases Nat.eq_zero_or_pos D.N with hN | hN
    · simp [hN]
    · obtain ⟨N', hN'⟩ : ∃ N', D.N = N' + 1 := ⟨D.N - 1, by omega⟩
      rw [hN']
      rw [Finset.sum_range_succ (fun q => ∑ p ∈ Finset.range (N' + 1),
          (-1 : ℤ) ^ (q + p) * (Module.finrank k (colH (transpose D) (q + 1) p) : ℤ)) N']
      rw [Finset.sum_eq_zero (s := Finset.range (N' + 1)) (f := fun p =>
          (-1 : ℤ) ^ (N' + p) * (Module.finrank k (colH (transpose D) (N' + 1) p) : ℤ)) (fun p _ => by
        beta_reduce
        rw [hvan_row (N' + 1) p (by omega), mul_zero]), add_zero]
      rw [Finset.sum_range_succ' (fun q => ∑ p ∈ Finset.range (N' + 1),
          (-1 : ℤ) ^ (q + p) * (Module.finrank k (colH (transpose D) q p) : ℤ)) N']
      have hsign : ∀ q p : ℕ, (-1 : ℤ) ^ (q + 1 + p) = -((-1 : ℤ) ^ (q + p)) := by
        intro q p; rw [show q + 1 + p = (q + p) + 1 by omega, pow_succ]; ring
      simp only [hsign, neg_mul, Finset.sum_neg_distrib, zero_add]
      ring

end ChiCol

open ChiCol DoubleComplex in
theorem solution
    {k : Type u} [Field k] (D : DoubleComplex.Bounded k)
    (hcol : ∀ p q : ℕ, Module.Finite k (DoubleComplex.colH D p q)) :
    (∀ n : ℕ, Module.Finite k (DoubleComplex.HTot D n)) ∧
      ∑ n ∈ Finset.range (2 * D.N), (-1 : ℤ) ^ n * (Module.finrank k (DoubleComplex.HTot D n) : ℤ) =
        ∑ p ∈ Finset.range D.N, ∑ q ∈ Finset.range D.N,
          (-1 : ℤ) ^ (p + q) * (Module.finrank k (DoubleComplex.colH D p q) : ℤ) := by
  have hTT : transpose (transpose D) = D := by cases D; rfl
  obtain ⟨hfinT, hsumT⟩ := row_form D.N (transpose D)
    (fun p q h => D.hBound q p (Or.inl h)) (fun q p => by rw [hTT]; exact hcol q p)
  have e : ∀ n, HTot (transpose D) n ≃ₗ[k] HTot D n :=
    fun n => (DoubleComplex.nonempty_HTot_transpose_equiv D n).some
  have hfin : ∀ n, Module.Finite k (HTot D n) := fun n => by
    haveI := hfinT n; exact Module.Finite.equiv (e n)
  refine ⟨hfin, ?_⟩
  rw [hTT] at hsumT
  have hsumT' : ∑ n ∈ Finset.range (2 * D.N), (-1 : ℤ) ^ n * (Module.finrank k (HTot (transpose D) n) : ℤ) =
      ∑ q ∈ Finset.range D.N, ∑ p ∈ Finset.range D.N,
        (-1 : ℤ) ^ (q + p) * (Module.finrank k (colH D q p) : ℤ) := hsumT
  rw [← hsumT']
  refine Finset.sum_congr rfl fun n _ => ?_
  haveI := hfinT n
  rw [(e n).finrank_eq]

end S_DoubleComplex_finite_HTot_and_sum_finrank_HTot_eq_sum_finrank_colH
end P2MW
export P2MW.S_DoubleComplex_finite_HTot_and_sum_finrank_HTot_eq_sum_finrank_colH (solution)
