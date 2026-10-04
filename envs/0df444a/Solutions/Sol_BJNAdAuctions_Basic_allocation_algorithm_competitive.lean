-- Prove2me | solution 1 for BJNAdAuctions.Basic.allocation_algorithm_competitive
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T07:33:00.411738+00:00
-- url     : https://prove2.me/submissions/57a0969d-6236-40b3-a213-cb8bfdcc422e

import Theorems.Thm_BJNAdAuctions_Basic_almost_dual_feasible
import Theorems.Thm_BJNAdAuctions_Basic_primal_feasible
import Theorems.Thm_BJNAdAuctions_Basic_primal_dual_ratio
import Theorems.Thm_BJNAdAuctions_Basic_weak_duality
import Definitions.Def_BJNAdAuctions_Basic_Instance
import Definitions.Def_BJNAdAuctions_Basic_AllocationAlgorithm

/-!
# Theorem 1 (first sentence): the Allocation Algorithm is `(1 - 1/c)(1 - R)`-competitive

Assembling the proved milestones of the mission:

* `almost_dual_feasible` (Claim 3): `(1 - R) · A i ≤ spent i` per buyer, where
  `A i = ∑_j b i j y i j`; summing over buyers gives
  `(1 - R) · packingValue(alg y) ≤ revenue`.
* `primal_dual_ratio` (Claim 2): `coveringValue = (1 + 1/(c-1)) · packingValue` for the
  algorithm's own solution, and `(1 - 1/c)(1 + 1/(c-1)) = 1`.
* `primal_feasible` (Claim 1) + `weak_duality`: `packingValue y' ≤ coveringValue(alg)`.

The case `R > 1` is trivial because then the claimed ratio is nonpositive while the revenue is
nonnegative; nonnegativity of `spent` (indeed `0 ≤ spent ≤ B`) is a short induction over the
run, included below.
-/

open BJNAdAuctions.Basic

open scoped Classical

namespace BJNCompetitive

variable {I : Type*} [Fintype I] {m : ℕ}

/-- The charge rule keeps `0 ≤ spent i ≤ B i` after every prefix. -/
private lemma spent_bounds (inst : Instance I m) (c : ℝ) (sel : (I → ℝ) → Fin m → I) :
    ∀ k ≤ m, ∀ (i : I), 0 ≤ (runPrefix inst c sel k).spent i
      ∧ (runPrefix inst c sel k).spent i ≤ inst.B i
  | 0, _, i => by
      simp only [runPrefix, State.init]
      exact ⟨le_refl 0, (inst.B_pos i).le⟩
  | k + 1, hk, i => by
      have hkm : k < m := by omega
      set X := sel (runPrefix inst c sel k).x ⟨k, hkm⟩ with hXdef
      have hguard' : 1 ≤ (runPrefix inst c sel k).x
          (sel (runPrefix inst c sel k).x ⟨k, hkm⟩) ∨
          ¬1 ≤ (runPrefix inst c sel k).x (sel (runPrefix inst c sel k).x ⟨k, hkm⟩) :=
        Classical.em _
      rcases hguard' with hguard | hguard
      · -- state unchanged
        have hgoal : 0 ≤ (runPrefix inst c sel (k + 1)).spent i
            ∧ (runPrefix inst c sel (k + 1)).spent i ≤ inst.B i := by
          have h := spent_bounds inst c sel k (by omega) i
          rw [runPrefix, dif_pos hkm]
          simp only [step, if_pos hguard]
          exact h
        exact hgoal
      · rcases eq_or_ne i X with rfl | hi
        · -- the selected buyer is charged
          have hXb := spent_bounds inst c sel k (by omega) X
          have hb : 0 ≤ inst.b X ⟨k, hkm⟩ := inst.b_nonneg X _
          have hstep : (runPrefix inst c sel (k + 1)).spent X
              = (runPrefix inst c sel k).spent X
                + min (inst.b X ⟨k, hkm⟩) (inst.B X - (runPrefix inst c sel k).spent X) := by
            simp only [runPrefix, dif_pos hkm, step, if_neg hguard, hXdef,
              Function.update_self]
          have hgoal : 0 ≤ (runPrefix inst c sel (k + 1)).spent X
              ∧ (runPrefix inst c sel (k + 1)).spent X ≤ inst.B X := by
            rw [hstep]
            have hmin0 : 0 ≤ min (inst.b X ⟨k, hkm⟩)
                (inst.B X - (runPrefix inst c sel k).spent X) :=
              le_min hb (by linarith)
            have hmin1 : min (inst.b X ⟨k, hkm⟩)
                (inst.B X - (runPrefix inst c sel k).spent X)
                  ≤ inst.B X - (runPrefix inst c sel k).spent X :=
              min_le_right _ _
            exact ⟨by linarith, by linarith⟩
          exact hgoal
        · -- other buyers are untouched
          have hi' : i ≠ sel (runPrefix inst c sel k).x ⟨k, hkm⟩ := hi
          have hstep : (runPrefix inst c sel (k + 1)).spent i
              = (runPrefix inst c sel k).spent i := by
            simp only [runPrefix, dif_pos hkm, step, if_neg hguard,
              Function.update_of_ne hi']
          have hgoal : 0 ≤ (runPrefix inst c sel (k + 1)).spent i
              ∧ (runPrefix inst c sel (k + 1)).spent i ≤ inst.B i := by
            rw [hstep]
            exact spent_bounds inst c sel k (by omega) i
          exact hgoal

end BJNCompetitive

open BJNAdAuctions.Basic BJNCompetitive

theorem solution {I : Type*} [Fintype I] [Nonempty I] {m : ℕ}
    (inst : Instance I m) (R : ℝ) (hR : 0 < R) (hbR : ∀ i j, inst.b i j ≤ R * inst.B i)
    (sel : (I → ℝ) → Fin m → I) (hsel : IsArgmaxRule inst sel)
    (y' : I → Fin m → ℝ) (hy' : PackingFeasible inst y') :
    (1 - 1 / (1 + R) ^ (1 / R)) * (1 - R) * packingValue inst y' ≤
      revenue inst ((1 + R) ^ (1 / R)) sel := by
  set c := (1 + R) ^ (1 / R) with hc
  have hc1 : 1 < c := Real.one_lt_rpow (by linarith) (by positivity)
  have hlc : 1 / c ≤ 1 := by
    rw [div_le_one (by linarith : (0 : ℝ) < c)]
    linarith
  have hPnn : 0 ≤ packingValue inst y' := by
    refine Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun i _ => ?_))
    exact mul_nonneg (inst.b_nonneg i j) (hy'.1 i j)
  -- the algorithm's covering solution is feasible, so weak duality applies
  have hpf := primal_feasible inst c hc1 sel hsel
  have hwd : packingValue inst y' ≤ coveringValue inst (run inst c sel).x (run inst c sel).z :=
    weak_duality inst y' hy' _ _ hpf
  -- Claim 3 summed over buyers
  have hrev : (1 - R) * packingValue inst (run inst c sel).y ≤ revenue inst c sel := by
    have had : ∀ i : I, (1 - R) * (∑ j, inst.b i j * (run inst c sel).y i j)
        ≤ (run inst c sel).spent i :=
      fun i => (almost_dual_feasible inst R hR hbR sel i).2
    have hsum : (∑ i, (1 - R) * (∑ j, inst.b i j * (run inst c sel).y i j))
        = (1 - R) * packingValue inst (run inst c sel).y := by
      have h1 : (∑ j : Fin m, ∑ i : I, inst.b i j * (run inst c sel).y i j)
          = packingValue inst (run inst c sel).y := rfl
      have h2 : (∑ i : I, (1 - R) * (∑ j : Fin m, inst.b i j * (run inst c sel).y i j))
          = (1 - R) * (∑ i : I, ∑ j : Fin m, inst.b i j * (run inst c sel).y i j) := by
        rw [Finset.mul_sum Finset.univ
          (fun i => ∑ j : Fin m, inst.b i j * (run inst c sel).y i j) (1 - R)]
      rw [h2, Finset.sum_comm, h1]
    rw [← hsum, revenue]
    exact Finset.sum_le_sum (fun i _ => had i)
  rcases le_total R 1 with hR1 | hR1
  · -- the honest regime: (1 - 1/c)(1 - R) ≥ 0
    have hcal : (1 - 1 / c) * (1 + 1 / (c - 1)) = 1 := by
      have hne1 : c - 1 ≠ 0 := by linarith
      have hne0 : c ≠ 0 := by linarith
      field_simp
      ring
    have hpd := primal_dual_ratio inst c hc1 sel
    have step1 : (1 - 1 / c) * (1 - R) * packingValue inst y'
        ≤ (1 - 1 / c) * (1 - R)
            * ((1 + 1 / (c - 1)) * packingValue inst (run inst c sel).y) := by
      refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 1 / c) (by linarith : (0 : ℝ) ≤ 1 - R))
      exact hwd.trans (le_of_eq hpd)
    have key : (1 - 1 / c) * (1 - R)
        * ((1 + 1 / (c - 1)) * packingValue inst (run inst c sel).y)
        = (1 - R) * packingValue inst (run inst c sel).y := by
      calc (1 - 1 / c) * (1 - R)
            * ((1 + 1 / (c - 1)) * packingValue inst (run inst c sel).y)
          = ((1 - 1 / c) * (1 + 1 / (c - 1))) * ((1 - R)
              * packingValue inst (run inst c sel).y) := by ring
        _ = 1 * ((1 - R) * packingValue inst (run inst c sel).y) := by rw [hcal]
        _ = (1 - R) * packingValue inst (run inst c sel).y := one_mul _
    linarith [step1, hrev, key]
  · -- R ≥ 1: the claimed bound is nonpositive, revenue is nonnegative
    have hL : (1 - 1 / c) * (1 - R) * packingValue inst y' ≤ 0 := by
      have h1 : 0 ≤ 1 - 1 / c := by linarith
      have h2 : (1 - R) * packingValue inst y' ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (show (1 : ℝ) - R ≤ 0 by linarith) hPnn
      rw [mul_assoc]
      exact mul_nonpos_of_nonneg_of_nonpos h1 h2
    have hrevnn : 0 ≤ revenue inst c sel := by
      have hsp : ∀ i : I, 0 ≤ (runPrefix inst c sel m).spent i := fun i =>
        (spent_bounds inst c sel m (le_refl m) i).1
      rw [revenue, run]
      exact Finset.sum_nonneg (fun i _ => hsp i)
    linarith
