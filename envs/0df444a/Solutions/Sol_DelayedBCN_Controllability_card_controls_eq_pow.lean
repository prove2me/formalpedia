-- Prove2me | solution 1 for DelayedBCN.Controllability.card_controls_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T05:14:26.432973+00:00
-- url     : https://prove2.me/submissions/ec012467-9ffc-4200-95a9-0d1cc67986e4

import Mathlib
import Definitions.Def_DelayedBCN_Controllability_Model
import Definitions.Def_DelayedBCN_Controllability_Matrix

open DelayedBCN.Controllability

theorem solution {μ n m : ℕ} [NeZero μ] (F : Network μ n m)
    (ya yb : Traj μ n) (k : ℕ) :
    numSteering F k ya yb = (Q F ^ k) yb ya := by
  have hprefix : ∀ (k : ℕ) (U : Fin (k+1) → Input m) (i : ℕ), i ≤ k →
      trajAt F ya U i = trajAt F ya (fun j : Fin k => U j.castSucc) i := by
    intro k U i hi
    induction i with
    | zero => rfl
    | succ i ih =>
        have hik : i < k := Nat.lt_of_succ_le hi
        rw [trajAt, dif_pos (Nat.lt_succ_of_lt hik)]
        rw [trajAt, dif_pos hik]
        have hidx : U ⟨i, Nat.lt_succ_of_lt hik⟩
            = (fun j : Fin k => U j.castSucc) ⟨i, hik⟩ := rfl
        rw [hidx, ih (Nat.le_of_lt hik)]
  have htraj_snoc : ∀ (k : ℕ) (U' : Fin k → Input m) (u : Input m),
      trajAt F ya (Fin.snoc U' u) (k+1) = step F u (trajAt F ya U' k) := by
    intro k U' u
    rw [trajAt, dif_pos (Nat.lt_succ_self k)]
    have hlast : (Fin.snoc (α := fun _ => Input m) U' u) ⟨k, Nat.lt_succ_self k⟩ = u := by
      rw [show (⟨k, Nat.lt_succ_self k⟩ : Fin (k+1)) = Fin.last k from Fin.ext rfl]
      exact Fin.snoc_last (α := fun _ => Input m) u U'
    rw [hlast]
    have hpref : (fun j : Fin k => (Fin.snoc (α := fun _ => Input m) U' u) j.castSucc) = U' := by
      funext j
      exact Fin.snoc_castSucc (α := fun _ => Input m) u U' j
    rw [hprefix k (Fin.snoc U' u) k (le_refl k), hpref]
  have hQ : ∀ (yb : Traj μ n) (a : Traj μ n),
      (∑ u : Input m, (if step F u a = yb then 1 else 0)) = Q F yb a := by
    intro yb a
    rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
    rfl
  have hsum : ∀ k : ℕ, ∀ yb : Traj μ n,
      (∑ U : Fin k → Input m, (if trajAt F ya U k = yb then (1:ℕ) else 0))
        = (Q F ^ k) yb ya := by
    intro k
    induction k with
    | zero =>
        intro yb
        haveI : Unique (Fin 0 → Input m) :=
          ⟨⟨fun i => i.elim0⟩, fun U => funext fun i => i.elim0⟩
        rw [pow_zero, Fintype.sum_unique, Matrix.one_apply]
        show (if ya = yb then (1:ℕ) else 0) = (if yb = ya then (1:ℕ) else 0)
        by_cases h : ya = yb
        · rw [if_pos h, if_pos h.symm]
        · rw [if_neg h, if_neg (fun hh => h hh.symm)]
    | succ k ih =>
        intro yb
        rw [pow_succ']
        rw [show (∑ U : Fin (k+1) → Input m,
              (if trajAt F ya U (k+1) = yb then (1:ℕ) else 0))
            = ∑ p : Input m × (Fin k → Input m),
                (if trajAt F ya (Fin.snoc p.2 p.1) (k+1) = yb then (1:ℕ) else 0) from
          (Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (k+1) => Input m))
            (fun p : Input m × (Fin k → Input m) =>
              (if trajAt F ya (Fin.snoc p.2 p.1) (k+1) = yb then (1:ℕ) else 0))
            (fun U : Fin (k+1) → Input m =>
              (if trajAt F ya U (k+1) = yb then (1:ℕ) else 0))
            (fun p => rfl)).symm]
        rw [show (∑ p : Input m × (Fin k → Input m),
              (if trajAt F ya (Fin.snoc p.2 p.1) (k+1) = yb then (1:ℕ) else 0))
            = ∑ p : Input m × (Fin k → Input m),
                (if step F p.1 (trajAt F ya p.2 k) = yb then (1:ℕ) else 0) from
          Finset.sum_congr rfl (fun p _ => by rw [htraj_snoc])]
        rw [Fintype.sum_prod_type]
        rw [Finset.sum_comm]
        rw [show (∑ U' : Fin k → Input m, ∑ u : Input m,
              (if step F u (trajAt F ya U' k) = yb then (1:ℕ) else 0))
            = ∑ U' : Fin k → Input m, Q F yb (trajAt F ya U' k) from
          Finset.sum_congr rfl (fun U' _ => hQ yb _)]
        rw [show (∑ U' : Fin k → Input m, Q F yb (trajAt F ya U' k))
            = ∑ a : Traj μ n, numSteering F k ya a * Q F yb a from by
          rw [← Finset.sum_fiberwise_of_maps_to'
                (s := (Finset.univ : Finset (Fin k → Input m)))
                (t := (Finset.univ : Finset (Traj μ n)))
                (g := fun U' => trajAt F ya U' k) (f := fun a => Q F yb a)
                (fun i _ => Finset.mem_univ _)]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_const]
          rfl]
        rw [show (∑ a : Traj μ n, numSteering F k ya a * Q F yb a)
            = ∑ a : Traj μ n, (Q F ^ k) a ya * Q F yb a from by
          apply Finset.sum_congr rfl
          intro a _
          have ha : numSteering F k ya a = (Q F ^ k) a ya := by
            unfold numSteering
            rw [Finset.card_eq_sum_ones, Finset.sum_filter]
            exact ih a
          rw [ha]]
        rw [show (∑ a : Traj μ n, (Q F ^ k) a ya * Q F yb a)
            = (Q F * Q F ^ k) yb ya from by
          rw [Matrix.mul_apply]
          apply Finset.sum_congr rfl
          intro a _
          rw [mul_comm]]
  unfold numSteering
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact hsum k yb
