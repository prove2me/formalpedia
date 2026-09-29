-- Prove2me | solution 1 for Combinatorics.finite_symmetric_local_lemma
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T20:17:16.94649+00:00
-- url     : https://prove2.me/submissions/5e8d556f-5a8a-4b68-99d2-1920ce850551
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Combinatorics_finite_symmetric_local_lemma_criterion
import Mathlib

theorem solution
    (Omega I : Type*) [Fintype Omega] [Nonempty Omega] [DecidableEq Omega]
    [Fintype I] [DecidableEq I]
    (A : I -> Finset Omega) (dep : I -> I -> Prop) [DecidableRel dep]
    (d : Nat) (p : Real)
    (hdegree : forall i, (Finset.univ.filter (fun j => dep i j)).card <= d)
    (hprob : forall i, ((A i).card : Real) / (Fintype.card Omega : Real) <= p)
    (hindependent : forall (i : I) (S : Finset I),
      (forall j, Membership.mem S j -> Not (dep i j)) ->
      ((Finset.filter (fun w => Membership.mem (A i) w)
          (Finset.univ.filter (fun w => forall j, Membership.mem S j ->
            Not (Membership.mem (A j) w)))).card : Real) /
          (Fintype.card Omega : Real) =
        (((Finset.univ.filter (fun w => forall j, Membership.mem S j ->
            Not (Membership.mem (A j) w))).card : Real) /
            (Fintype.card Omega : Real)) *
          ((A i).card : Real) / (Fintype.card Omega : Real))
    (hcond : 4 * p * ((d + 1 : Nat) : Real) < 1) :
    Exists fun w : Omega => forall i, Not (Membership.mem (A i) w) := by
  classical
  by_cases hI : Nonempty I
  · have hp : 0 <= p := by
      cases hI with
      | intro i =>
        have h := hprob i
        have hnonneg : 0 <= ((A i).card : Real) / (Fintype.card Omega : Real) :=
          div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        linarith
    push_cast at hcond
    let x : Real := 2 * p
    have hx0 : 0 <= x := by dsimp [x]; positivity
    have hx1 : x < 1 := by
      dsimp [x]
      have hDnat : 1 <= d + 1 := by omega
      have hD : (1 : Real) <= (d : Real) + 1 := by exact_mod_cast hDnat
      have hmult : 4 * p <= 4 * p * ((d : Real) + 1) := by nlinarith [hD, hp]
      nlinarith [hcond, hmult]
    have hbasepos : 0 < 1 - x := by linarith
    have hBernoulli : forall n : Nat, (1 - x) ^ n >= 1 - (n : Real) * x := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [pow_succ]
          calc
            (1 - x) ^ n * (1 - x) >= (1 - (n : Real) * x) * (1 - x) :=
              mul_le_mul_of_nonneg_right ih (le_of_lt hbasepos)
            _ = 1 - ((n + 1 : Nat) : Real) * x + (n : Real) * x ^ 2 := by
              push_cast
              ring
            _ >= 1 - ((n + 1 : Nat) : Real) * x := by
              have hsquare : 0 <= (n : Real) * x ^ 2 :=
                mul_nonneg (Nat.cast_nonneg _) (sq_nonneg x)
              linarith
    have hprob' : forall i,
        ((A i).card : Real) / (Fintype.card Omega : Real) <=
          x * (1 - x) ^ (Finset.univ.filter (fun j => dep i j)).card := by
      intro i
      have hcard : ((Finset.univ.filter (fun j => dep i j)).card : Real) <= d := by
        exact_mod_cast hdegree i
      have hnx : ((Finset.univ.filter (fun j => dep i j)).card : Real) * x <= d * x :=
        mul_le_mul_of_nonneg_right hcard hx0
      have hdx : (d : Real) * x < 1 / 2 := by
        dsimp [x]
        have hDnat : 1 <= d + 1 := by omega
        have hD : (1 : Real) <= (d : Real) + 1 := by exact_mod_cast hDnat
        have hmult : 4 * p <= 4 * p * ((d : Real) + 1) := by nlinarith [hD, hp]
        nlinarith [hcond, hmult]
      have hpow : (1 - x) ^ (Finset.univ.filter (fun j => dep i j)).card >= (1 : Real) / 2 := by
        have hb := hBernoulli (Finset.univ.filter (fun j => dep i j)).card
        nlinarith [hb, hnx, hdx]
      have hpbound := hprob i
      calc
        ((A i).card : Real) / (Fintype.card Omega : Real) <= p := hpbound
        _ <= x * (1 - x) ^ (Finset.univ.filter (fun j => dep i j)).card := by
          dsimp [x]
          nlinarith [hpow, hp]
    exact Combinatorics.finite_symmetric_local_lemma_criterion Omega I A dep x hx0 hx1 hprob' hindependent
  · letI : IsEmpty I := { false := fun i => hI (Nonempty.intro i) }
    exact Exists.intro (Classical.choice (inferInstance : Nonempty Omega))
      (fun i => isEmptyElim i)
