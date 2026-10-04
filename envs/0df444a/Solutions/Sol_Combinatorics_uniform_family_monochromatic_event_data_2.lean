-- Prove2me | solution 2 for Combinatorics.uniform_family_monochromatic_event_data
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T02:49:47.613212+00:00
-- url     : https://prove2.me/submissions/6810bbe9-b1bf-4aeb-a070-99ad0a799568

import Mathlib

theorem dp_bad8193e_aux (a b c N : ℕ) (hN : 0 < N)
    (h : (a : ℝ) / (N : ℝ) = (b : ℝ) / (N : ℝ) * (c : ℝ) / (N : ℝ)) :
    a * N = b * c := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  field_simp at h
  have h2 : ((a * N : ℕ) : ℝ) = ((b * c : ℕ) : ℝ) := by
    push_cast
    nlinarith [h]
  exact_mod_cast h2

theorem solution : ¬ (∀
    (X I : Type) [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I]
    (B : I -> Finset X) (m D : Nat)
    (hm : 0 < m) (hsize : forall i, (B i).card = m)
    (hdegree : forall x, (Finset.univ.filter (fun i => Membership.mem (B i) x)).card <= D),
    (let A : I -> Finset (X -> Bool) := fun i =>
      Finset.univ.filter (fun c =>
        (forall x, Membership.mem (B i) x -> c x = true) \/
        (forall x, Membership.mem (B i) x -> c x = false))
     let dep : I -> I -> Prop := fun i j =>
       i != j /\ Exists fun x => Membership.mem (B i) x /\ Membership.mem (B j) x
     (forall i, (Finset.univ.filter (fun j => dep i j)).card <= m * D - 1) /\
     (forall i, ((A i).card : Real) / (Fintype.card (X -> Bool) : Real) <=
       (2 : Real) ^ (1 - (m : Real))) /\
     (forall (i : I) (S : Finset I),
       (forall j, Membership.mem S j -> Not (dep i j)) ->
       ((Finset.filter (fun w => Membership.mem (A i) w)
           (Finset.univ.filter (fun w => forall j, Membership.mem S j ->
             Not (Membership.mem (A j) w)))).card : Real) /
           (Fintype.card (X -> Bool) : Real) =
         (((Finset.univ.filter (fun w => forall j, Membership.mem S j ->
             Not (Membership.mem (A j) w))).card : Real) /
             (Fintype.card (X -> Bool) : Real)) *
           ((A i).card : Real) / (Fintype.card (X -> Bool) : Real)))) := by
  intro h
  have h2 := h (Fin 2) Unit (fun _ => Finset.univ) 2 1 (by norm_num) (fun _ => rfl)
    (fun _ => (Finset.card_le_univ _).trans (by simp))
  obtain ⟨-, -, h3⟩ := h2
  have key := h3 () {()} (by
    intro j _ hd
    simp at hd)
  have := dp_bad8193e_aux _ _ _ _ (by exact Fintype.card_pos) key
  revert this
  decide
