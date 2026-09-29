-- Prove2me | solution 1 for Combinatorics.single_set_monochromatic_event_probability_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T20:54:54.094989+00:00
-- url     : https://prove2.me/submissions/c5479f8a-f675-473b-931c-06144eb6dcc9

import Mathlib

theorem solution
    (X : Type*) [Fintype X] [DecidableEq X]
    (B : Finset X) (m : Nat) (hm : 0 < m) (hsize : B.card = m) :
    ((Finset.univ.filter (fun c : X -> Bool =>
        (forall x, Membership.mem B x -> c x = true) \/
        (forall x, Membership.mem B x -> c x = false))).card : Real) /
        (Fintype.card (X -> Bool) : Real) <= (2 : Real) ^ (1 - (m : Real)) := by
  classical
  let T := {x : X // x ∉ B}
  have hconst (b : Bool) :
      (Finset.univ.filter (fun c : X -> Bool =>
        ∀ x, Membership.mem B x → c x = b)).card ≤ 2 ^ Fintype.card T := by
    let f : {c : X -> Bool // c ∈ Finset.univ.filter (fun c : X -> Bool =>
        ∀ x, Membership.mem B x → c x = b)} → (T → Bool) :=
      fun c x => c.1 x.1
    have hf : Function.Injective f := by
      intro c d h
      apply Subtype.ext
      funext x
      by_cases hx : Membership.mem B x
      · have hc := c.2
        have hd := d.2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc hd
        rw [hc x hx, hd x hx]
      · exact congrFun h ⟨x, hx⟩
    have hcard := Fintype.card_le_of_injective f hf
    have hcoe := Fintype.card_coe
      (Finset.univ.filter (fun c : X -> Bool =>
        ∀ x, Membership.mem B x → c x = b))
    rw [← hcoe]
    simpa [f, Fintype.card_fun] using hcard
  let E : Finset (X -> Bool) := Finset.univ.filter (fun c =>
    (∀ x, Membership.mem B x → c x = true) ∨
    (∀ x, Membership.mem B x → c x = false))
  let Et : Finset (X -> Bool) := Finset.univ.filter (fun c =>
    ∀ x, Membership.mem B x → c x = true)
  let Ef : Finset (X -> Bool) := Finset.univ.filter (fun c =>
    ∀ x, Membership.mem B x → c x = false)
  have hsub : E ⊆ Et ∪ Ef := by
    intro c hc
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rcases hc with hc | hc
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
  have hcount : E.card ≤ 2 * 2 ^ Fintype.card T := by
    calc
      E.card ≤ (Et ∪ Ef).card := Finset.card_le_card hsub
      _ ≤ Et.card + Ef.card := Finset.card_union_le _ _
      _ ≤ 2 ^ Fintype.card T + 2 ^ Fintype.card T := Nat.add_le_add (hconst true) (hconst false)
      _ = 2 * 2 ^ Fintype.card T := by rw [two_mul]
  have hT : Fintype.card T + m = Fintype.card X := by
    have hcomp := Fintype.card_subtype_compl (fun x : X => Membership.mem B x)
    have hB' : Fintype.card {x : X // Membership.mem B x} = B.card := by
      simpa using (Fintype.card_coe B).symm
    have hBcard : Fintype.card {x : X // Membership.mem B x} = m := by
      rw [hB', hsize]
    rw [hBcard] at hcomp
    have hle : m ≤ Fintype.card X := by
      rw [← hsize]
      exact Finset.card_le_univ B
    rw [hcomp]
    exact Nat.sub_add_cancel hle
  have hcardtotal : Fintype.card (X -> Bool) = 2 ^ Fintype.card X := by
    simp [Fintype.card_fun]
  have hden : 0 < (Fintype.card (X -> Bool) : Real) := by positivity
  have hcount' : E.card ≤ 2 ^ Fintype.card T * 2 := by
    simpa [Nat.mul_comm] using hcount
  have hnum : (E.card : Real) ≤ (2 : Real) ^ Fintype.card T * 2 := by
    exact_mod_cast hcount'
  have hpow : (2 : Real) ^ Fintype.card T * 2 =
      (2 : Real) ^ (1 - (m : Real)) * (Fintype.card (X -> Bool) : Real) := by
    rw [hcardtotal]
    rw [show ((2 ^ Fintype.card X : Nat) : Real) =
      (2 : Real) ^ (Fintype.card X : Real) by norm_cast]
    rw [← Real.rpow_natCast (2 : Real) (Fintype.card T)]
    have hTreal : (Fintype.card T : Real) + (m : Real) = Fintype.card X := by
      exact_mod_cast hT
    calc
      Real.rpow 2 (Fintype.card T : Real) * (2 : Real) =
          Real.rpow 2 (Fintype.card T : Real) * Real.rpow 2 1 := by
            have hr1 : Real.rpow 2 (1 : Real) = 2 := by
              exact Real.rpow_one 2
            rw [hr1]
      _ = Real.rpow 2 ((Fintype.card T : Real) + 1) := by
        exact (Real.rpow_add zero_lt_two _ _).symm
      _ = Real.rpow 2 ((Fintype.card X : Real) + (1 - (m : Real))) := by
        congr 1
        linarith
      _ = Real.rpow 2 (1 - (m : Real)) * Real.rpow 2 (Fintype.card X : Real) := by
        rw [show (Fintype.card X : Real) + (1 - (m : Real)) =
          (1 - (m : Real)) + (Fintype.card X : Real) by ring]
        exact Real.rpow_add zero_lt_two _ _
  change (E.card : Real) / (Fintype.card (X -> Bool) : Real) ≤ _
  rw [div_le_iff₀ hden]
  calc
    (E.card : Real) ≤ (2 : Real) ^ Fintype.card T * 2 := hnum
    _ = (2 : Real) ^ (1 - (m : Real)) * (Fintype.card (X -> Bool) : Real) := by
      simpa [hcardtotal] using hpow
