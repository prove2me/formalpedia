-- Prove2me | solution 1 for FixedMachinePrec.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:06:18.842159+00:00
-- url     : https://prove2.me/submissions/5400469a-a50a-4b7e-9435-921da53c2ae2

import Mathlib
import Definitions.Def_FixedMachinePrec_Instance

open FixedMachinePrec in
theorem solution (m : ℕ) (hm : 1 ≤ m) (G : Instance) (hG : G.Acyclic) (σ : Schedule G m)
    (hσ : σ.Feasible) :
    ∃ (T : ℕ) (τ : Fin G.n → ℕ), IsSlotSchedule G m T τ ∧ (T : ℝ) ≤ σ.cmax := by
  have hc : ∀ x, σ.start x + 1 ≤ σ.cmax := by
    intro x
    unfold Schedule.cmax
    rw [dif_pos x.pos]
    exact Finset.le_sup' (fun x => σ.start x + 1) (Finset.mem_univ x)
  have hc0 : 0 ≤ σ.cmax := by
    unfold Schedule.cmax
    split_ifs with h
    · exact le_trans (by linarith [hσ.1 ⟨0, h⟩])
        (Finset.le_sup' (fun x => σ.start x + 1) (Finset.mem_univ ⟨0, h⟩))
    · exact le_rfl
  refine ⟨⌊σ.cmax⌋₊, fun x => ⌊σ.start x⌋₊ + 1, ⟨fun x => ⟨Nat.le_add_left 1 _, ?_⟩, fun t => ?_,
    fun x y hxy => ?_⟩, Nat.floor_le hc0⟩
  · apply Nat.le_floor
    push_cast
    have := Nat.floor_le (hσ.1 x)
    linarith [hc x]
  · calc (Finset.univ.filter fun x => ⌊σ.start x⌋₊ + 1 = t).card
        ≤ (Finset.univ : Finset (Fin m)).card := by
          apply Finset.card_le_card_of_injOn σ.machine
            (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
          intro x hx y hy hmxy
          by_contra hne
          rw [Finset.mem_coe, Finset.mem_filter] at hx hy
          have hxt : ⌊σ.start x⌋₊ + 1 = t := hx.2
          have hyt : ⌊σ.start y⌋₊ + 1 = t := hy.2
          have hfl : ⌊σ.start x⌋₊ = ⌊σ.start y⌋₊ := by omega
          have hfl' : (⌊σ.start x⌋₊ : ℝ) = (⌊σ.start y⌋₊ : ℝ) := by exact_mod_cast hfl
          have h1 := Nat.floor_le (hσ.1 x)
          have h2 := Nat.floor_le (hσ.1 y)
          have h3 := Nat.lt_floor_add_one (σ.start x)
          have h4 := Nat.lt_floor_add_one (σ.start y)
          rcases hσ.2.1 x y hne hmxy with h | h <;> linarith
      _ = m := by simp
  · have h := hσ.2.2 x y hxy
    have h' := Nat.floor_le_floor h
    rw [Nat.floor_add_one (hσ.1 x)] at h'
    show ⌊σ.start x⌋₊ + 1 < ⌊σ.start y⌋₊ + 1
    omega
