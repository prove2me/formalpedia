-- Prove2me | solution 1 for Freiman.form_reduced_orbit_exists
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T20:19:25.141537+00:00
-- url     : https://prove2.me/submissions/9ac394b3-0dba-4f49-8728-3869a68db9d0

import Definitions.Def_Freiman_reducedForms
import Theorems.Thm_Freiman_cfValue_surjective_irrational_unit
import Theorems.Thm_Freiman_form_symbolic_orbit
import Theorems.Thm_Freiman_form_orbit_forward_tail
import Theorems.Thm_Freiman_form_orbit_backward_tail
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 800000

open Freiman

theorem solution (α β : ℝ) (hα : 1 < α) (hβ : 0 < β) (hβ1 : β < 1)
    (hiα : Irrational α) (hiβ : Irrational β) :
    ∃ R : ReducedOrbit, R.alpha 0 = α ∧ R.beta 0 = β := by
  let δ : ℝ := α - (⌊α⌋₊ : ℝ)
  have hiδ : Irrational δ := hiα.sub_natCast _
  have hδ0 : 0 < δ := by
    have hnonneg : 0 ≤ δ := sub_nonneg.mpr (Nat.floor_le (by linarith))
    exact lt_of_le_of_ne hnonneg (Ne.symm hiδ.ne_zero)
  have hδ1 : δ < 1 := by
    have hh := Nat.lt_floor_add_one α
    dsimp [δ]
    linarith
  obtain ⟨t, ht⟩ := cfValue_surjective_irrational_unit δ hiδ hδ0 hδ1
  obtain ⟨s, hs⟩ := cfValue_surjective_irrational_unit β hiβ hβ hβ1
  let d : ℕ+ := ⟨⌊α⌋₊, Nat.floor_pos.mpr hα.le⟩
  let a : ℤ → ℕ+
    | .ofNat 0 => d
    | .ofNat (k + 1) => t k
    | .negSucc k => s k
  have ha0 : a 0 = d := rfl
  have hap (k : ℕ) : a ((k : ℤ) + 1) = t k := by
    change a (Int.ofNat (k + 1)) = t k
    rfl
  have ham (k : ℕ) : a (-(k : ℤ) - 1) = s k := by
    have he : -(k : ℤ) - 1 = Int.negSucc k := by omega
    rw [he]
  obtain ⟨R, hR⟩ := form_symbolic_orbit a
  refine ⟨R, ?_, ?_⟩
  · rw [form_orbit_forward_tail R 0, hR, ha0]
    have he : (fun k : ℕ => a (0 + (k : ℤ) + 1)) = t := by
      funext k
      simpa using hap k
    rw [he, ht]
    change (⌊α⌋₊ : ℝ) + (α - (⌊α⌋₊ : ℝ)) = α
    ring
  · rw [form_orbit_backward_tail R 0, hR]
    have he : (fun k : ℕ => a (0 - (k : ℤ) - 1)) = s := by
      funext k
      simpa using ham k
    rw [he, hs]
