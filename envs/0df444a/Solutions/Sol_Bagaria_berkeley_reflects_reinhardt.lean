-- Prove2me | solution 1 for Bagaria.berkeley_reflects_reinhardt
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T12:37:05.630214+00:00
-- url     : https://prove2.me/submissions/46137e61-5742-4629-bb95-947ecb6b9445

import Mathlib
import Definitions.Def_Bagaria_arena
import Definitions.Def_Bagaria_reinhardt
import Definitions.Def_Bagaria_berkeley
universe v

open Bagaria Bagaria.Universe

namespace S215BG

/-- The universe of ZF sets as a `Bagaria.Universe`. -/
noncomputable def zfU : Universe.{v} where
  carrier := ZFSet.{v}
  mem := fun x y => x ∈ y
  rank := ZFSet.rank
  ord := Ordinal.toZFSet
  mem_rank := fun _ _ h => ZFSet.rank_lt_of_mem h
  mem_ord := fun _ _ => Ordinal.toZFSet_mem_toZFSet_iff
  rank_ord := Ordinal.rank_toZFSet

theorem zf : SatisfiesZF (fun x y : ZFSet.{v} => x ∈ y) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y h
    exact ZFSet.ext h
  · intro x y
    exact ⟨({x, y} : ZFSet), fun z => ZFSet.mem_pair⟩
  · intro x
    exact ⟨ZFSet.sUnion x, fun z => by
      change z ∈ ZFSet.sUnion x ↔ ∃ y, y ∈ x ∧ z ∈ y
      rw [ZFSet.mem_sUnion]⟩
  · refine ⟨ZFSet.omega, ∅, ZFSet.omega_zero, fun x hx => ⟨insert x x, ZFSet.omega_succ hx, ?_, ?_⟩⟩
    · change x ∈ insert x x
      exact ZFSet.mem_insert _ _
    · intro w hw
      change w ∈ insert x x
      exact ZFSet.mem_insert_of_mem _ hw
  · intro x
    exact ⟨ZFSet.powerset x, fun z => by
      change z ∈ ZFSet.powerset x ↔ ∀ w, w ∈ z → w ∈ x
      rw [ZFSet.mem_powerset]; rfl⟩
  · intro x ⟨z, hz⟩
    have hne : x ≠ ∅ := fun h => by
      change z ∈ x at hz
      rw [h] at hz; exact ZFSet.notMem_empty _ hz
    obtain ⟨m, hm, hmx⟩ := ZFSet.regularity _ hne
    refine ⟨m, hm, fun w hw hwm => ?_⟩
    have : w ∈ x ∩ m := ZFSet.mem_inter.mpr ⟨hw, hwm⟩
    rw [hmx] at this; exact ZFSet.notMem_empty _ this
  · intro φ s a
    exact ⟨ZFSet.sep (fun x => holds (fun x y : ZFSet.{v} => x ∈ y) (fun n => if n = 0 then x else s (n - 1)) φ) a,
      fun x => ZFSet.mem_sep⟩
  · intro φ s a h
    let P : ZFSet.{v} → ZFSet.{v} → Prop := fun x y =>
      holds (fun x y : ZFSet.{v} => x ∈ y) (fun n => if n = 0 then x else if n = 1 then y else s (n - 2)) φ
    let f : ZFSet.{v} → ZFSet.{v} := fun x => if hx : ∃ y, P x y then Classical.choose hx else ∅
    have : ZFSet.Definable₁ f := Classical.allZFSetDefinable _
    refine ⟨ZFSet.image f a, fun y => ?_⟩
    change y ∈ ZFSet.image f a ↔ ∃ x, x ∈ a ∧ P x y
    rw [ZFSet.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y0, hy0, -⟩ := h x hx
      have hex : ∃ y, P x y := ⟨y0, hy0⟩
      refine ⟨x, hx, ?_⟩
      simp only [f, dif_pos hex]
      exact Classical.choose_spec hex
    · rintro ⟨x, hx, hPy⟩
      refine ⟨x, hx, ?_⟩
      have hex : ∃ y, P x y := ⟨y, hPy⟩
      obtain ⟨y0, -, huniq⟩ := h x hx
      simp only [f, dif_pos hex]
      rw [huniq _ (Classical.choose_spec hex), huniq _ hPy]

end S215BG

theorem solution : ¬ ∀ (U : Universe.{0}) (hZF : SatisfiesZF U.mem)
    (δ0 : Ordinal.{0}) (hB : U.berkeley δ0)
    (hL : ∀ δ : Ordinal.{0}, δ < δ0 → ¬ U.berkeley δ),
    ∃ γ : Ordinal.{0}, γ < δ0 ∧ SatisfiesZF (U.segmentMem γ) ∧ U.hasReinhardtIn γ := by
  intro H
  have hB0 : (S215BG.zfU.{0}).berkeley 0 := by
    intro M _ _ η hη
    exact (not_lt_zero hη).elim
  obtain ⟨γ, hγ, -⟩ := H S215BG.zfU.{0} S215BG.zf.{0} 0 hB0 (fun δ hδ => (not_lt_zero hδ).elim)
  exact not_lt_zero hγ
