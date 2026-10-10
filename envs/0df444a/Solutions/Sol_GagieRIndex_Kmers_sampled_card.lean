-- Prove2me | solution 1 for GagieRIndex.Kmers.sampled_card
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-10T04:53:55.144402+00:00
-- url     : https://prove2.me/submissions/7001b0b0-77fc-43bb-8e8d-7cbc8cf591f4

import Mathlib
import Definitions.Def_GagieRIndex_Locate_Core

set_option autoImplicit false

namespace SampledCardAux

variable (n : ℕ) (T SA : ℕ → ℕ)

/-- Successor map: run-ends inject into run-starts via `p ↦ (p = n ? 1 : p + 1)`. -/
def succRS (p : ℕ) : ℕ := if p = n then 1 else p + 1

/-- `succRS` always lands back in `Icc 1 n`. -/
theorem succRS_mem_Icc (h1n : 1 ≤ n) {p : ℕ} (hmem : p ∈ Finset.Icc 1 n) :
    succRS n p ∈ Finset.Icc 1 n := by
  unfold succRS
  split
  · rw [Finset.mem_Icc]; exact ⟨le_rfl, h1n⟩
  · rename_i hpn
    obtain ⟨h1p, hple⟩ := Finset.mem_Icc.mp hmem
    have hlt : p < n := lt_of_le_of_ne hple hpn
    rw [Finset.mem_Icc]
    constructor <;> omega

/-- The successor of a run-end that is not a run-start is a run-start:
if `p ≠ n`, `IsRunEnd` gives `bwt (p+1) ≠ bwt p`, i.e. `p + 1` is a run-start;
if `p = n`, the successor is `1`, always a run-start. -/
theorem succRS_runStart (h1n : 1 ≤ n) {p : ℕ}
    (hmem : p ∈ Finset.Icc 1 n)
    (hend : GagieRIndex.Locate.IsRunEnd n T SA p)
    (hns : ¬ GagieRIndex.Locate.IsRunStart n T SA p) :
    GagieRIndex.Locate.IsRunStart n T SA (succRS n p) := by
  unfold succRS
  split
  · exact ⟨le_rfl, h1n, Or.inl rfl⟩
  · rename_i hpn
    obtain ⟨h1p, hple⟩ := Finset.mem_Icc.mp hmem
    have hlt : p < n := lt_of_le_of_ne hple hpn
    have hmem' : p + 1 ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hmem'
    obtain ⟨-, -, hdisj⟩ := hend
    refine ⟨h1, h2, Or.inr ?_⟩
    rcases hdisj with rfl | hne
    · exact absurd rfl hpn
    · have hsub : p + 1 - 1 = p := Nat.add_sub_cancel p 1
      rw [hsub]
      exact Ne.symm hne

/-- Injection from (run-starts ∪ run-ends) into (run-starts × Bool):
run-starts go to `(p, true)`, other run-ends to `(succRS p, false)`. -/
def injMap (p : ℕ) : ℕ × Bool :=
  if GagieRIndex.Locate.IsRunStart n T SA p then (p, true) else (succRS n p, false)

theorem injMap_mem (h1n : 1 ≤ n) {p : ℕ}
    (hmem : p ∈ (Finset.Icc 1 n).filter
      (fun p => GagieRIndex.Locate.IsRunStart n T SA p ∨ GagieRIndex.Locate.IsRunEnd n T SA p)) :
    injMap n T SA p ∈ (Finset.Icc 1 n).filter (GagieRIndex.Locate.IsRunStart n T SA)
      ×ˢ {true, false} := by
  rw [Finset.mem_filter] at hmem
  obtain ⟨hmemIcc, hdisj⟩ := hmem
  unfold injMap
  split
  · rename_i hs
    rw [Finset.mem_product, Finset.mem_filter]
    refine ⟨⟨hmemIcc, hs⟩, ?_⟩
    rw [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inl rfl
  · rename_i hns
    rcases hdisj with hs | he
    · exact absurd hs hns
    · rw [Finset.mem_product, Finset.mem_filter]
      refine ⟨⟨succRS_mem_Icc n h1n hmemIcc,
        succRS_runStart n T SA h1n hmemIcc he hns⟩, ?_⟩
      rw [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr rfl

/-- `succRS` is injective on `Icc 1 n` (the `p = n ↦ 1` case can't collide
with `p + 1` since `1 ≤ p` forces `p + 1 ≥ 2`). -/
theorem succRS_inj {a b : ℕ}
    (haIcc : a ∈ Finset.Icc 1 n) (hbIcc : b ∈ Finset.Icc 1 n)
    (h : succRS n a = succRS n b) : a = b := by
  unfold succRS at h
  by_cases han : a = n <;> by_cases hbn : b = n
  · exact han.trans hbn.symm
  · rw [if_pos han, if_neg hbn] at h
    obtain ⟨h1b, -⟩ := Finset.mem_Icc.mp hbIcc
    omega
  · rw [if_neg han, if_pos hbn] at h
    obtain ⟨h1a, -⟩ := Finset.mem_Icc.mp haIcc
    omega
  · rw [if_neg han, if_neg hbn] at h
    omega

theorem injMap_injOn :
    Set.InjOn (injMap n T SA)
      ↑((Finset.Icc 1 n).filter
        (fun p => GagieRIndex.Locate.IsRunStart n T SA p ∨ GagieRIndex.Locate.IsRunEnd n T SA p)) := by
  intro a ha b hb hab
  rw [Finset.mem_coe, Finset.mem_filter] at ha hb
  obtain ⟨haIcc, -⟩ := ha
  obtain ⟨hbIcc, -⟩ := hb
  unfold injMap at hab
  by_cases haS : GagieRIndex.Locate.IsRunStart n T SA a <;>
    by_cases hbS : GagieRIndex.Locate.IsRunStart n T SA b
  · rw [if_pos haS, if_pos hbS] at hab
    exact congrArg Prod.fst hab
  · rw [if_pos haS, if_neg hbS] at hab
    exact Bool.noConfusion (congrArg Prod.snd hab)
  · rw [if_neg haS, if_pos hbS] at hab
    exact Bool.noConfusion (congrArg Prod.snd hab)
  · rw [if_neg haS, if_neg hbS] at hab
    exact succRS_inj n haIcc hbIcc (congrArg Prod.fst hab)

/-- The counting core: `|sampled| ≤ |run-starts ∪ run-ends| ≤ 2 * |run-starts|`. -/
theorem sampled_card_le (σ : ℕ) (hT : GagieRIndex.Locate.IsText n σ T) :
    (GagieRIndex.Locate.sampled n T SA).card ≤ 2 * GagieRIndex.Locate.runs n T SA := by
  obtain ⟨h1n, -, -, -⟩ := hT
  have h1 : (GagieRIndex.Locate.sampled n T SA).card ≤
      ((Finset.Icc 1 n).filter
        (fun p => GagieRIndex.Locate.IsRunStart n T SA p ∨ GagieRIndex.Locate.IsRunEnd n T SA p)).card := by
    have heq : GagieRIndex.Locate.sampled n T SA =
        ((Finset.Icc 1 n).filter
          (fun p => GagieRIndex.Locate.IsRunStart n T SA p ∨
            GagieRIndex.Locate.IsRunEnd n T SA p)).image
          (GagieRIndex.Locate.textPos n SA) := rfl
    rw [heq]
    exact Finset.card_image_le
  have h2 : ((Finset.Icc 1 n).filter
        (fun p => GagieRIndex.Locate.IsRunStart n T SA p ∨ GagieRIndex.Locate.IsRunEnd n T SA p)).card ≤
      ((Finset.Icc 1 n).filter (GagieRIndex.Locate.IsRunStart n T SA)).card * 2 := by
    have h := Finset.card_le_card_of_injOn (injMap n T SA)
      (fun a ha => injMap_mem n T SA h1n ha)
      (injMap_injOn n T SA)
    rw [Finset.card_product] at h
    have hcard : ({true, false} : Finset Bool).card = 2 := by decide
    rw [hcard] at h
    exact h
  have h3 : GagieRIndex.Locate.runs n T SA =
      ((Finset.Icc 1 n).filter (GagieRIndex.Locate.IsRunStart n T SA)).card := rfl
  omega

end SampledCardAux

theorem solution (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : GagieRIndex.Locate.IsText n σ T) (hSA : GagieRIndex.Locate.IsSuffixArray n T SA) :
    (GagieRIndex.Locate.sampled n T SA).card ≤ 2 * GagieRIndex.Locate.runs n T SA :=
  SampledCardAux.sampled_card_le n T SA σ hT

theorem GagieRIndex.Kmers.sampled_card (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : GagieRIndex.Locate.IsText n σ T) (hSA : GagieRIndex.Locate.IsSuffixArray n T SA) :
    (GagieRIndex.Locate.sampled n T SA).card ≤ 2 * GagieRIndex.Locate.runs n T SA :=
  solution n σ T SA hT hSA
