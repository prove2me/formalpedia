-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_finite_grid_cross_pair_card_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:43:24.957845+00:00
-- url     : https://prove2.me/submissions/dde0aaff-9ade-4a0d-86d8-18256269144b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {α : Type*} (F : Finset α) (k : ℕ) (g : α → Fin k) :
    (∑ i : Fin k,
      (F.filter (fun u => g u < i)).card *
        (F.filter (fun v => g v = i)).card) =
      ((F ×ˢ F).filter (fun p : α × α => g p.1 < g p.2)).card := by
  classical
  let S : Finset (α × α) :=
    (F ×ˢ F).filter (fun p : α × α => g p.1 < g p.2)
  have hfiber (i : Fin k) :
      (S.filter (fun p : α × α => g p.2 = i)) =
        (F.filter (fun u => g u < i)) ×ˢ
          (F.filter (fun v => g v = i)) := by
    ext p
    simp only [S, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨ha, hb⟩, hab⟩, hbi⟩
      exact ⟨⟨ha, by simpa [hbi] using hab⟩, ⟨hb, hbi⟩⟩
    · rintro ⟨⟨ha, hai⟩, ⟨hb, hbi⟩⟩
      exact ⟨⟨⟨ha, hb⟩, by simpa [hbi] using hai⟩, hbi⟩
  have hsum :
      (∑ i : Fin k, (S.filter (fun p : α × α => g p.2 = i)).card) =
        S.card := by
    simpa using
      (Finset.sum_fiberwise (s := S)
        (g := fun p : α × α => g p.2) (f := fun _ => (1 : ℕ)))
  change (∑ i : Fin k,
      (F.filter (fun u => g u < i)).card *
        (F.filter (fun v => g v = i)).card) = S.card
  calc
    _ = ∑ i : Fin k, (S.filter (fun p : α × α => g p.2 = i)).card := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hfiber i, Finset.card_product]
    _ = S.card := hsum
