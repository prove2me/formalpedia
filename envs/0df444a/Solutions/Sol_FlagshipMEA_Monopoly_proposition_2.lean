-- Prove2me | solution 1 for FlagshipMEA.Monopoly.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T18:02:27.454287+00:00
-- url     : https://prove2.me/submissions/b963d110-52ee-4d17-9189-3f6d91b0e41a

import Mathlib
import Definitions.Def_FlagshipMEA_Monopoly_Model
import Theorems.Thm_FlagshipMEA_Monopoly_lemma_4
import Theorems.Thm_FlagshipMEA_Monopoly_lemma_5

open FlagshipMEA.Monopoly

theorem solution {n : ℕ} (D : Data n) (hS : D.Standing)
    (hfc : D.FcConcave) (m : Fin n → ℝ) (hm : D.IsOptimal m)
    (i : Fin n) (hi : 0 < m i) : D.IsArgmaxR (tme m) i := by
  have hn : 0 < n := Fin.pos i
  have hM : 0 < tme m :=
    lt_of_lt_of_le hi (Finset.single_le_sum (fun j _ => hm.1 j) (Finset.mem_univ i))
  obtain ⟨k0, -, hrev0, hmax⟩ := lemma_4 D hS hn (tme m) hM
  apply hmax m hm.1 rfl _ i hi
  intro m' hm' htme'
  have hfeas : Feasible (fun j : Fin n => if j = k0 then tme m else 0) := by
    intro j; dsimp only; split_ifs <;> linarith
  have hp := hm.2 _ hfeas
  have hc := lemma_5 D hS hfc (tme m) hM.le k0 m hm.1 rfl
  have hr := hrev0 m' hm' htme'
  unfold Data.profit at hp
  linarith
