-- Prove2me | solution 1 for DataMerger.Quality.exclusivity
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:42:33.795527+00:00
-- url     : https://prove2.me/submissions/a9dbab23-d757-49f6-997b-c99c85b3dfe5

import Mathlib
import Definitions.Def_DataMerger_Quality_Model

open DataMerger.Quality in
theorem solution (alpha : ℝ) (V : ℝ → ℝ) (hS : Standing alpha V)
    (δ : ℝ) (hδ : 0 < δ) :
    ExclusiveI (piB V) δ ∧ ExclusiveM (piB V) δ := by
  obtain ⟨_, hV, hder, _, _⟩ := hS
  have hmono : StrictMonoOn V (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hV.continuous.continuousOn
    intro x hx
    rw [interior_Ici] at hx
    exact hder x (le_of_lt hx)
  have ha : V 0 < V δ := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hδ.le) hδ
  have ha2 : 0 < (V δ - V 0) * (V δ - V 0) := mul_pos (by linarith) (by linarith)
  constructor
  · unfold ExclusiveI T1 T2 piB
    nlinarith
  · unfold ExclusiveM T2 piB
    nlinarith
