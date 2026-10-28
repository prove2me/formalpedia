-- Prove2me | solution 1 for DataMerger.Quality.lemma_2_ii
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:45:24.109241+00:00
-- url     : https://prove2.me/submissions/827b1424-2e49-48c6-b657-cadd2aa6e803

import Mathlib
import Definitions.Def_DataMerger_Quality_Model

open DataMerger.Quality in
theorem solution (alpha : ℝ) (V : ℝ → ℝ) (hS : Standing alpha V)
    (d d' : ℝ) (hd : 0 ≤ d) (hd' : 0 ≤ d') :
    deriv (fun x => piB V d x) d' < 0 := by
  obtain ⟨_, hV, hder, hbd, _⟩ := hS
  have hmono : StrictMonoOn V (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hV.continuous.continuousOn
    intro x hx
    rw [interior_Ici] at hx
    exact hder x (le_of_lt hx)
  have h0d : V 0 ≤ V d := hmono.monotoneOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hd) hd
  have hb := hbd d' hd'
  have hpos : 0 < 3 + V d - V d' := by linarith
  have hD : HasDerivAt (fun x => (3 + V d - V x) ^ 2 / 18)
      ((2 : ℕ) * (3 + V d - V d') ^ (2 - 1) * (-deriv V d') / 18) d' :=
    ((((hV d').hasDerivAt).const_sub (3 + V d))).pow 2 |>.div_const 18
  unfold piB
  rw [hD.deriv]
  apply div_neg_of_neg_of_pos _ (by norm_num)
  apply mul_neg_of_pos_of_neg (mul_pos (by norm_num) (pow_pos hpos _))
  linarith [hder d' hd']
