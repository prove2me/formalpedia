-- Prove2me | solution 1 for DataMerger.Quality.lemma_2_i
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:44:06.678754+00:00
-- url     : https://prove2.me/submissions/e2ebc896-b40b-45d0-87a5-9d198eb5f939

import Mathlib
import Definitions.Def_DataMerger_Quality_Model

open DataMerger.Quality in
theorem solution (alpha : ℝ) (V : ℝ → ℝ) (hS : Standing alpha V)
    (d d' : ℝ) (hd : 0 ≤ d) (hd' : 0 ≤ d') :
    0 < deriv (fun x => piB V x d') d := by
  obtain ⟨_, hV, hder, hbd, _⟩ := hS
  have hmono : StrictMonoOn V (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hV.continuous.continuousOn
    intro x hx
    rw [interior_Ici] at hx
    exact hder x (le_of_lt hx)
  have h0d : V 0 ≤ V d := hmono.monotoneOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hd) hd
  have hb := hbd d' hd'
  have hpos : 0 < 3 + V d - V d' := by linarith
  have hD : HasDerivAt (fun x => (3 + V x - V d') ^ 2 / 18)
      ((2 : ℕ) * (3 + V d - V d') ^ (2 - 1) * deriv V d / 18) d :=
    ((((hV d).hasDerivAt).const_add 3).sub_const (V d')).pow 2 |>.div_const 18
  unfold piB
  rw [hD.deriv]
  apply div_pos _ (by norm_num)
  exact mul_pos (mul_pos (by norm_num) (pow_pos hpos _)) (hder d hd)
