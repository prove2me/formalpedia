-- Prove2me | solution 1 for DistVerif.Simulation.observation_3_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:30:12.729026+00:00
-- url     : https://prove2.me/submissions/0ce1942c-4f46-4a14-8573-1d9f534d5aa9

import Mathlib
import Definitions.Def_DistVerif_Simulation_Algorithm

open DistVerif.Simulation in
theorem solution {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s r : V) {B b : ℕ} (A : DetAlg V B b) (U U' : Set V) (hUU' : U ⊆ U')
    (x y x' y' : Fin b → Bool) (t : ℕ)
    (hconf : ∀ v ∈ U', A.exec G s r x y t v = A.exec G s r x' y' t v)
    (hmsg : ∀ w u : V, w ∉ U' → u ∈ U → G.Adj w u →
      A.send w u (A.exec G s r x y t w) = A.send w u (A.exec G s r x' y' t w)) :
    ∀ v ∈ U, A.exec G s r x y (t + 1) v = A.exec G s r x' y' (t + 1) v := by
  intro v hv
  rw [DetAlg.exec, DetAlg.exec, hconf v (hUU' hv)]
  congr 1
  funext w
  split_ifs with h
  · by_cases hw : w ∈ U'
    · rw [hconf w hw]
    · exact hmsg w v hw hv h
  · rfl
