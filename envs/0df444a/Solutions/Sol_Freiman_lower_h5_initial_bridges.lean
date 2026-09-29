-- Prove2me | solution 1 for Freiman.lower_h5_initial_bridges
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T08:21:40.604516+00:00
-- url     : https://prove2.me/submissions/f227fd8e-27c7-48db-868e-d8acbeca8eaf

import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman
namespace M7H5Bridges14

private theorem family_parity (f : LowerInitialFamily) (n k p : ℕ) :
    (lowerFamilyPair f n k p).1.length % 2 = (lowerFamilyPair f n k p).2.length % 2 := by
  cases f <;>
    simp only [lowerFamilyPair, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil] <;> omega

private theorem normalized_parity (q : LowerPair) (hq : q.1.length % 2 = q.2.length % 2) :
    (lowerNormalize q).1.length % 2 = (lowerNormalize q).2.length % 2 := by
  unfold lowerNormalize
  split_ifs
  · exact hq
  · exact hq.symm

private theorem bridge_lengths (f : LowerInitialFamily) (n : ℕ) (d : LowerPair)
    (hd : d ∈ lowerBridgeLabels f n) : d.1.length = d.2.length := by
  cases f <;> simp only [lowerBridgeLabels] at hd
  · split_ifs at hd <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    · rcases hd with rfl | rfl | rfl | rfl | rfl <;> rfl
    · rcases hd with rfl | rfl | rfl | rfl <;> rfl
  · simp only [List.mem_singleton] at hd
    subst d
    rfl
  · exact (List.not_mem_nil hd).elim
  · exact (List.not_mem_nil hd).elim

private theorem bridges (f : LowerInitialFamily) (n p : ℕ) (d : LowerPair)
    (hd : d ∈ lowerBridgeLabels f n) :
    ¬(lowerMixed (lowerPhysicalAdd (lowerFamilyPair f n 0 p) d) ∧
      lowerL (lowerPhysicalAdd (lowerFamilyPair f n 0 p) d)) := by
  intro hm
  have hq := normalized_parity _ (family_parity f n 0 p)
  have hdlen := bridge_lengths f n d hd
  apply hm.1
  simp only [lowerPhysicalAdd, List.length_append]
  omega

end M7H5Bridges14

theorem solution (f : LowerInitialFamily) (n p : ℕ) (d : LowerPair) (hd : d ∈ lowerBridgeLabels f n) :
    ¬(lowerMixed (lowerPhysicalAdd (lowerFamilyPair f n 0 p) d) ∧ lowerL (lowerPhysicalAdd (lowerFamilyPair f n 0 p) d)) := by
  exact M7H5Bridges14.bridges f n p d hd

#print axioms solution
