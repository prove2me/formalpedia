-- Prove2me | solution 1 for FTheoryK3Tate.discriminant_natDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-22T11:08:55.569781+00:00
-- url     : https://prove2.me/submissions/e69fa028-e186-48db-845f-7b4fb26e600b

import Definitions.Def_FTheoryK3TateCore

open Polynomial

open FTheoryK3Tate

variable {k : Type*} [Field k]

theorem solution (f g : k[X])
    (hf : f.natDegree ≤ 8) (hg : g.natDegree ≤ 12) :
    (Δ f g).natDegree ≤ 24 := by
  unfold Δ
  compute_degree
  omega

#check @solution
#print axioms solution
