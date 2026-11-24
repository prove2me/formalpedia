-- Prove2me | solution 1 for FTheoryK3.discriminant_natDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-21T20:07:49.393303+00:00
-- url     : https://prove2.me/submissions/14dbad44-5344-4cc9-b500-a176532eff5b

import Definitions.Def_FTheoryK3Core
open Polynomial
variable {k : Type*} [Field k]

theorem solution (f g : k[X]) (hf : f.natDegree ≤ 8) (hg : g.natDegree ≤ 12) :
    (FTheoryK3.Δ f g).natDegree ≤ 24 := by
  unfold FTheoryK3.Δ
  compute_degree
  omega
