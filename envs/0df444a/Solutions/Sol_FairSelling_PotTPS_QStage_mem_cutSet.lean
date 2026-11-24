-- Prove2me | solution 1 for FairSelling.PotTPS.QStage.mem_cutSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:31:45.439244+00:00
-- url     : https://prove2.me/submissions/e77406fb-229d-40c5-91a2-84e6b40daca7

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PotTPS.QStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
omit [Fintype G]
namespace FairSelling.PotTPS.QStage
theorem _root_.solution {s : QStage G n} {g : G} {i : Fin n} (h : g ∈ s.src i) : g ∈ s.cutSet :=
  Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩
end FairSelling.PotTPS.QStage
