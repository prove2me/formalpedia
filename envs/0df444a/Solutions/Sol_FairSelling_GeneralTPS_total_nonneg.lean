-- Prove2me | solution 1 for FairSelling.GeneralTPS.total_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:39:11.151869+00:00
-- url     : https://prove2.me/submissions/171acafa-d4ee-490b-afc9-cce3ee8dff24

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
import Definitions.Def_RequestProject_TPSSefxGeneral

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.GeneralTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling.GeneralTPS
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (hp : ∀ g, 0 ≤ p g)
    {s : Stage G n} (hs : s.Good v p eps) : 0 ≤ s.total v p := by
  refine Finset.sum_nonneg (fun i _ => ?_)
  have hb : (0:ℝ) ≤ vbarSum (v i) p (s.bundle i) :=
    Finset.sum_nonneg (fun g _ => le_trans (hp g) (le_max_left _ _))
  linarith [hs.2.2.2.1 i]
end FairSelling.GeneralTPS
