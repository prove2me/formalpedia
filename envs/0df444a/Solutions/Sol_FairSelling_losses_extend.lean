-- Prove2me | solution 1 for FairSelling.losses_extend
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:11:41.395834+00:00
-- url     : https://prove2.me/submissions/32ac24d2-1601-4efd-8f2d-91d27e9bb84a

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_EquiMMS
import Definitions.Def_RequestProject_TwoThirdsLoss
import Theorems.Thm_FairSelling_losses_extend_set
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) {T : Finset (Fin n)} {R : Finset G}
    {D : ℝ} (hL : Losses v p T R D) {a : Fin n} (ha : a ∈ T)
    (E F : Finset G) (c : ℝ) (hE : E ⊆ R) (hF : F ⊆ R) (hEF : Disjoint E F) (hc : 0 ≤ c)
    (htype : ∀ i ∈ T.erase a, ∀ Ei : EquiMMS (v i) p (MMS n (v i) p) n,
      LossOK (v i) p Ei.sell (MMS n (v i) p) (thr v p i) E F c) :
    Losses v p (T.erase a) (R \ (E ∪ F)) (D + (∑ g ∈ F, p g) - c) := by
  classical
  have key := losses_extend_set v p hL (Kset := {a}) (by simpa using ha)
    (fun _ => E) (fun _ => F) (fun _ => c) (fun b _ => hE) (fun b _ => hF) (fun b _ => hEF)
    (fun b hb b' hb' hbb => absurd (by rw [Finset.mem_singleton.mp hb,
      Finset.mem_singleton.mp hb']) hbb)
    (fun b _ => hc) ?_
  · have h1 : T \ ({a} : Finset (Fin n)) = T.erase a := by
      rw [Finset.erase_eq]
    have h2 : ({a} : Finset (Fin n)).biUnion (fun _ => E ∪ F) = E ∪ F := by simp
    rw [h1, h2] at key
    simpa using key
  · intro i hi Ei b _
    exact htype i (by rwa [Finset.erase_eq]) Ei
end FairSelling
