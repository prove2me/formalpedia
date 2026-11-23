-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BoxAverageLimits.card_slab
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:34.793554+00:00
-- url     : https://prove2.me/submissions/b7973240-f1e7-4182-890f-4d540849e3b7

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AverageOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BoxAverageLimits
open Formalism.FourierDecayAlt.crystallineComparison
variable {Λ : Type} [AddCommGroup Λ] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace Formalism.FourierDecayAlt.P.BoxAverageLimits
theorem _root_.solution (R : ℕ) (j : ι) (a : ℕ) :
    (Fintype.piFinset (Function.update (fun _ : ι => range R) j {a})).card =
      R ^ (Fintype.card ι - 1) := by
  rw [Fintype.card_piFinset]
  have : ∀ i, (Function.update (fun _ : ι => range R) j {a} i).card = if i = j then 1 else R := by
    intro i; by_cases h : i = j
    · subst h; simp
    · simp [h]
  simp_rw [this]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  rw [Finset.filter_ne' Finset.univ j, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ]
end Formalism.FourierDecayAlt.P.BoxAverageLimits
