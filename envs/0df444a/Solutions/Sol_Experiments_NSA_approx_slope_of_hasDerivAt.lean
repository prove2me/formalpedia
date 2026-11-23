-- Prove2me | solution 1 for Experiments.NSA.approx_slope_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:23:48.361716+00:00
-- url     : https://prove2.me/submissions/57a0229f-23d3-42b2-9105-d84ef591c668

import Mathlib
import Definitions.Def_Experiments_Ultrapower
import Theorems.Thm_Experiments_NSA_approx_std_coe

set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
namespace Experiments.NSA
theorem _root_.solution [NormedSpace ℝ E] {f : ℝ → E} {f' : E} {x : ℝ}
    (hf : HasDerivAt f f' x) {ε : Hyp ℝ} (hpos : IMem ε (Ioi 0)) (hε : ε ≈ₕ std 0) :
    ext (fun h => h⁻¹ • (f (x + h) - f x)) ε ≈ₕ std f' := by
  induction ε using Germ.inductionOn with
  | h e =>
    exact approx_std_coe.mpr (hf.tendsto_slope_zero_right.comp
      (tendsto_nhdsWithin_iff.mpr ⟨approx_std_coe.mp hε, Germ.liftPred_coe.mp hpos⟩))
end Experiments.NSA
