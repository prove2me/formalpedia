-- Prove2me | solution 1 for Experiments.NSA.approx_of_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:21:53.650338+00:00
-- url     : https://prove2.me/submissions/a5c9e545-91f0-4f04-8bcc-296f4c55262d

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
theorem _root_.solution {lo ξ hi : Hyp ℝ} {t : ℝ} (hlo : lo ≤ ξ) (hhi : ξ ≤ hi)
    (hlot : lo ≈ₕ std t) (hhit : hi ≈ₕ std t) : ξ ≈ₕ std t := by
  induction lo, ξ, hi using Germ.inductionOn₃ with
  | H l u h =>
    exact approx_std_coe.mpr (tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (approx_std_coe.mp hlot) (approx_std_coe.mp hhit) (Germ.coe_le.mp hlo) (Germ.coe_le.mp hhi))
end Experiments.NSA
