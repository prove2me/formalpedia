-- Prove2me | solution 1 for GJKKL.Main.pfrac_ge_mu
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:55:42.012802+00:00
-- url     : https://prove2.me/submissions/897ff18a-fdeb-46be-b144-cb4a0025faae

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
variable {a μ x y : ℝ}
namespace GJKKL.Main
theorem _root_.solution {a μ : ℝ} (ha : 0 < a) {m t : ℕ} (hm : (m : ℝ) ≤ (1 - μ) * a) (ht : t ≤ m) :
    μ ≤ pfrac a t := by
  unfold pfrac
  have : (t : ℝ) / a ≤ 1 - μ := by
    rw [div_le_iff₀ ha]
    have : (t : ℝ) ≤ m := by exact_mod_cast ht
    linarith
  linarith
end GJKKL.Main
