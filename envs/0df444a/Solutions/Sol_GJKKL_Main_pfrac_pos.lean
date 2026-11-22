-- Prove2me | solution 1 for GJKKL.Main.pfrac_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:27:55.014956+00:00
-- url     : https://prove2.me/submissions/7234664d-6d08-4520-b319-929bdcea9877

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_Main_pfrac_ge_mu

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
variable {a μ x y : ℝ}
namespace GJKKL.Main
theorem _root_.solution {a μ : ℝ} (ha : 0 < a) (hμ : 0 < μ) {m t : ℕ} (hm : (m : ℝ) ≤ (1 - μ) * a)
    (ht : t ≤ m) : 0 < pfrac a t :=
  hμ.trans_le (pfrac_ge_mu ha hm ht)
end GJKKL.Main
