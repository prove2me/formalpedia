-- Prove2me | solution 1 for GJKKL.Main.g_le_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:55:45.850554+00:00
-- url     : https://prove2.me/submissions/f9274016-6aa6-4b18-a8fa-cc31d7887302

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_Trajectory_pow_sub_pow_le


set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
variable {a μ x y : ℝ}
namespace GJKKL.Main
theorem _root_.solution {x y a d : ℝ} (j : ℕ) (hy : 0 ≤ y) (hxy : y ≤ x) (hx : 0 < x) (ha : 0 < a)
    (hd : 0 ≤ d) (hxy' : x - y = 1 / a) :
    d * x ^ (j + 1) - d * y ^ (j + 1) ≤ ((j : ℝ) + 1) * (d * x ^ (j + 1)) / (a * x) := by
  have h := pow_sub_pow_le hy hxy j
  rw [hxy'] at h
  have hx0 : x ≠ 0 := hx.ne'
  have ha0 : a ≠ 0 := ha.ne'
  have e : ((j : ℝ) + 1) * (d * x ^ (j + 1)) / (a * x) = d * (((j : ℝ) + 1) * x ^ j * (1 / a)) := by
    rw [pow_succ]
    first | (field_simp; ring) | field_simp
  rw [e]
  have : d * (x ^ (j + 1) - y ^ (j + 1)) ≤ d * (((j : ℝ) + 1) * x ^ j * (1 / a)) :=
    mul_le_mul_of_nonneg_left h hd
  linarith
end GJKKL.Main
