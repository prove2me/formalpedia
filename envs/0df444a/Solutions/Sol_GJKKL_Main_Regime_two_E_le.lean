-- Prove2me | solution 1 for GJKKL.Main.Regime.two_E_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:21:04.343805+00:00
-- url     : https://prove2.me/submissions/b1deec1e-04ca-4411-acb6-e58757278982

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_Main_Regime_d_pos
public import Theorems.Thm_GJKKL_Main_Regime_mu_pos
public import Theorems.Thm_GJKKL_Main_Regime_key_E

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
namespace GJKKL.Main.Regime
theorem _root_.solution {x : ℝ} (hμx : d ^ (-(ε ^ 3)) ≤ x) (hx1 : x ≤ 1) :
    2 * d ^ (1 - ε / 8) ≤ d ^ (-(ε ^ 3)) * d * x ^ (Bn k + (k - 1)) := by
  have hk := R.two_le
  have hμ := R.mu_pos
  have e : Bn k + k = (Bn k + (k - 1)) + 1 := by omega
  have h1 := R.key_E
  rw [e, pow_succ] at h1
  have h2 : (d ^ (-(ε ^ 3))) ^ (Bn k + (k - 1)) ≤ x ^ (Bn k + (k - 1)) :=
    pow_le_pow_left₀ hμ.le hμx _
  have h3 : d * ((d ^ (-(ε ^ 3))) ^ (Bn k + (k - 1)) * d ^ (-(ε ^ 3))) ≤
      d ^ (-(ε ^ 3)) * d * x ^ (Bn k + (k - 1)) := by
    have := mul_le_mul_of_nonneg_left h2 (mul_nonneg hμ.le R.d_pos.le)
    nlinarith
  linarith
end GJKKL.Main.Regime
