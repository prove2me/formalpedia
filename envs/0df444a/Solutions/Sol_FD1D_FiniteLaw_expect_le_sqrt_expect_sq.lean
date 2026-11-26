-- Prove2me | solution 1 for FD1D.FiniteLaw.expect_le_sqrt_expect_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:37:48.596249+00:00
-- url     : https://prove2.me/submissions/d8023a96-9d01-4dde-8c6f-3ae073f21ca1

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_FiniteLaw_expect_sq_le_expect_sq
import Theorems.Thm_FD1D_FiniteLaw_expect_mono
import Theorems.Thm_FD1D_FiniteLaw_expect_nonneg


set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
open FD1D.FiniteLaw
namespace FD1D.FiniteLaw
theorem _root_.solution (μ : FiniteLaw Ω) (f g : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) (hg : ∀ ω, 0 ≤ g ω)
    (hfg : ∀ ω, f ω ^ 2 ≤ g ω) :
    μ.expect f ≤ Real.sqrt (μ.expect g) := by
  have hef : 0 ≤ μ.expect f := μ.expect_nonneg hf
  have heg : 0 ≤ μ.expect g := μ.expect_nonneg hg
  rw [Real.le_sqrt hef heg]
  calc
    μ.expect f ^ 2 ≤ μ.expect (fun ω => f ω ^ 2) :=
      μ.expect_sq_le_expect_sq f
    _ ≤ μ.expect g := μ.expect_mono hfg
end FD1D.FiniteLaw
