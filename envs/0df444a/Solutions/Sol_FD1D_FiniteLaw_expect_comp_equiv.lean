-- Prove2me | solution 1 for FD1D.FiniteLaw.expect_comp_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:29:05.050834+00:00
-- url     : https://prove2.me/submissions/c08e2809-8e42-4a4b-a959-c268809af79e

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
open FD1D.FiniteLaw
variable {Ω : Type*} [Fintype Ω]
namespace FD1D.FiniteLaw
theorem _root_.solution (μ : FiniteLaw Ω) (e : Ω ≃ Ω)
    (he : InvariantUnder μ e) (f : Ω → ℝ) :
    μ.expect (fun ω => f (e ω)) = μ.expect f := by
  rw [expect, expect]
  calc
    ∑ ω, μ.mass ω * f (e ω) = ∑ ω, μ.mass (e ω) * f (e ω) := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [he]
    _ = ∑ ω, μ.mass ω * f ω := by
      exact e.sum_comp (fun ω => μ.mass ω * f ω)
end FD1D.FiniteLaw
