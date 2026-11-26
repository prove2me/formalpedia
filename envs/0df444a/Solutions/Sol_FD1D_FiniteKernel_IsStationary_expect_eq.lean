-- Prove2me | solution 1 for FD1D.FiniteKernel.IsStationary.expect_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:45:49.415307+00:00
-- url     : https://prove2.me/submissions/9e8dd455-c13f-45bd-a7cb-d863450eab27

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Expectations

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
open FD1D.FiniteKernel
variable {α : Type*} [Fintype α]
namespace FD1D.FiniteKernel
namespace IsStationary
theorem _root_.solution {K : FiniteKernel α} {μ : FiniteLaw α}
    (hμ : K.IsStationary μ) (f : α → ℝ) :
    (K.step μ).expect f = μ.expect f := by
  rw [hμ]
end IsStationary
end FD1D.FiniteKernel
