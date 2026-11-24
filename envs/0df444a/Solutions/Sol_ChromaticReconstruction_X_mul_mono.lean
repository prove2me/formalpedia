-- Prove2me | solution 1 for ChromaticReconstruction.X_mul_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:34:05.665838+00:00
-- url     : https://prove2.me/submissions/ecab387e-e308-42d9-b415-41bdfd87c778

import Definitions.Def_RequestProject_RecoverP
import Definitions.Def_RequestProject_Theta

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution (r : ℕ) (μ : Multiset ℕ) : X r * mono μ = mono (r ::ₘ μ) := by
  unfold mono
  rw [X, monomial_mul, one_mul, ← Multiset.singleton_add, Multiset.toFinsupp_add,
    Multiset.toFinsupp_singleton]
end ChromaticReconstruction
