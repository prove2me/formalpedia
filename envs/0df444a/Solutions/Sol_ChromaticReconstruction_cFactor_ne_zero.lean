-- Prove2me | solution 1 for ChromaticReconstruction.cFactor_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T13:10:26.616114+00:00
-- url     : https://prove2.me/submissions/626b380e-41bd-44c1-bc32-a1e1d9ecac64

import Definitions.Def_RequestProject_ChromCoeff
import Definitions.Def_RequestProject_Theorem2

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*} [Fintype V] [Fintype W]
namespace ChromaticReconstruction
theorem _root_.solution {q : ℕ} (hq : 2 ≤ q) (t : ℕ) : cFactor q t ≠ 0 := by
  unfold cFactor
  apply mul_ne_zero (pow_ne_zero _ (by norm_num))
  exact_mod_cast (by omega : q - 1 ≠ 0)
end ChromaticReconstruction
