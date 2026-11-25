-- Prove2me | solution 1 for ChromaticReconstruction.floor_half_le_tau
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:03:54.022011+00:00
-- url     : https://prove2.me/submissions/1516c260-7fcf-4018-a23e-6ab877de58e8

import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_Theorem2
import Definitions.Def_RequestProject_ProperTree
import Definitions.Def_RequestProject_CountingLimit
import Definitions.Def_RequestProject_TauBound
import Definitions.Def_RequestProject_MainTheorems
import Theorems.Thm_P2M_ChromaticReconstruction_floor_half_le_tau__f5e5110d9215


set_option autoImplicit true
open MvPolynomial Finset Filter Topology
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution (k : ℕ) (hk : 4 ≤ k) : ((k / 2 : ℕ) : ℕ∞) ≤ tau k :=
  floor_half_le_tau' k hk
end ChromaticReconstruction
