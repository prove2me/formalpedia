-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.pow_diff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:54.710401+00:00
-- url     : https://prove2.me/submissions/6ec10f58-bae3-4404-8ad8-56a3aef76428

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_mulU
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_powU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HenselRootsBounded
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.HenselRootsBounded
theorem _root_.solution (h : Ctx K R ϖ) {n : ℤ} (hn : 0 ≤ n) (s : ℕ) {w w' : K} (hw : w ∈ Pk R ϖ n)
    (hw' : w' ∈ Pk R ϖ n) :
    ∃ g ∈ Pk R ϖ n, (1 + w') ^ s - (1 + w) ^ s = (w' - w) * ((s : K) + g) := by
  refine ⟨∑ i ∈ Finset.range s, ((1 + w') ^ i * (1 + w) ^ (s - 1 - i) - 1),
    (Pk R ϖ n).sum_mem fun i _ => mulU h hn (powU h hn (by simpa using hw') i)
      (powU h hn (by simpa using hw) _), ?_⟩
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    add_sub_cancel, ← geom_sum₂_mul]
  ring
end Formalism.FourierDecayAlt.P.HenselRootsBounded
