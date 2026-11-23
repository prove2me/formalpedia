-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PairingConjugationLemmas.map_fd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:49.462832+00:00
-- url     : https://prove2.me/submissions/08d1a8c9-4ed2-4648-acc0-90f96bde02b2

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PairingTriangular
import Theorems.Thm_Formalism_FourierDecayAlt_P_PairingConjugationLemmas_repr_Tl
import Theorems.Thm_Formalism_FourierDecayAlt_P_PairingConjugationLemmas_Tl_emb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PairingConjugationLemmas
open MeasureTheory Filter Topology Finset Module Formalism.FourierDecayAlt.crystallineComparison
noncomputable section
variable {f : ℕ}
variable (La : Submodule ℤ (V f)) [DiscreteTopology La] [IsZLattice ℝ La]
namespace Formalism.FourierDecayAlt.P.PairingConjugationLemmas
theorem _root_.solution :
    Measure.map (Tl La) (volume : Measure (Fin (finrank ℤ La) → ℝ)) (ZSpan.fundamentalDomain (bR La)) = 1 := by
  rw [(Tl_emb La).map_apply]
  have hpre : (Tl La) ⁻¹' ZSpan.fundamentalDomain (bR La) =
      Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1) := by
    ext y
    simp [ZSpan.mem_fundamentalDomain, repr_Tl]
  rw [hpre, MeasureTheory.volume_pi_pi]
  simp [Real.volume_Ico]
end Formalism.FourierDecayAlt.P.PairingConjugationLemmas
