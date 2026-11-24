-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.poisson_level_joint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:53.470862+00:00
-- url     : https://prove2.me/submissions/dbf98767-2534-4121-859e-6fd20143a476

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonJointFirstReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open MeasureTheory Formalism.H
open scoped FourierTransform ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.PoissonStepJoint := by
  intro hF hJ E W _ D V _ _ _ _ _ ι _ π hπ Λ _ _ emb dmap hFr hW
  intro ε hε i hi1 hi2 w Y hY κ hκ t₀ B hB S hS
  obtain ⟨φ, Cφ, hc, hb, hnn, hdiag, hhat⟩ := hW ε hε i hi1 hi2 w Y hY κ hκ
  obtain ⟨hinj, hmem, hd0, hdual⟩ := hFr i hi1 hi2
  have key := hJ hF V ι π hπ (Λ i) E (emb i) (dmap i) (D.La i 1) (D.Lad i) φ Cφ
    (D.Nhat ε i w Y κ) hinj hmem hd0 hdual hc hb hnn hhat t₀ B hB S (fun t ht => (hS t ht).2)
  refine Eq.trans_le ?_ key
  exact Finset.sum_congr rfl fun t ht => hdiag t (hS t ht).1
end Formalism.FourierDecayAlt.P
