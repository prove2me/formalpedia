-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:38:08.803111+00:00
-- url     : https://prove2.me/submissions/9b7ee28e-63e2-4110-977a-1c248771ec97

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellInversePair
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOpenDomain
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedA
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedA_uwb_glev
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedA_muZ_uwb
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedA_zeta_muZ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFRadRedA
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Classical
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
namespace Formalism.FourierDecayAlt.P.NFRadRedA
theorem _root_.solution (hz : inWb k r z) (hz' : inWb k r z') (hsec : IsSection k r z z' μsec)
    {q : (Fin r → ℂ) × ℂ} (hq : q ∈ QR k r z z') : (q.1, muZ k r μsec q.2) ∈ DomR k r z z' := by
  refine ⟨hq.1, uwb_glev (muZ_uwb hsec hq.2), ?_⟩
  show 0 < GGl k r z z' (muZ k r μsec q.2)
  unfold GGl
  rw [zeta_muZ hz hz' hsec hq.2]
  exact sub_pos.2 hq.2
end Formalism.FourierDecayAlt.P.NFRadRedA
