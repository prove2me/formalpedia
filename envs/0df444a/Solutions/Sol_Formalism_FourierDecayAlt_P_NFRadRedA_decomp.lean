-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFRadRedA.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:32:11.972814+00:00
-- url     : https://prove2.me/submissions/7fd7a3ac-9424-44d8-aa9c-2801205d0ffc

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellInversePair
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOpenDomain
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedA
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedA_glev_uwb
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedA_zeta_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellInversePair_uw_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_rankOneCoord
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uw_inv


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
theorem _root_.solution (hk : 1 ≤ k) (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {g : Q.Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (hG : 0 < GGl k r z z' g) :
    ∃ h ∈ UWset k r z, ∃ h' ∈ UWset k r z', g = h * muZ k r μsec (zetaL k r z z' (Fin.last r) g) * h' := by
  have hU : g ∈ B2.UWb k r := glev_uwb hg
  have hζ : Tz k r z * Tz k r z' < Complex.normSq (herm (Hpk k r) (g *ᵥ z') z) := by
    have h2 := hG
    unfold GGl at h2
    rw [zeta_eq] at h2
    linarith
  obtain ⟨h, hh, h', hh', he⟩ := TwoByOneBlock.rankOneCoord k r z z' μsec hk hz hz' hT hT' hsec g hU hζ
  refine ⟨h⁻¹, BigCellInversePair.uw_inv hh, h', hh', ?_⟩
  rw [zeta_eq]
  exact he
end Formalism.FourierDecayAlt.P.NFRadRedA
