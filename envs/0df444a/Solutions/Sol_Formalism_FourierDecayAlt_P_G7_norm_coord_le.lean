-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.norm_coord_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:43:48.315844+00:00
-- url     : https://prove2.me/submissions/11d521a7-6d72-4b17-bf18-6e27fe4cb53a

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_norm_entry_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_blk_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_blk_cl
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_blk_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_wMat_mulVec_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_wMat_mul_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G7
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2
namespace Formalism.FourierDecayAlt.P.G7
theorem _root_.solution {n : ℕ} (t σ : ℂ) (x : UT n → ℂ) (B ρ : Fin n → ℂ) (Z : Mat (n + 1))
    (hZ : Z = Mcoord t (strictUpper x) B ρ σ) : ‖((ρ, x, B) : BlockCoord n)‖ ≤ ‖Z‖ := by
  have hent : ∀ i j, ‖Mcoord t (strictUpper x) B ρ σ i j‖ ≤ ‖Z‖ := fun i j => by
    have he : Z i j = Mcoord t (strictUpper x) B ρ σ i j := by rw [hZ]
    rw [← he]; exact norm_entry_le Z i j
  rw [Prod.norm_def, Prod.norm_def]
  refine max_le ?_ (max_le ?_ ?_)
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
    have h := hent (Fin.last n) j.castSucc
    rwa [Mcoord, blk_lc] at h
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun ⟨⟨i, j⟩, hij⟩ => ?_
    have h := hent i.rev.castSucc j.castSucc
    have hij' : i < j := hij
    rw [Mcoord, blk_cc, wMat_mul_apply, Fin.rev_rev] at h
    simpa [strictUpper, hij', Matrix.one_apply, hij'.ne] using h
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    have h := hent i.rev.castSucc (Fin.last n)
    rwa [Mcoord, blk_cl, wMat_mulVec_apply, Fin.rev_rev] at h
end Formalism.FourierDecayAlt.P.G7
