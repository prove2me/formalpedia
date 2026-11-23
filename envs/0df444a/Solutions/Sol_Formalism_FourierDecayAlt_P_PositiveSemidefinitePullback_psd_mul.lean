-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback.psd_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:31.772576+00:00
-- url     : https://prove2.me/submissions/203eb228-63f4-4aec-afc3-f6879b4dd4c6

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveSemidefinitePullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
open Finset Matrix Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
noncomputable section
open Classical
namespace Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
theorem _root_.solution {α : Type} {Y : Finset α} {k₁ k₂ : α → α → ℂ} (h₁ : PSDOn Y k₁) (h₂ : PSDOn Y k₂) :
    PSDOn Y (fun p q => k₁ p q * k₂ p q) :=
  Matrix.PosSemidef.hadamard h₁ h₂
end Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
