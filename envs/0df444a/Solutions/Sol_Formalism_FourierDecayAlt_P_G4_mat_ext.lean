-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.mat_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:40:49.449133+00:00
-- url     : https://prove2.me/submissions/3d489abc-7dec-4a82-9a88-23e1454e17dc

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt.G
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G4
namespace Formalism.FourierDecayAlt.P.G4
theorem _root_.solution {n : ℕ} {M N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (h1 : ∀ i j : Fin n, M i.castSucc j.castSucc = N i.castSucc j.castSucc)
    (h2 : ∀ i : Fin n, M i.castSucc (Fin.last n) = N i.castSucc (Fin.last n))
    (h3 : ∀ j : Fin n, M (Fin.last n) j.castSucc = N (Fin.last n) j.castSucc)
    (h4 : M (Fin.last n) (Fin.last n) = N (Fin.last n) (Fin.last n)) : M = N := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact h4
    | cast j => exact h3 j
  | cast i =>
    induction j using Fin.lastCases with
    | last => exact h2 i
    | cast j => exact h1 i j
end Formalism.FourierDecayAlt.P.G4
