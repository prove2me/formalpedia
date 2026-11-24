-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianXiVector.uh_of_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:12:52.104548+00:00
-- url     : https://prove2.me/submissions/fdce9954-4f51-4a1d-9a11-5462ada33866

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagSpanVanishing
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianXiVector
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_herm_basis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.HermitianXiVector
open C2x5 FlagSpanVanishing
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.HermitianXiVector
theorem _root_.solution {n : ℕ} (H A : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ y y', herm H (A *ᵥ y) (A *ᵥ y') = herm H y y') : A ∈ UH H := by
  show Aᴴ * H * A = H
  ext i j
  have h1 := h (Pi.single j 1) (Pi.single i 1)
  rw [herm_basis] at h1
  rw [h1]
  simp [herm, dotProduct, mulVec, Pi.single_apply]
end Formalism.FourierDecayAlt.P.HermitianXiVector
