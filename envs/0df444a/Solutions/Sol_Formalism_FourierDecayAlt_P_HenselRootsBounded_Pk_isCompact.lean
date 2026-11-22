-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.Pk_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:53:38.182079+00:00
-- url     : https://prove2.me/submissions/cae1e429-d83a-44a1-9e14-9a2e2f9681bb

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded

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
theorem _root_.solution (h : Ctx K R ϖ) (k : ℤ) : IsCompact (Pk R ϖ k : Set K) := by
  have : (Pk R ϖ k : Set K) = (fun x => ((ϖ ^ k : Kˣ) : K) * x) '' (R : Set K) := by
    ext x
    constructor
    · intro hx
      refine ⟨((ϖ ^ (-k) : Kˣ) : K) * x, hx, ?_⟩
      show ((ϖ ^ k : Kˣ) : K) * (((ϖ ^ (-k) : Kˣ) : K) * x) = x
      rw [← mul_assoc, ← Units.val_mul, ← zpow_add]; simp
    · rintro ⟨r, hr, rfl⟩
      show ((ϖ ^ (-k) : Kˣ) : K) * (((ϖ ^ k : Kˣ) : K) * r) ∈ R
      rw [← mul_assoc, ← Units.val_mul, ← zpow_add]; simpa using hr
  rw [this]
  exact h.isCompact.image (continuous_const.mul continuous_id)
end Formalism.FourierDecayAlt.P.HenselRootsBounded
