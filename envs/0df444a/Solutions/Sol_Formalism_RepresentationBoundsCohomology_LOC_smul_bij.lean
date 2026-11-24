-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.smul_bij
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:36:34.627708+00:00
-- url     : https://prove2.me/submissions/e407357e-7493-4cca-bc4d-d13c6315f642

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_FibreDualStable
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_PropLoc
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_HOneTorsionFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism.NG (KO annih)
open ReciprocityTheory.Gal
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.LOC
namespace Formalism.RepresentationBoundsCohomology.LOC
theorem _root_.solution {O V : Type u} [CommRing O] [IsDomain O] [AddCommGroup V] [Module O V]
    [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] (c : O) (hc : c ≠ 0) :
    Function.Bijective fun v : V => c • v := by
  have hc' : algebraMap O (FractionRing O) c ≠ 0 := by
    simpa using hc
  constructor
  · intro v w h
    have h' : algebraMap O (FractionRing O) c • v = algebraMap O (FractionRing O) c • w := by
      simpa only [algebraMap_smul] using h
    exact smul_right_injective V hc' h'
  · intro v
    refine ⟨(algebraMap O (FractionRing O) c)⁻¹ • v, ?_⟩
    show c • _ = v
    rw [← algebraMap_smul (FractionRing O) c, smul_smul, mul_inv_cancel₀ hc', one_smul]
end Formalism.RepresentationBoundsCohomology.LOC
