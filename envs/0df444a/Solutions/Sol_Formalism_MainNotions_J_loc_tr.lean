-- Prove2me | solution 1 for Formalism.MainNotions.J.loc_tr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:42:30.932347+00:00
-- url     : https://prove2.me/submissions/31f272f7-eeef-4a22-aaca-94ecb70fecd6

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_SfromGLa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
namespace Formalism.MainNotions.J
theorem _root_.solution (φ : V ≃ₗ[K] V') (p : Ideal (𝓞 K)) (M : Submodule (𝓞 K) V) :
    loc (K := K) p (latMap φ M) = latMap φ (loc (K := K) p M) := by
  ext y
  rw [mem_tr]
  constructor
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, ?_⟩
    rw [mem_tr] at h
    have e : φ.symm (s • y) = s • φ.symm y := by
      rw [← algebraMap_smul K s y, map_smul, algebraMap_smul]
    rwa [e] at h
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, ?_⟩
    rw [mem_tr]
    have e : φ.symm (s • y) = s • φ.symm y := by
      rw [← algebraMap_smul K s y, map_smul, algebraMap_smul]
    rwa [e]
end Formalism.MainNotions.J
