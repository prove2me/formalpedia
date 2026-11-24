-- Prove2me | solution 1 for Formalism.NG.genfin_ker_map_uncurry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:34:03.342511+00:00
-- url     : https://prove2.me/submissions/292f58bd-deba-4276-b446-6a16155b3dab

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_StatementG
import Definitions.Def_Formalism_CharacterColumnKernels_StatementX
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenRelMapApply
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenFin
import Theorems.Thm_Formalism_NG_genfin_uncurry_relMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
variable {R : Type*} [Ring R] {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {m g d : Type} [Fintype m] [Fintype g] [DecidableEq g] [Fintype d] [DecidableEq d]
  (ρ : R →+* Matrix d d O) [SMulCommClass R O (LatQ O d ρ)]
namespace Formalism.NG
theorem _root_.solution (P : Matrix m g R) :
    (LinearMap.ker (relMap O (LatQ O d ρ) P)).map (uncurryEquiv (g := g) ρ).toLinearMap =
      LinearMap.ker (relMap O (KO O) (fun (p : m × d) (q : g × d) => ρ (P p.1 q.1) p.2 q.2)) := by
  ext w
  rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro h
    have := genfin_uncurry_relMap ρ P ((uncurryEquiv ρ).symm w)
    rw [h, map_zero, LinearEquiv.apply_symm_apply] at this
    exact this.symm
  · intro h
    have := genfin_uncurry_relMap ρ P ((uncurryEquiv ρ).symm w)
    rw [LinearEquiv.apply_symm_apply, h] at this
    exact (uncurryEquiv ρ).map_eq_zero_iff.mp this
end Formalism.NG
