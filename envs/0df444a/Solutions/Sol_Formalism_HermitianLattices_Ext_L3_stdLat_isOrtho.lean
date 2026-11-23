-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.stdLat_isOrtho
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:12.453589+00:00
-- url     : https://prove2.me/submissions/63698eb4-1af4-4452-9db9-38cf038cd67d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_stdForm_apply
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) :
    Formalism.HermitianLatticesTheory.IsOrthoLattice (stdForm K n) (stdLat K n) n := by
  refine ⟨fun i => Pi.single i 1, ?_, ?_, rfl, ?_⟩
  · have := (Pi.basisFun K (Fin n)).linearIndependent
    rwa [show ⇑(Pi.basisFun K (Fin n)) = fun i => (Pi.single i 1 : Fin n → K) from
      funext fun i => Pi.basisFun_apply K (Fin n) i] at this
  · have := (Pi.basisFun K (Fin n)).span_eq
    rwa [show ⇑(Pi.basisFun K (Fin n)) = fun i => (Pi.single i 1 : Fin n → K) from
      funext fun i => Pi.basisFun_apply K (Fin n) i] at this
  · intro i j
    rw [stdForm_apply]
    by_cases hij : i = j
    · subst hij
      simp [Pi.single_apply]
    · simp [Pi.single_apply, hij, Ne.symm hij]
end Formalism.HermitianLattices.Ext.L3
