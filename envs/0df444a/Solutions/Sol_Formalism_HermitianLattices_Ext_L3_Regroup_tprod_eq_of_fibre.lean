-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.Regroup.tprod_eq_of_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:35.689863+00:00
-- url     : https://prove2.me/submissions/ebd20185-a67f-46e7-9612-ed5630c520ee

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LValEtaEqLValEtaF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
open Formalism.HermitianLattices.Ext.L3.Regroup
namespace Formalism.HermitianLattices.Ext.L3.Regroup
theorem _root_.solution {α β : Type*} {f : α → ℝ} (π : α → β) {g : β → ℝ} (hf : Multipliable f)
    (hg : ∀ b, HasProd (fun c : {x // π x = b} => f c.1) (g b)) : ∏' a, f a = ∏' b, g b := by
  have h1 : HasProd (fun p : (Σ b : β, {x // π x = b}) => f (Equiv.sigmaFiberEquiv π p))
      (∏' a, f a) := (Equiv.sigmaFiberEquiv π).hasProd_iff.2 hf.hasProd
  exact (HasProd.sigma h1 hg).tprod_eq.symm
end Formalism.HermitianLattices.Ext.L3.Regroup
