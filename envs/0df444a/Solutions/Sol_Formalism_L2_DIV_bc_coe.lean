-- Prove2me | solution 1 for Formalism.L2.DIV.bc_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:48.91559+00:00
-- url     : https://prove2.me/submissions/1a059e9e-00c3-4c06-84e4-b0818c2303c6

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
namespace Formalism.L2.DIV
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (φ : A →+* B) (g : GL (Fin n) A) :
    ((Formalism.UG.bc φ g : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) = (g : Matrix (Fin n) (Fin n) A).map φ := rfl
end Formalism.L2.DIV
