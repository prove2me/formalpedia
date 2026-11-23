-- Prove2me | solution 1 for Formalism.UG.P.stdform_Q_dot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:16.433803+00:00
-- url     : https://prove2.me/submissions/5b791cb6-6ea5-49b1-bf3e-2a109cd3ab8e

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (M : Matrix n n ℂ) (y : n → ℂ) :
    stdformQ M y = (star y ⬝ᵥ (M *ᵥ y)).re := by
  unfold stdformQ
  congr 1
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def, mul_assoc]
end Formalism.UG.P
