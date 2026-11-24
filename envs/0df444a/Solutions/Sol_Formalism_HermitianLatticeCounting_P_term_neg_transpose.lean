-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.term_neg_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:33.4038+00:00
-- url     : https://prove2.me/submissions/c21a4316-dc42-4042-8e69-e2a603b5c2ca

import Definitions.Def_Formalism_FlagUnipotentLattices_QDetNegTranspose
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LanglandsParameterEquivariant
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_AntisymmetrizedProductEqFactorialSmulQdet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S8 Formalism.REAL TensorProduct Finset
set_option linter.all false
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (y : ℂ) (a b : Fin n) :
    Tm (fun a b => -E b a) y a b = -Tm E (-y) b a := by
  simp only [Tm]
  by_cases h : a = b
  · subst h
    rw [if_pos rfl, if_pos rfl, map_neg]
    abel
  · rw [if_neg h, if_neg (Ne.symm h)]
    simp
end Formalism.HermitianLatticeCounting.P
