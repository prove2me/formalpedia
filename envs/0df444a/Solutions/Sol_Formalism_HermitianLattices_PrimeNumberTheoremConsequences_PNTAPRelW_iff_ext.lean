-- Prove2me | solution 1 for Formalism.HermitianLattices.PrimeNumberTheoremConsequences.PNTAPRelW_iff_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:58.380265+00:00
-- url     : https://prove2.me/submissions/64bdad98-6568-4349-8c1e-1acad5a67361

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimePairOfPrimeNumberTheoremInProgressions
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqFinal
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_PrimePairOfBoxAndWeakMeanSquareHypotheses
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BoxCountOfZeroDensity
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BoxCountAllStatement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_MeanSquareOfPrimeNumberTheorem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.PrimeNumberTheoremConsequences
namespace Formalism.HermitianLattices.PrimeNumberTheoremConsequences
theorem _root_.solution : PNTAPRelW ↔ Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.PNTAPRelW := Iff.rfl
end Formalism.HermitianLattices.PrimeNumberTheoremConsequences
