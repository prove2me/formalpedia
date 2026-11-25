-- Prove2me | solution 1 for Formalism.HermitianLattices.Final.lattice_and_zeta_arithmetic_estimates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:18:23.696826+00:00
-- url     : https://prove2.me/submissions/59273f88-2250-46c3-92b1-6d848eeeb1a8

import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_TeichmullerUnitAllPrimes
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HadamardUnitDiagonalDetLeOne
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound
import Definitions.Def_Formalism_GL3MeanSquares_FinalB
import Theorems.Thm_Formalism_HermitianLattices_LatticeEstimates_L1LeSqrtCardOfL2_statement
import Theorems.Thm_Formalism_HermitianLattices_LatticeEstimates_block_cauchy_schwarz
import Theorems.Thm_Formalism_HermitianLattices_LatticeEstimates_column_other_entries
import Theorems.Thm_Formalism_HermitianLattices_LatticeEstimates_fifth_zeta_arithmetic_bound
import Theorems.Thm_Formalism_HermitianLattices_LatticeEstimates_fourth_zeta_arithmetic_bound
import Theorems.Thm_Formalism_HermitianLattices_LatticeEstimates_hadamard_inequality_bound
import Theorems.Thm_Formalism_HermitianLattices_LatticeEstimates_inverse_norm_le_of_integer_inner
import Theorems.Thm_Formalism_HermitianLattices_LatticeEstimates_mean_value_inequality_radial
import Theorems.Thm_Formalism_HermitianLattices_LatticeEstimates_moduli_entry_bound
import Theorems.Thm_Formalism_HermitianLattices_LatticeEstimates_moduli_intermediate_bound
import Theorems.Thm_Formalism_HermitianLattices_LatticeEstimates_moduli_minimum_bound
import Theorems.Thm_Formalism_HermitianLattices_LatticeEstimates_third_zeta_arithmetic_bound
import Theorems.Thm_Formalism_HermitianLattices_LatticeEstimates_third_zeta_minor_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Final
namespace Formalism.HermitianLattices.Final
theorem _root_.solution :
    Formalism.HermitianLattices.LatticeEstimates.Ms_min ∧
    Formalism.HermitianLattices.LatticeEstimates.Ms_entry ∧
    Formalism.HermitianLattices.LatticeEstimates.Ms_hadamard ∧
    Formalism.HermitianLattices.LatticeEstimates.Ms_between ∧
    Formalism.HermitianLattices.LatticeEstimates.MeanValueInequalityRadial ∧
    Formalism.HermitianLattices.LatticeEstimates.WeightedCauchySchwarz ∧
    Formalism.HermitianLattices.LatticeEstimates.L1LeSqrtCardOfL2 ∧
    Formalism.HermitianLattices.LatticeEstimates.UnitaryMinorNormLeOne ∧
    Formalism.HermitianLattices.LatticeEstimates.InverseNormLeOfIntegerInner ∧
    Formalism.HermitianLattices.LatticeEstimates.InterlacingLogSquareBound ∧
    Formalism.HermitianLattices.LatticeEstimates.MuMaxBoundOfAntitoneWeight ∧
    Formalism.HermitianLattices.LatticeEstimates.AntitoneWeightLogBoundExists ∧
    Formalism.HermitianLattices.LatticeEstimates.Col_other :=
  ⟨Formalism.HermitianLattices.LatticeEstimates.moduli_minimum_bound,
   Formalism.HermitianLattices.LatticeEstimates.moduli_entry_bound,
   Formalism.HermitianLattices.LatticeEstimates.hadamard_inequality_bound,
   Formalism.HermitianLattices.LatticeEstimates.moduli_intermediate_bound,
   Formalism.HermitianLattices.LatticeEstimates.mean_value_inequality_radial,
   Formalism.HermitianLattices.LatticeEstimates.block_cauchy_schwarz,
   Formalism.HermitianLattices.LatticeEstimates.L1LeSqrtCardOfL2_statement,
   Formalism.HermitianLattices.LatticeEstimates.third_zeta_minor_bound,
   Formalism.HermitianLattices.LatticeEstimates.inverse_norm_le_of_integer_inner,
   Formalism.HermitianLattices.LatticeEstimates.third_zeta_arithmetic_bound,
   Formalism.HermitianLattices.LatticeEstimates.fourth_zeta_arithmetic_bound,
   Formalism.HermitianLattices.LatticeEstimates.fifth_zeta_arithmetic_bound,
   Formalism.HermitianLattices.LatticeEstimates.column_other_entries⟩
end Formalism.HermitianLattices.Final
