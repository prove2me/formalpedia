-- Prove2me | solution 1 for Formalism.HermitianLattices.Final.model_cocycle_identities
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:03:26.928353+00:00
-- url     : https://prove2.me/submissions/c3011a49-7057-4ec8-91d2-f298530c706e

import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_TeichmullerUnitAllPrimes
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HadamardUnitDiagonalDetLeOne
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound
import Definitions.Def_Formalism_GL3MeanSquares_FinalB
import Theorems.Thm_Formalism_HermitianLattices_ModelCocycles_adjoint_additive
import Theorems.Thm_Formalism_HermitianLattices_ModelCocycles_adjoint_from_norm
import Theorems.Thm_Formalism_HermitianLattices_ModelCocycles_character_modulus_all
import Theorems.Thm_Formalism_HermitianLattices_ModelCocycles_character_power_formula
import Theorems.Thm_Formalism_HermitianLattices_ModelCocycles_cross_terms_vanish
import Theorems.Thm_Formalism_HermitianLattices_ModelCocycles_equal_powers_formula
import Theorems.Thm_Formalism_HermitianLattices_ModelCocycles_genus_one_character
import Theorems.Thm_Formalism_HermitianLattices_ModelCocycles_isotropic_vector_zero
import Theorems.Thm_Formalism_HermitianLattices_ModelCocycles_jets_of_log_unit
import Theorems.Thm_Formalism_HermitianLattices_ModelCocycles_model_cocycle_exponent
import Theorems.Thm_Formalism_HermitianLattices_ModelCocycles_model_cocycle_order_two
import Theorems.Thm_Formalism_HermitianLattices_ModelCocycles_split_component_vanishes
import Theorems.Thm_Formalism_HermitianLattices_ModelCocycles_teichmuller_unit_all_primes


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
    Formalism.HermitianLattices.ModelCocycles.AdjointFromNorm ∧
    Formalism.HermitianLattices.ModelCocycles.AdjointAdd ∧
    Formalism.HermitianLattices.ModelCocycles.SplitVanish ∧
    Formalism.HermitianLattices.ModelCocycles.IsotropicZero ∧
    Formalism.HermitianLattices.ModelCocycles.CrossTermsVanish ∧
    Formalism.HermitianLattices.ModelCocycles.EqualPowers ∧
    Formalism.HermitianLattices.ModelCocycles.JetsOfLogUnit ∧
    Formalism.HermitianLattices.ModelCocycles.GenusOneCharacter ∧
    Formalism.HermitianLattices.ModelCocycles.EpsTeichAll ∧
    Formalism.HermitianLattices.ModelCocycles.ChiPower ∧
    Formalism.HermitianLattices.ModelCocycles.ChiModulusAll ∧
    Formalism.HermitianLattices.ModelCocycles.ModelCocycleExponent ∧
    Formalism.HermitianLattices.ModelCocycles.ModelCocycleTwo :=
  ⟨Formalism.HermitianLattices.ModelCocycles.adjoint_from_norm,
   Formalism.HermitianLattices.ModelCocycles.adjoint_additive,
   Formalism.HermitianLattices.ModelCocycles.split_component_vanishes,
   Formalism.HermitianLattices.ModelCocycles.isotropic_vector_zero,
   Formalism.HermitianLattices.ModelCocycles.cross_terms_vanish,
   Formalism.HermitianLattices.ModelCocycles.equal_powers_formula,
   Formalism.HermitianLattices.ModelCocycles.jets_of_log_unit,
   Formalism.HermitianLattices.ModelCocycles.genus_one_character,
   Formalism.HermitianLattices.ModelCocycles.teichmuller_unit_all_primes,
   Formalism.HermitianLattices.ModelCocycles.character_power_formula,
   Formalism.HermitianLattices.ModelCocycles.character_modulus_all,
   Formalism.HermitianLattices.ModelCocycles.model_cocycle_exponent,
   Formalism.HermitianLattices.ModelCocycles.model_cocycle_order_two⟩
end Formalism.HermitianLattices.Final
