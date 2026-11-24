-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.dual_lattice_index
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:48.696531+00:00
-- url     : https://prove2.me/submissions/2c684bdb-7aba-4cb7-ae0b-33275b0fb922

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_relIndex_hermitian_dual_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : DualIndex := by
  intro E _ _ _ U _ _ _ _ _ h M N hnd hNM hM hN
  let _ : Module ℚ U := Module.compHom U (algebraMap ℚ E)
  have hq : ∀ (q : ℚ) (x : U), q • x = (algebraMap ℚ E q) • x := fun _ _ => rfl
  have : IsScalarTower ℚ E U := ⟨fun q e x => by rw [hq, Algebra.smul_def, mul_smul]⟩
  have : FiniteDimensional ℚ U := Module.Finite.trans E U
  exact DualLatticeIndexBis.relIndex_hermitian_dual_eq h M N hnd hNM hM hN
end Formalism.HermitianLatticeCounting.P
