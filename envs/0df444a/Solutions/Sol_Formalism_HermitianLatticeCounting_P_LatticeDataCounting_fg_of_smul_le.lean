-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.LatticeDataCounting.fg_of_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:32.409802+00:00
-- url     : https://prove2.me/submissions/08d892b4-fbdb-4655-a0e0-1e3abf0d89b1

import Definitions.Def_Formalism_FlagUnipotentLattices_OmSumLong
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeDataCounting

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
open Formalism.HermitianLatticeCounting.P.LatticeDataCounting
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]
namespace Formalism.HermitianLatticeCounting.P.LatticeDataCounting
theorem _root_.solution (A B : Submodule (𝓞 E) V) (hA : A.FG) (d : 𝓞 E) (hd : d ≠ 0)
    (hdB : ∀ x ∈ B, d • x ∈ A) : B.FG := by
  have : Module.IsTorsionFree (𝓞 E) V := Module.IsTorsionFree.trans E
  have hinj : Function.Injective (LinearMap.lsmul (𝓞 E) V d) := by
    intro x y hxy
    exact smul_right_injective V hd hxy
  apply Submodule.fg_of_fg_map_injective _ hinj
  have hN : IsNoetherian (𝓞 E) A := isNoetherian_of_fg_of_noetherian A hA
  apply isNoetherian_submodule.mp hN
  rintro _ ⟨x, hx, rfl⟩
  exact hdB x hx
end Formalism.HermitianLatticeCounting.P.LatticeDataCounting
