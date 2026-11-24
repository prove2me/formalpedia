-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.colon_ideal_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:42.289951+00:00
-- url     : https://prove2.me/submissions/ddd98cc4-d845-4a76-8bab-42103da40000

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted

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
theorem _root_.solution : ColonNorm := by
  intro E _ _ L _ _ Lam₁ y
  set aa : Ideal (𝓞 E) := Lam₁.comap (LinearMap.toSpanSingleton (𝓞 E) L y) with haa
  have hdvd : Ideal.absNorm aa ∣ Lam₁.toAddSubgroup.index := by
    have e1 : Ideal.absNorm aa = (Submodule.toAddSubgroup aa).index := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
    have e2 : Submodule.toAddSubgroup aa =
        Lam₁.toAddSubgroup.comap (LinearMap.toSpanSingleton (𝓞 E) L y).toAddMonoidHom := by
      ext a; rfl
    rw [e1, e2, AddSubgroup.index_comap]
    exact AddSubgroup.relIndex_dvd_index_of_normal _ _
  refine ⟨hdvd, fun h0 => ⟨?_, Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd⟩⟩
  rcases Nat.eq_zero_or_pos (Ideal.absNorm aa) with h | h
  · rw [h] at hdvd; exact absurd (Nat.eq_zero_of_zero_dvd hdvd) h0
  · exact h
end Formalism.HermitianLatticeCounting.P
