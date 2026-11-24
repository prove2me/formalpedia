-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.embedding_dual_compatible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:43.555531+00:00
-- url     : https://prove2.me/submissions/e0889afc-5f2a-456f-b681-823583bbf2da

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
theorem _root_.solution : IotaDual := by
  intro K U _ _ _ _ h O g L₀ L₀' ι' hg hsg hg0 hO hι hiso
  refine ⟨?_, ?_⟩
  · intro l' hl' x hx hxl
    obtain ⟨l, hl, hxl⟩ := hxl
    obtain ⟨t, ht, hiso'⟩ := hiso l' hl' x hx.2
    have hx' : x = ι' x - g • l := by rw [← hxl]; abel
    have h1 : h (ι' l') x = h (ι' l') (ι' x) - g * h (ι' l') l := by
      conv_lhs => rw [hx']
      rw [map_sub, LinearMap.map_smulₛₗ, starRingEnd_apply, hsg, smul_eq_mul]
    have key : h (l' - ι' l') x = g * (h (ι' l') l - t) := by
      rw [map_sub, LinearMap.sub_apply, h1]
      linear_combination (-1 : K) * hiso'
    rw [map_smul, LinearMap.smul_apply, key, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hg0, one_mul]
    exact O.sub_mem (hO _ (hι l' hl') _ hl) ht
  · rintro l' hl' ⟨l, hl, e⟩
    have h2 : l' - ι' l' = g • (-l) := by rw [smul_neg, ← e]; abel
    rw [h2, smul_smul, inv_mul_cancel₀ hg0, one_smul]
    exact L₀.neg_mem hl
end Formalism.HermitianLatticeCounting.P
