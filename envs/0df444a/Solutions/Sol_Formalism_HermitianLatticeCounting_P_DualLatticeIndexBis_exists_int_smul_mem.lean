-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.exists_int_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:12.412414+00:00
-- url     : https://prove2.me/submissions/ae09de71-b18f-4713-8fda-0600d934a9ce

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
open Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
namespace Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
theorem _root_.solution {E U : Type} [Field E] [NumberField E] [AddCommGroup U]
    [Module (𝓞 E) U] (L : Submodule (𝓞 E) U) (x : U) (d : 𝓞 E) (hd : d ≠ 0) (hx : d • x ∈ L) :
    ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ L := by
  have h1 := Ideal.absNorm_mem (Ideal.span {d})
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h1
  refine ⟨(Ideal.absNorm (Ideal.span {d}) : ℕ), ?_, ?_⟩
  · have : Ideal.absNorm (Ideal.span {d}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hd
    exact_mod_cast this
  · rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E), ← hc, mul_smul]
    exact L.smul_mem c hx
end Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
