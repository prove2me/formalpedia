-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.int_on_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:14.146995+00:00
-- url     : https://prove2.me/submissions/74890ea7-7773-4cf0-92e9-6e84fda4291f

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
theorem _root_.solution {V ι : Type*} [AddCommGroup V] [Module ℚ V] (φ : V →ₗ[ℚ] ℚ) (v : ι → V) :
    (∀ y ∈ Submodule.span ℤ (Set.range v), ∃ n : ℤ, φ y = n) ↔ ∀ i, ∃ n : ℤ, φ (v i) = n := by
  constructor
  · intro h i
    exact h _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro h y hy
    induction hy using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨n, hn⟩ := hx
      obtain ⟨m, hm⟩ := hy
      exact ⟨n + m, by rw [map_add, hn, hm]; push_cast; rfl⟩
    | smul a x _ hx =>
      obtain ⟨n, hn⟩ := hx
      exact ⟨a * n, by rw [← Int.cast_smul_eq_zsmul ℚ a x, map_smul, hn]; push_cast; rfl⟩
end Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
