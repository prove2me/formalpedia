-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.exists_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:13.766463+00:00
-- url     : https://prove2.me/submissions/9af00c82-1108-4d52-b298-0436576306b8

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_exists_smul_mem_of_span

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
theorem _root_.solution {E U : Type} [Field E] [NumberField E] [AddCommGroup U] [Module E U]
    [Module (𝓞 E) U] [IsScalarTower (𝓞 E) E U] (N M : Submodule (𝓞 E) U)
    (hN : Submodule.span E (N : Set U) = ⊤) (hM : M.FG) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ x ∈ M, d • x ∈ N := by
  induction M, hM using Submodule.fg_induction with
  | singleton x =>
    obtain ⟨d, hd, hdx⟩ := exists_smul_mem_of_span N hN x
    refine ⟨d, hd, fun y hy => ?_⟩
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [smul_comm]
    exact N.smul_mem r hdx
  | sup M₁ M₂ _ _ h₁ h₂ =>
    obtain ⟨d, hd, hdx⟩ := h₁
    obtain ⟨e, he, hey⟩ := h₂
    refine ⟨d * e, mul_ne_zero hd he, fun z hz => ?_⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N.smul_mem e (hdx x hx)
    · rw [mul_smul]; exact N.smul_mem d (hey y hy)
end Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
