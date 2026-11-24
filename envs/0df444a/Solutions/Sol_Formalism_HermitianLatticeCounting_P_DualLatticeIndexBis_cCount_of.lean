-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.cCount_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:04.213995+00:00
-- url     : https://prove2.me/submissions/9e8d597b-cc65-409f-86be-26fbbfd700e6

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_cSet_count

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
theorem _root_.solution (E : Type) [Field E] [NumberField E] (f D : ℕ) (e : ℝ)
    (hT : Nat.card (NumberField.Units.torsion E) ≤ 8 * f ^ 2)
    (hS : {I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D}.Finite ∧
      (({I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D}.ncard : ℕ) : ℝ) ≤ (D : ℝ) ^ e) :
    (cSet E D).Finite ∧ (((cSet E D).ncard : ℕ) : ℝ) ≤ 8 * (f : ℝ) ^ 2 * (D : ℝ) ^ (2 * e) := by
  obtain ⟨h1, h2⟩ := cSet_count E D hS.1
  refine ⟨h1, ?_⟩
  have hT' : ((Nat.card (NumberField.Units.torsion E) : ℕ) : ℝ) ≤ 8 * (f : ℝ) ^ 2 := by
    exact_mod_cast hT
  calc (((cSet E D).ncard : ℕ) : ℝ)
      ≤ ((Nat.card (NumberField.Units.torsion E) *
          {I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D}.ncard ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast h2
    _ = ((Nat.card (NumberField.Units.torsion E) : ℕ) : ℝ) *
          (({I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D}.ncard : ℕ) : ℝ) ^ 2 := by
        push_cast; ring
    _ ≤ 8 * (f : ℝ) ^ 2 * ((D : ℝ) ^ e) ^ 2 := by
        gcongr
        exact hS.2
    _ = 8 * (f : ℝ) ^ 2 * (D : ℝ) ^ (2 * e) := by
        rw [← Real.rpow_natCast ((D : ℝ) ^ e) 2, ← Real.rpow_mul (Nat.cast_nonneg D), mul_comm e]
        norm_num
end Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
