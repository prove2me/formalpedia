-- Prove2me | solution 1 for Formalism.DivisionValues.shift_existence
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:37.068417+00:00
-- url     : https://prove2.me/submissions/405ffa73-41b3-4208-ae72-ada70a1d356a

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TwistedLatticeNaturality
import Theorems.Thm_Formalism_DivisionValues_shift_exists_val
import Theorems.Thm_Formalism_DivisionValues_shift_shiftIdeal_ne_zero
import Theorems.Thm_Formalism_DivisionValues_shift_count_shiftIdeal
import Theorems.Thm_Formalism_DivisionValues_localizationAt_fractionalIdeal_smul_eq_smul
import Theorems.Thm_Formalism_DivisionValues_shift_idealSmul_lattice
import Theorems.Thm_Formalism_DivisionValues_shift_eq_of_locP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution : ShiftEx := by
  intro K _ _ _ d N hN σ hσ
  have hI := shift_shiftIdeal_ne_zero σ
  have hsh : IsShift N (Formalism.HermitianLatticesTheory.idealSmul (shiftIdeal σ : Submodule (𝓞 K) K) N) σ := by
    intro w
    obtain ⟨a, ha, hv⟩ := shift_exists_val w (-σ w)
    exact ⟨a, ha, hv, localizationAt_fractionalIdeal_smul_eq_smul _ hI w N ha (by rw [hv, shift_count_shiftIdeal σ hσ])⟩
  refine ⟨hsh, shift_idealSmul_lattice _ hI N hN, ?_⟩
  intro N' hN'
  apply shift_eq_of_locP
  intro w
  obtain ⟨a, ha, hv, hl⟩ := hN' w
  rw [hl]
  exact (localizationAt_fractionalIdeal_smul_eq_smul _ hI w N ha (by rw [hv, shift_count_shiftIdeal σ hσ])).symm
end Formalism.DivisionValues
