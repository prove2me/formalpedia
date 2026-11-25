-- Prove2me | solution 1 for Formalism.DivisionValues.shift_idx_smulLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:06:08.893818+00:00
-- url     : https://prove2.me/submissions/8da01cf4-b21a-45e9-bada-e9d30a675d2a

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
import Theorems.Thm_Formalism_DivisionValues_localizationAt_smul
import Theorems.Thm_Formalism_DivisionValues_shift_smulLat_span
import Theorems.Thm_Formalism_DivisionValues_shift_vw_pow
import Theorems.Thm_Formalism_DivisionValues_idxChange_act_diagonal
import Theorems.Thm_Formalism_DivisionValues_idxChange_at
import Theorems.Thm_Formalism_DivisionValues_idxChange_lidx_congr
import Theorems.Thm_Formalism_DivisionValues_idxChange_locS_of_le
import Theorems.Thm_Formalism_DivisionValues_semilocal_basis_exists
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_hcompl_le


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
variable {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ}
namespace Formalism.DivisionValues
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (N : Submodule (𝓞 K) (Fin d → K))
    (hN : Submodule.IsLattice K N) (a : K) (ha : a ≠ 0) :
    idx w N (smulLat a N) = (d : ℤ) * vw w a := by
  obtain ⟨f, hf, hl⟩ := semilocal_basis_exists K d N hN w
  have h1 : Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Submodule.span (𝓞 K) (Set.range f)) =
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N := by
    unfold Formalism.HermitianLatticesTheory.loc at hl
    unfold Formalism.HermitianLatticesTheory.localization₂
    exact idxChange_locS_of_le (Formalism.HermitianLatticesTheory.locBasic_hcompl_le (K := K) w.asIdeal) hl
  have hdet : (Matrix.diagonal fun _ : Fin d => a).det = a ^ d := by
    simp [Matrix.det_diagonal]
  have h2 : Formalism.HermitianLatticesTheory.localization₂ w.asIdeal
      (Submodule.span (𝓞 K) (Set.range (idxChangeAct f (Matrix.diagonal fun _ : Fin d => a)))) =
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (smulLat a N) := by
    rw [idxChange_act_diagonal, ← shift_smulLat_span, localizationAt_smul w a ha, h1,
      ← localizationAt_smul w a ha]
  have h3 := idxChange_at w (smulLat a N) f hf (Matrix.diagonal fun _ : Fin d => a)
    (by rw [hdet]; exact pow_ne_zero d ha) h2
  rw [hdet, shift_vw_pow w a ha] at h3
  rw [← h3]
  unfold idx
  exact idxChange_lidx_congr w.asIdeal h1.symm rfl
end Formalism.DivisionValues
