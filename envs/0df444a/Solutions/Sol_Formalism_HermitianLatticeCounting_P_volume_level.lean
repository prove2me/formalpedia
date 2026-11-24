-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.volume_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:54:49.320941+00:00
-- url     : https://prove2.me/submissions/d27da873-3f8d-4e42-b441-8d7d0ec1f850

import Definitions.Def_Formalism_FlagUnipotentLattices_CuspidalityThreshold
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_OperatorHilbertSchmidtNorm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_ydat_facts
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_Final_h1
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_Final_h2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory NumberField
open scoped ComplexOrder
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : VolLevel := by
  intro C n f rd g b volG volK hn hf hrd hg hb hvK hG hK
  obtain ⟨hY2, -, -, -, hgY, -⟩ := ydat_facts hn hf hrd hg hb
  have hY0 : 0 < Ydat n f rd g b := by linarith
  have e : Ydat n f rd g b ^ ((C + 2) * (n : ℝ) ^ 2 * f)
      = Ydat n f rd g b ^ (C * (n : ℝ) ^ 2 * f) * Ydat n f rd g b ^ (2 * n ^ 2 * f) := by
    rw [← Real.rpow_natCast (Ydat n f rd g b) (2 * n ^ 2 * f), ← Real.rpow_add hY0]
    congr 1; push_cast; ring
  rw [e, div_eq_mul_inv]
  have h1 : volK⁻¹ ≤ Ydat n f rd g b ^ (2 * n ^ 2 * f) :=
    hK.trans (pow_le_pow_left₀ (by linarith) hgY _)
  have h2 : 0 ≤ volK⁻¹ := by positivity
  have h3 : 0 ≤ Ydat n f rd g b ^ (C * (n : ℝ) ^ 2 * f) := (Real.rpow_pos_of_pos hY0 _).le
  calc volG * volK⁻¹ ≤ Ydat n f rd g b ^ (C * (n : ℝ) ^ 2 * f) * volK⁻¹ := by gcongr
    _ ≤ _ := by gcongr
end Formalism.HermitianLatticeCounting.P
