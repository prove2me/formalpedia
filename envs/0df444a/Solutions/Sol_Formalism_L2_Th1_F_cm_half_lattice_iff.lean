-- Prove2me | solution 1 for Formalism.L2.Th1.F.cm_half_lattice_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:26:13.20784+00:00
-- url     : https://prove2.me/submissions/ce6b7dec-7779-4ecf-b0d5-b41db895f99d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_CMQuasiPeriodConst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_CmAlternatingForm
import Theorems.Thm_Formalism_L2_Th1_F_Cm1_coord
import Theorems.Thm_Formalism_L2_Th1_F_Cm1_mem_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Cm1
namespace Formalism.L2.Th1.F
theorem _root_.solution : CMHalfLatticeIff := by
  intro a b d ha hd hodd m n
  rw [Formalism.L2.Th1.F.Cm1.mem_iff a b d ha hd]
  constructor
  · rintro ⟨x, y, hxy⟩
    obtain ⟨h1, h2⟩ := Formalism.L2.Th1.F.Cm1.coord a b d ha hd ((x : ℝ) - (m : ℝ) / 2)
      ((y : ℝ) - (n : ℝ) * (a : ℝ) / 2) (by push_cast; linear_combination hxy)
    have hm : (m : ℝ) = 2 * x := by linarith
    have hm' : m = 2 * x := by exact_mod_cast hm
    have hn : (n : ℝ) * a = 2 * y := by linarith
    have hn' : n * (a : ℤ) = 2 * y := by exact_mod_cast hn
    obtain ⟨k, hk⟩ := hodd
    have hkZ : (a : ℤ) = 2 * k + 1 := by exact_mod_cast hk
    exact ⟨⟨x, by omega⟩, ⟨y - n * k, by linear_combination hn' - n * hkZ⟩⟩
  · rintro ⟨⟨r, rfl⟩, ⟨s, rfl⟩⟩
    exact ⟨r, s * a, by push_cast; ring⟩
end Formalism.L2.Th1.F
