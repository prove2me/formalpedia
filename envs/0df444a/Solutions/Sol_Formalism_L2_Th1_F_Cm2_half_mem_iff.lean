-- Prove2me | solution 1 for Formalism.L2.Th1.F.Cm2.half_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:24:03.672331+00:00
-- url     : https://prove2.me/submissions/d1a81a39-c2d8-4815-a616-90541ce6ac70

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_CmAlternatingForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_FormEvenIff

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
open Formalism.L2.Th1.F.Cm2
open Cm1
namespace Formalism.L2.Th1.F.Cm2
theorem _root_.solution (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (m n : ℤ) :
    ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d) / 2 ∈ (cmPair a b d ha hd).lattice ↔ Even m ∧ Even n := by
  rw [PeriodPair.mem_lattice]
  constructor
  · rintro ⟨p, q, hpq⟩
    change (p : ℂ) * (a : ℂ) + (q : ℂ) * cmTheta b d = _ at hpq
    have hli := (cmPair a b d ha hd).indep
    rw [LinearIndependent.pair_iff] at hli
    obtain ⟨h1, h2⟩ := hli (2 * (p : ℝ) - m) (2 * (q : ℝ) - n) (by
      change ((2 * (p : ℝ) - m : ℝ)) • (a : ℂ) + ((2 * (q : ℝ) - n : ℝ)) • cmTheta b d = 0
      simp only [Complex.real_smul]
      push_cast
      linear_combination 2 * hpq)
    have hm : m = 2 * p := by
      have : (m : ℝ) = 2 * p := by linarith
      exact_mod_cast this
    have hn : n = 2 * q := by
      have : (n : ℝ) = 2 * q := by linarith
      exact_mod_cast this
    exact ⟨⟨p, by omega⟩, ⟨q, by omega⟩⟩
  · rintro ⟨⟨r, rfl⟩, ⟨s, rfl⟩⟩
    refine ⟨r, s, ?_⟩
    change (r : ℂ) * (a : ℂ) + (s : ℂ) * cmTheta b d = _
    push_cast
    ring
end Formalism.L2.Th1.F.Cm2
