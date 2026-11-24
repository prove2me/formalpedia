-- Prove2me | solution 1 for Formalism.L2.SG.MassRatio.formsEq_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:17:47.643669+00:00
-- url     : https://prove2.me/submissions/00813ab2-e5b8-4325-9723-f4693ff83a59

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_MassRatio

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.MassRatio
namespace Formalism.L2.SG.MassRatio
theorem _root_.solution (hD : DegEq) (hS : DiscSq) (hL : EulerEq) : FormsEq := by
  intro F E _ _ _ _ _ _ hFE M hM
  have hf : fF F = Formalism.HermitianLatticesTheory.fDeg E := hD F E hFE
  have hd : |((discr E : ℤ) : ℝ)| = dF F ^ 2 := hS F E hFE
  have hl : lText F E M = Formalism.HermitianLatticesTheory.lValEta E M := hL F E hFE M hM
  have h0 : (0 : ℝ) ≤ dF F := abs_nonneg _
  have hfpos : 0 < fF F := Module.finrank_pos
  have hfR : (fF F : ℝ) ≠ 0 := by exact_mod_cast hfpos.ne'

  have hv : Formalism.HermitianLatticesTheory.vInv E = vF F := by
    unfold Formalism.HermitianLatticesTheory.vInv vF
    rw [hd, ← hf, ← Real.rpow_natCast (dF F) 2, ← Real.rpow_mul h0]
    congr 2
    push_cast
    field_simp

  have h2v : (2 * vF F) ^ fF F = dF F := by
    unfold vF
    rw [mul_div_cancel₀ _ (two_ne_zero), ← Real.rpow_natCast, ← Real.rpow_mul h0,
      one_div_mul_cancel hfR, Real.rpow_one]
  unfold rText Formalism.HermitianLatticesTheory.massRatioRightSide
  rw [hv, ← hf, h2v, hl, Real.sqrt_eq_rpow, show (-(1 : ℝ) / 2) = -(1 / 2) by ring,
    Real.rpow_neg h0]
  ring
end Formalism.L2.SG.MassRatio
