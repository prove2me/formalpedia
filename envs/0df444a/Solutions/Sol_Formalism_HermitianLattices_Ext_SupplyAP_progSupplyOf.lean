-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.SupplyAP.progSupplyOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:09:12.30074+00:00
-- url     : https://prove2.me/submissions/55c68b67-1acf-4848-a814-01dedf91fbe1

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffPsi
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffConsts
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffExc
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_PsiAPLeCount
import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffFinal
import Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_constsOf
import Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_psiAPLowerOf
import Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_psiAP_le_count


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.ZeroFreeDirichlet
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP
namespace Formalism.HermitianLattices.Ext.SupplyAP
theorem _root_.solution (A : ℕ) (hA : ExcBoundAt A) : ∃ K : ℝ, 4 ≤ K ∧ ∀ (m a : ℕ) (x : ℝ), 1 ≤ m → Nat.Coprime a m →
    K * Real.log (3 * m) ^ 2 ≤ Real.log x → Real.sqrt x ≤ ((primesAP m a x).card : ℝ) := by
  obtain ⟨c, c₀, C, hc, hc₀, hC, hlow⟩ := psiAPLowerOf A hA
  obtain ⟨K, hK, hsz⟩ := constsOf A c c₀ C hc hc₀ hC
  refine ⟨K, hK, fun m a x hm ha hx => ?_⟩
  rcases le_or_gt x 0 with hx0 | hx0
  · rw [Real.sqrt_eq_zero'.mpr hx0]; positivity
  obtain ⟨h4, hrange, hmain⟩ := hsz m x hm hx0 hx
  have hψ := hlow m a x hm ha hx0 h4 hrange
  have hx1 : 1 ≤ x := by
    by_contra h
    push Not at h
    have := Real.log_nonpos hx0.le h.le
    linarith
  have hcnt := psiAP_le_count m a x hx1
  have hLpos : 0 < Real.log x := by linarith
  have h2 : Real.log x * Real.sqrt x ≤ Real.log x * ((primesAP m a x).card : ℝ) := by
    nlinarith
  exact le_of_mul_le_mul_left h2 hLpos
end Formalism.HermitianLattices.Ext.SupplyAP
