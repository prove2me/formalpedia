-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.prodLower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:50.329894+00:00
-- url     : https://prove2.me/submissions/10780324-707b-4362-8afe-1765154ea94d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExistsFarFromPoints
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_RootNorm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_HDSucc
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_Turan2Main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
theorem _root_.solution (n : ℕ) (z : Fin n → ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ξ : ℂ) (hξ : ‖ξ‖ = ρ⁻¹) :
    ρ⁻¹ ^ n * ∏ i, |ρ - ‖z i‖| ≤ ‖∏ i, (1 - z i * ξ)‖ := by
  have hfac : ∀ i, ρ⁻¹ * |ρ - ‖z i‖| ≤ ‖1 - z i * ξ‖ := by
    intro i
    have h1 : ρ⁻¹ * (ρ - ‖z i‖) = 1 - ‖z i‖ * ρ⁻¹ := by
      rw [mul_sub, inv_mul_cancel₀ hρ.ne']; ring
    have h2 : ρ⁻¹ * |ρ - ‖z i‖| = |1 - ‖z i‖ * ρ⁻¹| := by
      rw [← h1, abs_mul, abs_of_pos (inv_pos.mpr hρ)]
    rw [h2]
    calc |1 - ‖z i‖ * ρ⁻¹| = |‖(1 : ℂ)‖ - ‖z i * ξ‖| := by rw [norm_one, norm_mul, hξ]
      _ ≤ ‖1 - z i * ξ‖ := abs_norm_sub_norm_le _ _
  calc ρ⁻¹ ^ n * ∏ i, |ρ - ‖z i‖| = ∏ i, (ρ⁻¹ * |ρ - ‖z i‖|) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ i, ‖1 - z i * ξ‖ :=
        Finset.prod_le_prod (fun i _ => mul_nonneg (inv_nonneg.mpr hρ.le) (abs_nonneg _))
          (fun i _ => hfac i)
    _ = ‖∏ i, (1 - z i * ξ)‖ := (norm_prod Finset.univ _).symm
end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
