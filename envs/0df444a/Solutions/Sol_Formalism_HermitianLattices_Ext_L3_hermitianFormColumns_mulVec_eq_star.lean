-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.hermitianFormColumns.mulVec_eq_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:32:00.221128+00:00
-- url     : https://prove2.me/submissions/a2d7144c-4da7-4868-b22d-1b5ea43477bf

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEighth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences reductionMapsOfForms
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m : Type} [Fintype m] [DecidableEq m]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable {A : Type*} [CommRing A] [StarRing A]
namespace Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
theorem _root_.solution {H : Matrix m m A} (hH : Hᴴ = H) (x : m → A) :
    H *ᵥ x = star (star x ᵥ* H) := by
  ext i
  have hHij : ∀ j, star (H j i) = H i j := fun j => by
    rw [← Matrix.conjTranspose_apply, hH]
  simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Pi.star_apply, star_sum, star_mul',
    star_star, hHij]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
end Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
