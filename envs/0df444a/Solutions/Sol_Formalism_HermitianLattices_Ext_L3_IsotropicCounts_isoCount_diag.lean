-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.IsotropicCounts.isoCount_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:26:14.317267+00:00
-- url     : https://prove2.me/submissions/76695306-c2c1-48f8-8e9b-86541226efbc

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MapMkConjTranspose
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsoCountOneInert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IsotropicCounts_isoCount_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IsotropicCounts_isoCount_eq_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.IsotropicCounts
open Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [hFF : Fact (IsFixF K F)] {m : ℕ}
namespace Formalism.HermitianLattices.Ext.L3.IsotropicCounts
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (u : Fin m → 𝓞 K) (hu : ∀ i, conjO K (u i) = u i)
    (hunit : ∀ i, Ideal.span {u i} ⊔ extP K 𝔭 = ⊤) (k : ℕ) :
    (isoCount 𝔭 (k + 1) (diagonal u) : ℝ) =
      (Ideal.absNorm 𝔭 : ℝ) ^ ((k + 1) * m ^ 2) * alphaStd K 𝔭 m := by
  have hg : (diagonal u)ᴴ = diagonal u := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    exact hu i
  have hdet : Ideal.span {(diagonal u).det} ⊔ extP K 𝔭 = ⊤ := by
    rw [Matrix.det_diagonal, ← Ideal.prod_span_singleton]
    exact Ideal.prod_sup_eq_top fun i _ => hunit i
  rw [isoCount_eq_pow hK h𝔭 (diagonal u) hg hdet k]
  push_cast
  rw [isoCount_one hK h𝔭 u hu hunit]
  ring
end Formalism.HermitianLattices.Ext.L3.IsotropicCounts
