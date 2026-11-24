-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.geom_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:42:52.80636+00:00
-- url     : https://prove2.me/submissions/fb087019-0406-48bf-8d03-7e0b52e8fa43

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLocFOfVdZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldFurther
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlphaNOfVdZeroUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
theorem _root_.solution {x : ℝ} (hx : |x| ≤ 1 / 2) (N : ℕ) :
    0 ≤ ∑ l ∈ Finset.range N, x ^ l ∧ ∑ l ∈ Finset.range N, x ^ l ≤ 4 := by
  have hxa := abs_le.mp hx
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1] at hxa
    linarith [hxa.2]
  have hxN : |x ^ N| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg x) (by linarith)
  have hxN' := abs_le.mp hxN
  rw [geom_sum_eq hx1 N]
  constructor
  · exact div_nonneg_of_nonpos (by linarith [hxN'.2]) (by linarith [hxa.2])
  · rw [div_le_iff_of_neg (by linarith [hxa.2])]
    linarith [hxa.2, hxN'.1]
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
