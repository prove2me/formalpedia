-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BoxCube.abs_sub_lt_of_floor_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:37.693517+00:00
-- url     : https://prove2.me/submissions/894e5b12-ec45-4b8a-b697-3f929e9b8a6a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormEqProdOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormLeOfMemIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxCube
open BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.BoxCube
theorem _root_.solution {δ a a' : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (ha' : 0 ≤ a')
    (h : ⌊a / δ⌋₊ = ⌊a' / δ⌋₊) : |a - a'| < δ := by
  have h1 := Nat.floor_le (div_nonneg ha hδ.le)
  have h2 := Nat.lt_floor_add_one (a / δ)
  have h3 := Nat.floor_le (div_nonneg ha' hδ.le)
  have h4 := Nat.lt_floor_add_one (a' / δ)
  rw [h] at h1 h2
  have h5 : a / δ - a' / δ < 1 := by linarith
  have h6 : a' / δ - a / δ < 1 := by linarith
  rw [← sub_div, div_lt_one hδ] at h5 h6
  rw [abs_lt]
  constructor <;> linarith
end Formalism.HermitianLattices.Ext.L3.BoxCube
