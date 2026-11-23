-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BoxCube.absNorm_le_of_mem_ideal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:24.166351+00:00
-- url     : https://prove2.me/submissions/b3bb0322-da08-4aed-acf5-990785b3b491

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
theorem _root_.solution {b : Ideal (𝓞 F)} {n : 𝓞 F} (hn : n ∈ b) (h0 : n ≠ 0) :
    (Ideal.absNorm b : ℝ) ≤ (Ideal.absNorm (Ideal.span {n}) : ℝ) := by
  have h1 : Ideal.absNorm b ∣ Ideal.absNorm (Ideal.span {n}) :=
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem b).2 hn)
  have h2 : Ideal.absNorm (Ideal.span {n}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact h0
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h1
end Formalism.HermitianLattices.Ext.L3.BoxCube
