-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.integralBasisSpans.form_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:46.095532+00:00
-- url     : https://prove2.me/submissions/ad29adaa-4502-4663-85c1-c3345bed6f4d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.integralBasisSpans
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable [Fact (IsFixF K F)]
namespace Formalism.HermitianLattices.Ext.L3.integralBasisSpans
theorem _root_.solution {A : Type*} [CommRing A] [StarRing A] (M N : Matrix κ κ A) (u v : κ → A) :
    star (M *ᵥ u) ⬝ᵥ (N *ᵥ (M *ᵥ v)) = star u ⬝ᵥ ((Mᴴ * N * M) *ᵥ v) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
end Formalism.HermitianLattices.Ext.L3.integralBasisSpans
