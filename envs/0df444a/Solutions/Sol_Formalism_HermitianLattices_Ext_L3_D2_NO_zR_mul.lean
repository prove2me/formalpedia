-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.NO.zR_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:46:33.475954+00:00
-- url     : https://prove2.me/submissions/023e0624-297e-4673-84e3-466cbcdde68d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.D2.NO
namespace Formalism.HermitianLattices.Ext.L3.D2.NO
theorem _root_.solution (𝔭 : Ideal (𝓞 F)) (z w : K) :
    zR 𝔭 (z * w) = (zR 𝔭 w).map (AddMonoidHom.mulLeft z) := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨w * b, ⟨b, hb, rfl⟩, (mul_assoc z w b).symm⟩
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨b, hb, mul_assoc z w b⟩
end Formalism.HermitianLattices.Ext.L3.D2.NO
