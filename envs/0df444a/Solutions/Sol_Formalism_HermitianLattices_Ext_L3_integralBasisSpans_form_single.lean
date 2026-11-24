-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.integralBasisSpans.form_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:45.485574+00:00
-- url     : https://prove2.me/submissions/6e368f23-9acd-4fbc-a1db-d6b222448944

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.integralBasisSpans
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable [Fact (IsFixF K F)]
namespace Formalism.HermitianLattices.Ext.L3.integralBasisSpans
theorem _root_.solution {A : Type*} [CommRing A] [StarRing A] (N : Matrix κ κ A) (i j : κ) :
    star (Pi.single i (1 : A)) ⬝ᵥ (N *ᵥ Pi.single j (1 : A)) = N i j := by
  have : star (Pi.single i (1 : A) : κ → A) = Pi.single i 1 := by
    funext l
    by_cases hl : l = i
    · subst hl; simp
    · simp [hl]
  rw [this, mulVec_single_one, single_one_dotProduct]
  rfl
end Formalism.HermitianLattices.Ext.L3.integralBasisSpans
