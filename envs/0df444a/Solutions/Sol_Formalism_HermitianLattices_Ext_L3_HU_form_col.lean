-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.form_col
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:42.157282+00:00
-- url     : https://prove2.me/submissions/bf461800-9883-425e-b089-05a03906e570

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EquivFunEquivOfMatrixSymm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsUnitaryNear
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMatrixOfIsom
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_form_mulVec
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_form_single


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution (H Y : Matrix κ κ (𝓞 K)) (i j : κ) :
    (Yᴴ * H * Y) i j = star (fun l => Y l i) ⬝ᵥ (H *ᵥ fun l => Y l j) := by
  have := form_mulVec Y H (Pi.single i 1) (Pi.single j 1)
  rw [form_single, mulVec_single_one, mulVec_single_one] at this
  exact this.symm
end Formalism.HermitianLattices.Ext.L3.HU
