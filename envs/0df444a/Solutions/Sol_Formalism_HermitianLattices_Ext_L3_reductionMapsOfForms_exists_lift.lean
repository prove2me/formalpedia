-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:38:10.517813+00:00
-- url     : https://prove2.me/submissions/f9a53ff9-e238-4efc-9f9b-616bd18db644

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySeventh
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEighth
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m r : Type} [Fintype m] [Fintype r] [DecidableEq m] [DecidableEq r]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
theorem _root_.solution {a b : Type} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (X : Matrix a b (𝓞 K ⧸ extP K 𝔭 ^ k)) :
    ∃ Y : Matrix a b (𝓞 K), Y.map (mkk K 𝔭 k) = X := by
  choose f hf using fun x : 𝓞 K ⧸ extP K 𝔭 ^ k => Ideal.Quotient.mk_surjective x
  refine ⟨X.map f, ?_⟩
  ext i j
  simp [hf]
end Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
