-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.hermitianFormColumns.exists_liftv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:12:11.340503+00:00
-- url     : https://prove2.me/submissions/a2fe6d10-c73e-4c65-9deb-0e3e6cf873f3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEighth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences reductionMapsOfForms
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m : Type} [Fintype m] [DecidableEq m]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
theorem _root_.solution (𝔭 : Ideal (𝓞 F)) (k : ℕ) (x : m → 𝓞 K ⧸ extP K 𝔭 ^ k) :
    ∃ y : m → 𝓞 K, (fun i => mkk K 𝔭 k (y i)) = x := by
  choose f hf using fun z : 𝓞 K ⧸ extP K 𝔭 ^ k => Ideal.Quotient.mk_surjective z
  exact ⟨fun i => f (x i), funext fun i => hf _⟩
end Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
