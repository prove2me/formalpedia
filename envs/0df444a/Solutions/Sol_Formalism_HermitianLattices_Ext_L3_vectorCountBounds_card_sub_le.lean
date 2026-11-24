-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.vectorCountBounds.card_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:29.778746+00:00
-- url     : https://prove2.me/submissions/f457c855-880a-4a31-926d-ce83636b40a5

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEleventh
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_vectorCountBounds_finite_vec
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_vectorCountBounds_card_vec

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.vectorCountBounds
open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences reductionMapsOfForms hermitianFormColumns
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m : Type} [Fintype m] [DecidableEq m]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.vectorCountBounds
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ)
    (p : (m → 𝓞 K ⧸ extP K 𝔭 ^ k) → Prop) :
    Nat.card {x // p x} ≤ Ideal.absNorm 𝔭 ^ (k * (2 * Fintype.card m)) := by
  haveI := finite_vec (m := m) (K := K) h𝔭 k
  rw [← card_vec hK h𝔭 k]
  exact Finite.card_subtype_le p
end Formalism.HermitianLattices.Ext.L3.vectorCountBounds
