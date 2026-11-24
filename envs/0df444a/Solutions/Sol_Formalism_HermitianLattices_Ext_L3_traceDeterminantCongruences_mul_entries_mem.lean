-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences.mul_entries_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:56.973671+00:00
-- url     : https://prove2.me/submissions/74d7c207-2064-492f-b640-629941eacccd

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySeventh

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences
open idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable {m : Type} [Fintype m] [DecidableEq m]
namespace Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences
theorem _root_.solution {r : Type} {J : Ideal (𝓞 K)} (M : Matrix m m (𝓞 K)) {R : Matrix m r (𝓞 K)}
    (hR : ∀ i j, R i j ∈ J) (i : m) (j : r) : (M * R) i j ∈ J := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ (fun l _ => Ideal.mul_mem_left _ _ (hR l j))
end Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences
