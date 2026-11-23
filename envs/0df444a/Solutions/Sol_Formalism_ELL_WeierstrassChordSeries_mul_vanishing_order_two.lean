-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.mul_vanishing_order_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:37.86551+00:00
-- url     : https://prove2.me/submissions/740ae53a-fcd1-4f5f-9fdf-c411c92ba50a

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_L_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
namespace Formalism.ELL.WeierstrassChordSeries
theorem _root_.solution {φ : MvPowerSeries (Fin 2) K} (h0 : cc φ = 0) (h1 : ∀ i, (L i) φ = 0)
    (ψ : MvPowerSeries (Fin 2) K) : cc (φ * ψ) = 0 ∧ ∀ i, (L i) (φ * ψ) = 0 := by
  exact ⟨by rw [map_mul, h0, zero_mul], fun i => by rw [L_mul, h0, h1 i]; ring⟩
end Formalism.ELL.WeierstrassChordSeries
