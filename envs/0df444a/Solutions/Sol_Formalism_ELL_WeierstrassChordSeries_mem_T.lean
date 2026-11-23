-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.mem_T
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:10:24.553311+00:00
-- url     : https://prove2.me/submissions/a0a9ffdd-7561-4846-9feb-835bc81b5b27

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord

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
variable (W : WeierstrassCurve K) (w : PowerSeries K)
variable {W w}
namespace Formalism.ELL.WeierstrassChordSeries
theorem _root_.solution {φ : MvPowerSeries (Fin 2) K} : φ ∈ T W ↔ ∀ e, MvPowerSeries.coeff e φ ∈ Sadj W := by
  constructor
  · intro hφ e
    obtain ⟨p, rfl⟩ := RingHom.mem_range.mp hφ
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff e p).2
  · intro h
    refine RingHom.mem_range.mpr ⟨fun e => ⟨MvPowerSeries.coeff e φ, h e⟩, ?_⟩
    ext e
    first
      | rfl
      | simp [MvPowerSeries.coeff_map]
end Formalism.ELL.WeierstrassChordSeries
