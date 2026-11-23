-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.coprime_of_cls
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:26.334996+00:00
-- url     : https://prove2.me/submissions/23fa4284-2beb-4334-b798-6472b36ff45f

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution {m₀ s a₀ b : ℕ} (ha : a₀.Coprime m₀) (hb : b ∈ clsB m₀ s a₀) : b.Coprime (m₀ * s) := by
  simp only [clsB, Finset.mem_filter, Finset.mem_range] at hb
  have hm : b.Coprime m₀ := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hb.2.1, ← Nat.gcd_rec, Nat.gcd_comm]
    exact ha
  exact Nat.Coprime.mul_right hm hb.2.2
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
