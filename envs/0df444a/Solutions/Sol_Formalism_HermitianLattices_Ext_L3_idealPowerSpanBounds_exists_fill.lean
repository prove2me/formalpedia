-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.exists_fill
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:42.927838+00:00
-- url     : https://prove2.me/submissions/80f3a834-1477-446e-90fd-b0e7ef609141

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_pow_le_span_mul_sup

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {P : Ideal R}
namespace Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
theorem _root_.solution (hP : P.IsPrime) (hP0 : P ≠ ⊥) {g : R} {c k : ℕ} (hg : g ∉ P ^ (c + 1))
    (hck : c ≤ k) {s : R} (hs : s ∈ P ^ k) : ∃ r ∈ P ^ (k - c), s - g * r ∈ P ^ (k + 1) := by
  have h := pow_le_span_mul_sup hP hP0 hg hck hs
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h
  obtain ⟨r, hr, rfl⟩ := Ideal.mem_span_singleton_mul.mp hy
  refine ⟨r, hr, ?_⟩
  rw [← hyz, add_sub_cancel_left]
  exact hz
end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
