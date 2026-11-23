-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.SplitA.mul_mem_locR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:33:59.668486+00:00
-- url     : https://prove2.me/submissions/d25c8511-6f90-491e-9c11-cfe100de3042

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemHcompl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.SplitA
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLattices.Ext.L3.SplitA
theorem _root_.solution (p : Ideal (𝓞 K)) {c d : K} (hc : c ∈ Formalism.HermitianLatticesTheory.locR (K := K) p)
    (hd : d ∈ Formalism.HermitianLatticesTheory.locR (K := K) p) : c * d ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by
  obtain ⟨s, hs, hc⟩ := hc
  obtain ⟨t, ht, hd⟩ := hd
  refine ⟨s * t, Submonoid.mul_mem _ hs ht, ?_⟩
  obtain ⟨r₁, hr₁⟩ := Submodule.mem_one.mp hc
  obtain ⟨r₂, hr₂⟩ := Submodule.mem_one.mp hd
  refine Submodule.mem_one.mpr ⟨r₁ * r₂, ?_⟩
  rw [Algebra.smul_def] at hr₁ hr₂ ⊢
  rw [map_mul, hr₁, hr₂, map_mul]
  ring
end Formalism.HermitianLattices.Ext.L3.SplitA
