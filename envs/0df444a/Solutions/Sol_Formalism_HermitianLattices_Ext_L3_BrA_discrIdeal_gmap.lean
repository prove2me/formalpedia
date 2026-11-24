-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BrA.discrIdeal_gmap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:53.098226+00:00
-- url     : https://prove2.me/submissions/222c3996-bf4a-4d01-a69e-20e0c65e7f67

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinrankRingOfIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module IsDedekindDomain Function
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BrA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.BrA
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (A : Submodule (𝓞 K) V) : discrIdeal h (Formalism.HermitianLatticesTheory.gmap g A) = discrIdeal h A := by
  unfold discrIdeal
  congr 1
  ext z
  constructor
  · rintro ⟨x, hx, e⟩
    refine ⟨fun i => g.symm (x i), fun i => ?_, ?_⟩
    · obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp (hx i)
      have : g y = x i := hyx
      change g.symm (x i) ∈ A
      rw [← this, LinearEquiv.symm_apply_apply]
      exact hy
    · rw [e]
      congr 1
      ext i j
      have := hg (g.symm (x i)) (g.symm (x j))
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
      exact this
  · rintro ⟨x, hx, e⟩
    refine ⟨fun i => g (x i), fun i => Submodule.mem_map.mpr ⟨x i, hx i, rfl⟩, ?_⟩
    rw [e]
    congr 1
    ext i j
    exact (hg (x i) (x j)).symm
end Formalism.HermitianLattices.Ext.L3.BrA
