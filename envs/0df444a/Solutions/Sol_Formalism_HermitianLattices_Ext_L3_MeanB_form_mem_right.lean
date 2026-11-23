-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.MeanB.form_mem_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:29:43.168803+00:00
-- url     : https://prove2.me/submissions/d521fe56-c4aa-42a7-8197-1d5842365235

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulSubOneMemPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.MeanB
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
namespace Formalism.HermitianLattices.Ext.L3.MeanB
theorem _root_.solution (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (u : ↥L) {w : ↥L}
    (hw : w ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) :
    ∃ z ∈ extP K 𝔭 ^ k, algebraMap (𝓞 K) K z = h (u : V) (w : V) := by
  induction hw using Submodule.smul_induction_on' with
  | smul a ha v _ =>
    obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hLi u u.2 v v.2)
    refine ⟨a * c, Ideal.mul_mem_right _ _ ha, ?_⟩
    rw [map_mul, hc, Submodule.coe_smul, ← algebraMap_smul K a (v : V), map_smul, smul_eq_mul]
  | add a _ b _ ha hb =>
    obtain ⟨x', hx', ex⟩ := ha
    obtain ⟨y', hy', ey⟩ := hb
    exact ⟨x' + y', add_mem hx' hy', by rw [map_add, ex, ey, Submodule.coe_add, map_add]⟩
end Formalism.HermitianLattices.Ext.L3.MeanB
