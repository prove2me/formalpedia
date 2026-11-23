-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallB.mem_of_unram
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:23.879649+00:00
-- url     : https://prove2.me/submissions/10c9dfdc-7a3d-40e9-9354-32abb8f151ae

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapConjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_sub_conjO_notMem


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallB
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.BallB
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {I : Ideal (𝓞 K)} {z : 𝓞 K}
    (hz : ∀ θ : 𝓞 K, (θ - conjO K θ) * z ∈ I) : z ∈ I := by
  by_contra hn
  let J : Ideal (𝓞 K) :=
    { carrier := {c | c * z ∈ I}
      add_mem' := fun {a c} ha hc => by
        change (a + c) * z ∈ I
        rw [add_mul]; exact I.add_mem ha hc
      zero_mem' := by change (0 : 𝓞 K) * z ∈ I; rw [zero_mul]; exact I.zero_mem
      smul_mem' := fun c a ha => by
        change (c • a) * z ∈ I
        rw [smul_eq_mul, mul_assoc]; exact I.mul_mem_left c ha }
  have hJ : J ≠ ⊤ := by
    intro hJ
    have h1 : (1 : 𝓞 K) ∈ J := hJ ▸ Submodule.mem_top
    have h2 : (1 : 𝓞 K) * z ∈ I := h1
    rw [one_mul] at h2
    exact hn h2
  obtain ⟨P, hP, hJP⟩ := Ideal.exists_le_maximal J hJ
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
  exact hθ (hJP (hz θ))
end Formalism.HermitianLattices.Ext.L3.BallB
