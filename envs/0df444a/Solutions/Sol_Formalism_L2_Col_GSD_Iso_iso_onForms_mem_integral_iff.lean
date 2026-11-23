-- Prove2me | solution 1 for Formalism.L2.Col.GSD.Iso.iso_onForms_mem_integral_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:59.039978+00:00
-- url     : https://prove2.me/submissions/dc26f80d-40da-471a-93c4-ab88a5f0d861

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.DivisionValues Formalism.L2.DIV
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Col.GSD Formalism.L2.Col.GSD.Iso
variable {S S' : GSD K} (e : GSD.Iso S S')
namespace Formalism.L2.Col.GSD.Iso
theorem _root_.solution (N : S.D → Submodule (𝓞 K) S.V) (N' : S'.D → Submodule (𝓞 K) S'.V)
    (hc : ∀ d : S.D, N' (e.eD d) = (N d).map ((e.eV : S.V →ₗ[K] S'.V).restrictScalars (𝓞 K))) (φ : S.EqFun) :
    e.onForms φ ∈ S'.intOf N' ↔ φ ∈ S.intOf N := by
  constructor
  · intro hφ d
    have h1 : e.eV ((φ : S.D → S.V) (e.eD.symm (e.eD d))) ∈ N' (e.eD d) := hφ (e.eD d)
    rw [Equiv.symm_apply_apply, hc] at h1
    obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.mp h1
    have hy' : y = (φ : S.D → S.V) d := e.eV.injective hxy
    rw [← hy']
    exact hy
  · intro hφ d'
    show e.eV ((φ : S.D → S.V) (e.eD.symm d')) ∈ N' d'
    have h2 := hc (e.eD.symm d')
    rw [Equiv.apply_symm_apply] at h2
    rw [h2]
    exact Submodule.mem_map_of_mem (hφ _)
end Formalism.L2.Col.GSD.Iso
