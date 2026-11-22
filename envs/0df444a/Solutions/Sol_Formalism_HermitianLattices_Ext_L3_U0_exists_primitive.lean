-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.exists_primitive
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:38:15.852803+00:00
-- url     : https://prove2.me/submissions/20603124-78ea-42ae-bd89-51b13feff31d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {M : AddSubgroup V}
namespace Formalism.HermitianLattices.Ext.L3.U0
theorem _root_.solution (hS : IsHermSemilocal S) (hd : ∀ x, h x x = 0 → x = 0)
    (hM : IsLatIn S h W M) {ξ : V} (hξ : ξ ∈ W) (hξ0 : ξ ≠ 0) :
    ∃ l : K, l ≠ 0 ∧ l • ξ ∈ M ∧ ∀ c : K, c • ξ ∈ M → c * l⁻¹ ∈ S := by
  obtain ⟨t, ht0, htM⟩ := hM.span ξ hξ
  have hξξ : h ξ ξ ≠ 0 := fun h0 => hξ0 (hd ξ h0)
  let A : AddSubgroup K :=
    { carrier := {c | c • ξ ∈ M}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, add_smul] at *
        exact M.add_mem ha hb
      zero_mem' := by simp only [Set.mem_setOf_eq, zero_smul]; exact M.zero_mem
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq, neg_smul] at *
        exact M.neg_mem ha }
  have hA : ∀ c, c ∈ A ↔ c • ξ ∈ M := fun c => Iff.rfl
  obtain ⟨α, hαA, hα0, hα⟩ := hS.principal A
    (fun s hs a ha => (hA _).2 (by rw [mul_smul]; exact hM.smul_mem s hs _ ((hA a).1 ha)))
    ⟨t, (hA t).2 htM, ht0⟩
    ⟨star t * h ξ ξ, mul_ne_zero (star_ne_zero.2 ht0) hξξ, fun a ha => by
      have h1 := hM.int _ htM _ ((hA a).1 ha)
      simp only [LinearMap.map_smulₛₗ₂, map_smul, starRingEnd_apply, smul_eq_mul] at h1
      convert h1 using 1
      ring⟩
  exact ⟨α, hα0, (hA α).1 hαA, fun c hc => hα c ((hA c).2 hc)⟩
end Formalism.HermitianLattices.Ext.L3.U0
