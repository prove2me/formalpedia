-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.isUnitIn_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:36.686425+00:00
-- url     : https://prove2.me/submissions/8ae37f71-4787-40c4-9141-e759366fc8bd

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_mem


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
theorem _root_.solution (hS : IsHermSemilocal S) (hπ : IsUnif S π) {t : K} (ht : t ∈ S)
    (hc : ∀ d : K, d ≠ 0 → t * d⁻¹ ∈ S → π * d⁻¹ ∈ S → d⁻¹ ∈ S) : IsUnitIn S t := by
  let A : AddSubgroup K :=
    { carrier := {x | ∃ s ∈ S, ∃ r ∈ S, x = s * t + r * π}
      add_mem' := by
        rintro _ _ ⟨s, hs, r, hr, rfl⟩ ⟨s', hs', r', hr', rfl⟩
        exact ⟨s + s', S.add_mem hs hs', r + r', S.add_mem hr hr', by ring⟩
      zero_mem' := ⟨0, S.zero_mem, 0, S.zero_mem, by ring⟩
      neg_mem' := by
        rintro _ ⟨s, hs, r, hr, rfl⟩
        exact ⟨-s, S.neg_mem hs, -r, S.neg_mem hr, by ring⟩ }
  have hAm : ∀ x, x ∈ A ↔ ∃ s ∈ S, ∃ r ∈ S, x = s * t + r * π := fun x => Iff.rfl
  obtain ⟨α, hαA, hα0, hα⟩ := hS.principal A
    (fun c hc' a ha => by
      obtain ⟨s, hs, r, hr, rfl⟩ := (hAm a).1 ha
      exact (hAm _).2 ⟨c * s, S.mul_mem hc' hs, c * r, S.mul_mem hc' hr, by ring⟩)
    ⟨π, (hAm π).2 ⟨0, S.zero_mem, 1, S.one_mem, by ring⟩, hπ.ne⟩
    ⟨1, one_ne_zero, fun a ha => by
      obtain ⟨s, hs, r, hr, rfl⟩ := (hAm a).1 ha
      rw [one_mul]
      exact S.add_mem (S.mul_mem hs ht) (S.mul_mem hr hπ.mem)⟩
  have htα := hα t ((hAm t).2 ⟨1, S.one_mem, 0, S.zero_mem, by ring⟩)
  have hπα := hα π ((hAm π).2 ⟨0, S.zero_mem, 1, S.one_mem, by ring⟩)
  have hαinv : α⁻¹ ∈ S := hc α hα0 htα hπα
  obtain ⟨s, hs, r, hr, hαe⟩ := (hAm α).1 hαA
  have hunit : IsUnitIn S (1 + π * (-(r * α⁻¹))) := hπ.rad _ (S.neg_mem (S.mul_mem hr hαinv))
  have he : s * t * α⁻¹ = 1 + π * (-(r * α⁻¹)) := by
    have h1 : (s * t + r * π) * α⁻¹ = 1 := by rw [← hαe, mul_inv_cancel₀ hα0]
    linear_combination h1
  rw [← he] at hunit
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hunit.1 (by ring)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hunit.1 (by ring)
  refine ⟨ht0, ht, ?_⟩
  have e : t⁻¹ = s * α⁻¹ * (s * t * α⁻¹)⁻¹ := by
    field_simp
  rw [e]
  exact S.mul_mem (S.mul_mem hs hαinv) hunit.2.2
end Formalism.HermitianLattices.Ext.L3.U0
