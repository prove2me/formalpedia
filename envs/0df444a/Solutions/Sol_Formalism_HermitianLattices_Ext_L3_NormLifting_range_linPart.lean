-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.NormLifting.range_linPart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:31.837237+00:00
-- url     : https://prove2.me/submissions/4757dafc-e68b-494d-8c3a-d4c2059426b0

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_mem_fixSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_exists_trace
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_linPart_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.NormLifting
variable {A B : Type*} [CommRing A] [CommRing B] {σ : A →+* A} {τ : B →+* B} {π : A →+* B}
namespace Formalism.HermitianLattices.Ext.L3.NormLifting
theorem _root_.solution (hσ : ∀ a, σ (σ a) = a) {I : Ideal A} (hI : ∀ a ∈ I, σ a ∈ I)
    (hsq : ∀ a ∈ I, ∀ b ∈ I, a * b = 0) {θ e : A} (he : (θ - σ θ) * e = 1) {n m : A}
    (hnm : n * m = 1) {M : ℕ} (y : Fin M → A) (hy : n - ∑ i, σ (y i) * y i ∈ I) :
    (linPart σ I y).range = fixSub σ I := by

  ext w
  rw [mem_fixSub, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨δ, rfl⟩
    rw [linPart_apply]
    constructor
    · exact sum_mem (fun i _ => I.add_mem (I.mul_mem_left _ (δ i).2) (I.mul_mem_right _ (hI _ (δ i).2)))
    · rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [map_add, map_mul, hσ]
      ring
  · rintro ⟨hwI, hwσ⟩
    obtain ⟨v, hv, hv2⟩ := exists_trace hσ he ((mem_fixSub σ I).mpr ⟨hwI, hwσ⟩)
    refine ⟨fun i => ⟨y i * (m * v), I.mul_mem_left _ (I.mul_mem_left _ hv)⟩, ?_⟩
    rw [linPart_apply]
    have hs : ∑ i, σ (y i) * (y i * (m * v)) = v := by
      have h1 : ∑ i, σ (y i) * (y i * (m * v)) = (∑ i, σ (y i) * y i) * (m * v) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [h1]
      have h2 := hsq _ hy _ hv
      linear_combination (-m) * h2 + v * hnm
    calc ∑ i, (σ (y i) * ((⟨y i * (m * v), I.mul_mem_left _ (I.mul_mem_left _ hv)⟩ : I) : A) +
          σ ((⟨y i * (m * v), I.mul_mem_left _ (I.mul_mem_left _ hv)⟩ : I) : A) * y i)
        = ∑ i, σ (y i) * (y i * (m * v)) + σ (∑ i, σ (y i) * (y i * (m * v))) := by
          rw [Finset.sum_add_distrib, map_sum]
          congr 1
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simp only [map_mul, hσ]
          ring
      _ = w := by rw [hs, hv2]
end Formalism.HermitianLattices.Ext.L3.NormLifting
