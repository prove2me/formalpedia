-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.char_family
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:54.490801+00:00
-- url     : https://prove2.me/submissions/8b2c6907-b603-481e-ad54-6a81971b6786

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HenselRootsBounded
namespace Formalism.FourierDecayAlt.P.HenselRootsBounded
theorem _root_.solution {K : Type} [CommRing K] (B B' : AddSubgroup K)
    (hfin : Finite (B ⧸ B'.addSubgroupOf B)) :
    ∃ S : Finset K, S.card ≠ 0 ∧ (∀ b ∈ S, b ∈ B) ∧ ∀ χ : AddChar K ℂ, (∀ b ∈ B', χ b = 1) →
      (∃ b ∈ B, χ b ≠ 1) → ∑ b ∈ S, χ b = 0 := by
  classical
  have := Fintype.ofFinite (B ⧸ B'.addSubgroupOf B)
  let o : B ⧸ B'.addSubgroupOf B → K := fun q => ((Quotient.out q : B) : K)
  have hinj : Function.Injective o := by
    intro q q' hq
    have : (Quotient.out q : B) = Quotient.out q' := Subtype.ext hq
    calc q = Quotient.mk'' (Quotient.out q) := (Quotient.out_eq' q).symm
      _ = Quotient.mk'' (Quotient.out q') := by rw [this]
      _ = q' := Quotient.out_eq' q'
  refine ⟨Finset.univ.image o, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj]
    exact Finset.card_ne_zero.2 ⟨0, Finset.mem_univ _⟩
  · intro b hb
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 hb
    exact (Quotient.out q : B).2
  · intro χ h1 ⟨b₀, hb₀, hne⟩
    rw [Finset.sum_image fun x _ y _ hxy => hinj hxy]
    let q₀ : B ⧸ B'.addSubgroupOf B := ((⟨b₀, hb₀⟩ : B) : B ⧸ B'.addSubgroupOf B)
    have hshift : ∀ q, χ (o (q₀ + q)) = χ b₀ * χ (o q) := by
      intro q
      have hq : ((Quotient.out (q₀ + q) : B) : B ⧸ B'.addSubgroupOf B) =
          (((⟨b₀, hb₀⟩ : B) + Quotient.out q : B) : B ⧸ B'.addSubgroupOf B) := by
        rw [QuotientAddGroup.mk_add]
        show Quotient.mk'' (Quotient.out (q₀ + q)) = q₀ + Quotient.mk'' (Quotient.out q)
        rw [Quotient.out_eq', Quotient.out_eq']
      rw [QuotientAddGroup.eq] at hq
      have hq' : -o (q₀ + q) + (b₀ + o q) ∈ B' := by
        have := AddSubgroup.mem_addSubgroupOf.1 hq
        simpa [o] using this
      have h2 := h1 _ hq'
      rw [AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, AddChar.map_add_eq_mul] at h2
      have hne0 : χ (o (q₀ + q)) ≠ 0 := by
        intro h0
        rw [h0] at h2; simp at h2
      field_simp at h2
      exact h2.symm
    have hsum : ∑ q, χ (o q) = χ b₀ * ∑ q, χ (o q) := by
      rw [Finset.mul_sum, ← Fintype.sum_equiv (Equiv.addLeft q₀) (fun q => χ (o (q₀ + q)))
        (fun q => χ (o q)) (fun q => rfl)]
      exact Finset.sum_congr rfl fun q _ => hshift q
    have : (1 - χ b₀) * ∑ q, χ (o q) = 0 := by linear_combination hsum
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd (sub_eq_zero.1 h0).symm hne
    · exact h0
end Formalism.FourierDecayAlt.P.HenselRootsBounded
