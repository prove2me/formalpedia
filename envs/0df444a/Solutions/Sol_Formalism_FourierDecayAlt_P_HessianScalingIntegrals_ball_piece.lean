-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HessianScalingIntegrals.ball_piece
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:20.714019+00:00
-- url     : https://prove2.me/submissions/5dc6a552-539b-4f5d-a618-64ab7d003ae4

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HessianScalingIntegrals
import Theorems.Thm_Formalism_FourierDecayAlt_P_HessianScalingIntegrals_out_mk_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HessianScalingIntegrals
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.HessianScalingIntegrals
theorem _root_.solution (R : Subring K) (m : ℕ) (B Λ : AddSubgroup K) (hΛB : Λ ≤ B) (z : K)
    (φ : (Fin m → K) → (Fin m → K))
    (hbij : Set.BijOn φ {ξ | ∀ k, ξ k ∈ B} {ξ | ∀ k, ξ k ∈ B})
    (hcos : ∀ ξ η : Fin m → K, (∀ k, ξ k ∈ B) → (∀ k, η k ∈ B) →
      ((∀ k, φ ξ k - φ η k ∈ Λ) ↔ ∀ k, ξ k - η k ∈ Λ))
    (G G' : (Fin m → K) → ℂ) (hG : LatInvN Λ G)
    (hG0 : ∀ x, (¬ ∀ k, x k - z ∈ B) → G x = 0)
    (hG'0 : ∀ ξ, (¬ ∀ k, ξ k ∈ B) → G' ξ = 0)
    (hGG' : ∀ ξ, (∀ k, ξ k ∈ B) → G (fun k => z + φ ξ k) = G' ξ) :
    LatInvN Λ G' ∧ intK R Λ m G = intK R Λ m G' := by
  classical
  have hinv : ∀ x x' : Fin m → K, (∀ k, x k - x' k ∈ Λ) → G x = G x' := by
    intro x x' h
    have := hG x' (fun k => x k - x' k) h
    rw [← this]; congr 1; ext k; simp
  constructor
  · intro ξ l hl
    by_cases hξ : ∀ k, ξ k ∈ B
    · have hξl : ∀ k, (ξ + l) k ∈ B := fun k => B.add_mem (hξ k) (hΛB (hl k))
      rw [← hGG' _ hξl, ← hGG' _ hξ]
      apply hinv
      intro k
      have := (hcos (ξ + l) ξ hξl hξ).2 (fun k => by simpa using hl k) k
      simpa using this
    · have hξl : ¬ ∀ k, (ξ + l) k ∈ B := fun h => hξ fun k => by
        have := B.sub_mem (h k) (hΛB (hl k)); simpa using this
      rw [hG'0 _ hξl, hG'0 _ hξ]
  · unfold intK
    congr 1
    let o : (Fin m → K ⧸ Λ) → (Fin m → K) := fun y i => Quotient.out (y i)
    let e : (Fin m → K ⧸ Λ) → (Fin m → K ⧸ Λ) := fun y k => ((z + φ (o y) k : K) : K ⧸ Λ)
    have hoe : ∀ y k, o (e y) k - (z + φ (o y) k) ∈ Λ := fun y k => out_mk_sub Λ _
    have h1 : ∑ᶠ y, G (o y) = ∑ᶠ y ∈ {y | ∀ k, o y k - z ∈ B}, G (o y) := by
      refine finsum_congr fun y => ?_
      rw [finsum_eq_if]
      split_ifs with h
      · rfl
      · exact hG0 _ h
    have h2 : ∑ᶠ y, G' (o y) = ∑ᶠ y ∈ {y | ∀ k, o y k ∈ B}, G' (o y) := by
      refine finsum_congr fun y => ?_
      rw [finsum_eq_if]
      split_ifs with h
      · rfl
      · exact hG'0 _ h
    change ∑ᶠ y, G (o y) = ∑ᶠ y, G' (o y)
    rw [h1, h2]
    symm
    refine finsum_mem_eq_of_bijOn e ⟨?_, ?_, ?_⟩ ?_
    · intro y hy k
      have h3 : φ (o y) k ∈ B := hbij.mapsTo hy k
      have h4 := B.add_mem (hΛB (hoe y k)) h3
      have : o (e y) k - z = o (e y) k - (z + φ (o y) k) + φ (o y) k := by ring
      rw [this]; exact h4
    · intro y hy y' hy' hyy
      have h3 : ∀ k, φ (o y) k - φ (o y') k ∈ Λ := by
        intro k
        have := congrFun hyy k
        have h5 : ((z + φ (o y) k : K) : K ⧸ Λ) = ((z + φ (o y') k : K) : K ⧸ Λ) := this
        rw [QuotientAddGroup.eq] at h5
        have h6 := Λ.neg_mem h5
        have : φ (o y) k - φ (o y') k = -(-(z + φ (o y) k) + (z + φ (o y') k)) := by ring
        rw [this]; exact h6
      have h4 := (hcos _ _ hy hy').1 h3
      funext k
      have h5 : ((o y k : K) : K ⧸ Λ) = ((o y' k : K) : K ⧸ Λ) := by
        rw [QuotientAddGroup.eq]
        have h6 := Λ.neg_mem (h4 k)
        have : -o y k + o y' k = -(o y k - o y' k) := by ring
        rw [this]; exact h6
      simpa [o] using h5
    · intro y hy
      have hmem : (fun k => o y k - z) ∈ {ξ : Fin m → K | ∀ k, ξ k ∈ B} := hy
      obtain ⟨ξ, hξ, hξy⟩ := hbij.surjOn hmem
      let y' : Fin m → K ⧸ Λ := fun k => ((ξ k : K) : K ⧸ Λ)
      have h3 : ∀ k, o y' k - ξ k ∈ Λ := fun k => out_mk_sub Λ _
      have h4 : ∀ k, o y' k ∈ B := fun k => by
        have := B.add_mem (hΛB (h3 k)) (hξ k); simpa using this
      refine ⟨y', h4, ?_⟩
      funext k
      have h5 := (hcos _ _ h4 hξ).2 h3 k
      have h6 : ((z + φ (o y') k : K) : K ⧸ Λ) = ((o y k : K) : K ⧸ Λ) := by
        rw [QuotientAddGroup.eq]
        have h7 : φ ξ k = o y k - z := congrFun hξy k
        have : -(z + φ (o y') k) + o y k = -(φ (o y') k - φ ξ k) := by rw [h7]; ring
        rw [this]; exact Λ.neg_mem h5
      have h8 : ((o y k : K) : K ⧸ Λ) = y k := QuotientAddGroup.out_eq' _
      exact h6.trans h8
    · intro y hy
      rw [← hGG' _ hy]
      symm
      exact hinv _ _ (hoe y)
end Formalism.FourierDecayAlt.P.HessianScalingIntegrals
