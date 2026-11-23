-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdicNeighbourhood.local_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:55.306792+00:00
-- url     : https://prove2.me/submissions/f5d7e9b2-c8cb-49b7-8b48-36e6310e0aac

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdicNeighbourhood
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_out_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Formalism.DoubleCosetMeasures Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdicNeighbourhood
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.AdicNeighbourhood
theorem _root_.solution (Λ N : AddSubgroup K) [Fintype (N ⧸ Λ.addSubgroupOf N)] {d : ℕ}
    (F : (Fin d → K) → ℂ) (hF : LatInvN Λ F) (x : Fin d → K) (hx : Osc N F x) :
    ∑ h : Fin d → N ⧸ Λ.addSubgroupOf N, F (x + fun i => ((Quotient.out (h i) : N) : K)) = 0 := by
  classical
  rcases hx with hx | ⟨k, n₀, hn₀, c, hc, hx⟩
  · exact Finset.sum_eq_zero fun h _ => hx _ fun i => (Quotient.out (h i) : N).2
  · obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Fin d → N ⧸ Λ.addSubgroupOf N) → ℂ,
        Φ = fun h => F (x + fun i => ((Quotient.out (h i) : N) : K)) := ⟨_, rfl⟩
    obtain ⟨q, hq⟩ : ∃ q : Fin d → N ⧸ Λ.addSubgroupOf N,
        q = fun i => (((Pi.single k ⟨n₀, hn₀⟩ : Fin d → N) i : N) : N ⧸ Λ.addSubgroupOf N) := ⟨_, rfl⟩
    have key : ∀ h, Φ (h + q) = c * Φ h := by
      intro h
      rw [hΦ]
      show F _ = c * F _
      rw [← hx _ (fun i => (Quotient.out (h i) : N).2)]
      have : ∀ i, ∃ l ∈ Λ, ((Quotient.out ((h + q) i) : N) : K) =
          ((Quotient.out (h i) : N) : K) + (Pi.single k n₀ : Fin d → K) i + l := by
        intro i
        obtain ⟨l, hl, e⟩ := out_add (Λ.addSubgroupOf N) (h i) ((Pi.single k ⟨n₀, hn₀⟩ : Fin d → N) i)
        refine ⟨(l : K), AddSubgroup.mem_addSubgroupOf.1 hl, ?_⟩
        have e' : (h + q) i = h i + (((Pi.single k ⟨n₀, hn₀⟩ : Fin d → N) i : N) :
            N ⧸ Λ.addSubgroupOf N) := by rw [hq]; rfl
        rw [e', e]
        have e'' : (((Pi.single k ⟨n₀, hn₀⟩ : Fin d → N) i : N) : K) =
            (Pi.single k n₀ : Fin d → K) i := by
          by_cases hik : i = k
          · subst hik; simp
          · simp [hik]
        push_cast
        rw [e'']
      choose l hl el using this
      have e : (x + fun i => ((Quotient.out ((h + q) i) : N) : K)) =
          (x + (fun i => ((Quotient.out (h i) : N) : K)) + Pi.single k n₀) + l := by
        ext i
        have e0 := el i
        simp only [Pi.add_apply] at e0 ⊢
        rw [e0]; ring
      rw [e, hF _ l hl]
    have e := Equiv.sum_comp (Equiv.addRight q) Φ
    simp only [Equiv.coe_addRight, key] at e
    rw [← Finset.mul_sum] at e
    have e2 : (c - 1) * ∑ h, Φ h = 0 := by linear_combination e
    rw [hΦ] at e2
    rcases mul_eq_zero.1 e2 with h | h
    · exact absurd (sub_eq_zero.1 h) hc
    · exact h
end Formalism.FourierDecayAlt.P.AdicNeighbourhood
