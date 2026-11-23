-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdicNeighbourhood.avg_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:14.392801+00:00
-- url     : https://prove2.me/submissions/07324141-dea9-4185-bed2-6131f0897715

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdicNeighbourhood
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_out_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_local_zero

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
theorem _root_.solution (Λ N : AddSubgroup K) [Finite (N ⧸ Λ.addSubgroupOf N)] {d : ℕ}
    (F : (Fin d → K) → ℂ) (hF : LatInvN Λ F) (hx : ∀ x, Osc N F x) :
    ∑ᶠ y : Fin d → K ⧸ Λ, F (fun i => Quotient.out (y i)) = 0 := by
  classical
  have := Fintype.ofFinite (N ⧸ Λ.addSubgroupOf N)
  obtain ⟨f, hf⟩ : ∃ f : (Fin d → K ⧸ Λ) → ℂ, f = fun y => F (fun i => Quotient.out (y i)) :=
    ⟨_, rfl⟩
  rw [← hf]
  by_cases hfin : (Function.support f).Finite
  swap
  · exact finsum_of_infinite_support hfin
  have shift : ∀ (v : Fin d → K) (y : Fin d → K ⧸ Λ), f (y + fun i => (v i : K ⧸ Λ)) =
      F ((fun i => Quotient.out (y i)) + v) := by
    intro v y
    have : ∀ i, ∃ l ∈ Λ, (Quotient.out (y i + (v i : K ⧸ Λ)) : K) = Quotient.out (y i) + v i + l :=
      fun i => out_add Λ (y i) (v i)
    choose l hl el using this
    have e : (fun i => (Quotient.out ((y + fun i => (v i : K ⧸ Λ)) i) : K)) =
        ((fun i => Quotient.out (y i)) + v) + l := by
      ext i; exact el i
    rw [hf]
    show F _ = _
    rw [e, hF _ l hl]
  obtain ⟨o, ho⟩ : ∃ o : (Fin d → N ⧸ Λ.addSubgroupOf N) → Fin d → K,
      o = fun h i => ((Quotient.out (h i) : N) : K) := ⟨_, rfl⟩
  have h1 : ∀ h, ∑ᶠ y, f (y + fun i => (o h i : K ⧸ Λ)) = ∑ᶠ y, f y :=
    fun h => finsum_comp_equiv (Equiv.addRight (fun i => (o h i : K ⧸ Λ)))
  have h2 : ∑ h : (Fin d → N ⧸ Λ.addSubgroupOf N), ∑ᶠ y, f (y + fun i => (o h i : K ⧸ Λ)) = 0 := by
    rw [← finsum_sum_comm]
    · have : ∀ y : Fin d → K ⧸ Λ, ∑ h, f (y + fun i => (o h i : K ⧸ Λ)) = 0 := by
        intro y
        simp only [shift]
        rw [ho]
        exact local_zero Λ N F hF _ (hx _)
      simp only [this, finsum_zero]
    · intro h _
      exact hfin.preimage ((Equiv.addRight (fun i => (o h i : K ⧸ Λ))).injective.injOn)
  simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd h (by exact_mod_cast Fintype.card_ne_zero)
  · exact h
end Formalism.FourierDecayAlt.P.AdicNeighbourhood
