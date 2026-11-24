-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.NMul.comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:27:23.283337+00:00
-- url     : https://prove2.me/submissions/eeb1a54f-5d3c-41e5-80a5-d11b4b4e4118

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NormMul
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NMul_vandermonde

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas
open Formalism.NormUnitaryCountingLemmas.NMul
namespace Formalism.NormUnitaryCountingLemmas.NMul
theorem _root_.solution {N n : ℕ} (ν : Fin N → ℕ) (sF sG : Finset (Fin N × Fin n →₀ ℕ))
    (hF : ∀ a ∈ sF, ∀ j, blockDeg a j = ν j) (c : Fin N × Fin n →₀ ℕ) :
    ∑ p ∈ (sF ×ˢ sG).filter (fun p => p.1 + p.2 = c), ∏ j, ∏ k, (c (j, k)).choose (p.1 (j, k)) ≤
      ∏ j, (blockDeg c j).choose (ν j) := by
  classical
  have hR : ∏ j, (blockDeg c j).choose (ν j) =
      ∑ x ∈ Fintype.piFinset (fun j => finsuppAntidiag (univ : Finset (Fin n)) (ν j)),
        ∏ j, ∏ k, (c (j, k)).choose (x j k) := by
    calc ∏ j, (blockDeg c j).choose (ν j)
        = ∏ j, ∑ l ∈ finsuppAntidiag (univ : Finset (Fin n)) (ν j), ∏ k, (c (j, k)).choose (l k) :=
          prod_congr rfl fun j _ => (vandermonde (fun k => c (j, k)) (ν j)).symm
      _ = _ := Finset.prod_univ_sum _ _
  rw [hR]
  let ι : (Fin N × Fin n →₀ ℕ) × (Fin N × Fin n →₀ ℕ) → (Fin N → Fin n →₀ ℕ) :=
    fun p j => Finsupp.equivFunOnFinite.symm (fun k => p.1 (j, k))
  have hinj : Set.InjOn ι ((sF ×ˢ sG).filter (fun p => p.1 + p.2 = c)) := by
    intro p hp q hq hpq
    rw [mem_coe, mem_filter] at hp hq
    have h1 : p.1 = q.1 := by
      ext ⟨j, k⟩
      have := congrArg (fun x => x j k) hpq
      simpa [ι] using this
    have h2 : p.2 = q.2 := by
      have := hp.2.trans hq.2.symm
      rw [h1] at this
      exact add_left_cancel this
    exact Prod.ext h1 h2
  calc ∑ p ∈ (sF ×ˢ sG).filter (fun p => p.1 + p.2 = c), ∏ j, ∏ k, (c (j, k)).choose (p.1 (j, k))
      = ∑ p ∈ (sF ×ˢ sG).filter (fun p => p.1 + p.2 = c),
          (fun x : Fin N → Fin n →₀ ℕ => ∏ j, ∏ k, (c (j, k)).choose (x j k)) (ι p) := by
        simp [ι]
    _ = ∑ x ∈ ((sF ×ˢ sG).filter (fun p => p.1 + p.2 = c)).image ι,
          ∏ j, ∏ k, (c (j, k)).choose (x j k) := (sum_image (f := fun x : Fin N → Fin n →₀ ℕ =>
          ∏ j, ∏ k, (c (j, k)).choose (x j k)) hinj).symm
    _ ≤ _ := by
        apply sum_le_sum_of_subset
        intro x hx
        rw [mem_image] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        rw [Fintype.mem_piFinset]
        intro j
        rw [mem_finsuppAntidiag]
        refine ⟨?_, subset_univ _⟩
        rw [mem_filter, mem_product] at hp
        rw [← hF _ hp.1.1 j]
        simp [ι, blockDeg]
end Formalism.NormUnitaryCountingLemmas.NMul
