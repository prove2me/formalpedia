-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.Slope.trunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:49:29.659596+00:00
-- url     : https://prove2.me/submissions/65964864-fed5-4966-bb5c-2a63026a47a7

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Theorems.Thm_Formalism_MainNotions_PlaneGram_le_val_of_le_pow_six
import Theorems.Thm_Formalism_MainNotions_PlaneGram_val_nonneg_of_pow_six
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_mul_ge_left
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_add_ge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) {σ : Type}
variable {v}
namespace Slope
variable {TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop} {c : ℕ}
private theorem le_valuation_finset_sum {ι : Type} (s : Finset ι) (f : ι → K) {t : WithTop ℚ}
    (h : ∀ i ∈ s, t ≤ v (f i)) : t ≤ v (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, AddValuation.map_zero]; exact le_top
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (le_min (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))) (AddValuation.map_add v _ _)
end Slope
namespace CostOK
variable {TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop}
end CostOK
section Binom
variable {TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop}
end Binom
section DiagCost
open MvPolynomial
end DiagCost
end Formalism.MainNotions.PlaneGram
end
end

set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) {σ : Type}
variable {v}
open Formalism.MainNotions.PlaneGram.Slope
variable {TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop} {c : ℕ}
namespace Formalism.MainNotions.PlaneGram.Slope
theorem _root_.solution {f : (σ →₀ ℕ) → K} (sf : Slope v TotallyRealRoots c f) :
    ∃ (ι : Type) (_ : Fintype ι) (lam : ι → K) (n : ι → ℕ) (b : ι → (σ →₀ ℕ) → K),
      (∀ k, 0 ≤ v (lam k)) ∧ (∀ k, n k ≤ 6 * c) ∧ (∀ k, TotallyRealRoots (n k) (b k)) ∧
      (∀ k α, 0 ≤ v (b k α)) ∧ ∀ α, (c : WithTop ℚ) ≤ v (f α - ∑ k, lam k * b k α) := by
  classical
  obtain ⟨ι, hι, lam, n, b, h1, h2, h3, h4⟩ := sf
  refine ⟨{k // n k ≤ 6 * c}, inferInstance, fun k => lam k.1, fun k => n k.1, fun k => b k.1,
    fun k => val_nonneg_of_pow_six _ _ (h1 k.1), fun k => k.2, fun k => h2 k.1,
    fun k α => h3 k.1 α, fun α => ?_⟩
  show (c : WithTop ℚ) ≤ v (f α - ∑ k : {k // n k ≤ 6 * c}, lam k.1 * b k.1 α)
  have hsub : ∑ k : {k // n k ≤ 6 * c}, lam k.1 * b k.1 α =
      ∑ k ∈ Finset.univ.filter (fun k => n k ≤ 6 * c), lam k * b k α :=
    (Finset.sum_subtype _ (fun x => by simp) (fun k => lam k * b k α)).symm
  have e : f α - ∑ k : {k // n k ≤ 6 * c}, lam k.1 * b k.1 α =
      (f α - ∑ k, lam k * b k α) +
        ∑ k ∈ Finset.univ.filter (fun k => ¬ n k ≤ 6 * c), lam k * b k α := by
    rw [hsub, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => n k ≤ 6 * c)]
    ring
  rw [e]
  refine v_add_ge (h4 α) (le_valuation_finset_sum _ _ (fun k hk => ?_))
  have hk' := (Finset.mem_filter.mp hk).2
  exact v_mul_ge_left (le_val_of_le_pow_six (lam k) c (n k) (by omega) (h1 k)) (h3 k α)
end Formalism.MainNotions.PlaneGram.Slope
