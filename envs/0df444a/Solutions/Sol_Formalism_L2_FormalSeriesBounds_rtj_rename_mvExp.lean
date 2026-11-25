-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rtj_rename_mvExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:42:02.566832+00:00
-- url     : https://prove2.me/submissions/444d090b-78ea-448b-a4d5-2281181af77b

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_degree_embDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
section Disjoint
variable {K : Type} [Field K] {σ : Type}
end Disjoint
section Rename
variable {K : Type} [Field K] {σ τ : Type}
private theorem coeff_embDomain_rename_character_germs (e : σ ↪ τ) (F : MvPowerSeries σ K) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.embDomain e d) (MvPowerSeries.rename e F) = MvPowerSeries.coeff d F := by
  rw [MvPowerSeries.coeff_rename, Finset.sum_eq_single_of_mem d]
  · simp [Finsupp.embDomain_eq_mapDomain]
  · intro y hy hne
    exfalso
    apply hne
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Finsupp.embDomain_eq_mapDomain] at hy
    exact Finsupp.mapDomain_injective e.injective hy
private theorem coeff_rename_eq_zero_of_ne_embDomain (e : σ ↪ τ) (F : MvPowerSeries σ K) (x : τ →₀ ℕ)
    (hx : ∀ d, Finsupp.embDomain e d ≠ x) : MvPowerSeries.coeff x (MvPowerSeries.rename e F) = 0 := by
  rw [MvPowerSeries.coeff_rename]
  refine Finset.sum_eq_zero fun y hy => ?_
  simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq] at hy
  exact absurd (by rw [Finsupp.embDomain_eq_mapDomain]; exact hy) (hx y)
end Rename
section Rows
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} {N K : ℕ} {what₂ : Fin K → ℕ}
end Rows
end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {K : Type} [Field K] {σ τ : Type}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (e : σ ↪ τ) (L : MvPowerSeries σ K) :
    MvPowerSeries.rename e (mvExp L) = mvExp (MvPowerSeries.rename e L) := by
  ext x
  by_cases hx : ∃ d, Finsupp.embDomain e d = x
  · obtain ⟨d, rfl⟩ := hx
    rw [coeff_embDomain_rename_character_germs]
    change (∑ k ∈ Finset.range (Finsupp.degree d + 1), MvPowerSeries.coeff d (L ^ k) / (k.factorial : K)) =
      ∑ k ∈ Finset.range (Finsupp.degree (Finsupp.embDomain e d) + 1),
        MvPowerSeries.coeff (Finsupp.embDomain e d) ((MvPowerSeries.rename e L) ^ k) / (k.factorial : K)
    rw [rtj_degree_embDomain]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← map_pow, coeff_embDomain_rename_character_germs]
  · push_neg at hx
    rw [coeff_rename_eq_zero_of_ne_embDomain e _ x hx]
    change (0 : K) = ∑ k ∈ Finset.range (Finsupp.degree x + 1),
        MvPowerSeries.coeff x ((MvPowerSeries.rename e L) ^ k) / (k.factorial : K)
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← map_pow, coeff_rename_eq_zero_of_ne_embDomain e _ x hx, zero_div]
end Formalism.L2.FormalSeriesBounds
