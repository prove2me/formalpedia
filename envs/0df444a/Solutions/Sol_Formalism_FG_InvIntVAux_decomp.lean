-- Prove2me | solution 1 for Formalism.FG.InvIntVAux.decomp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:56.952773+00:00
-- url     : https://prove2.me/submissions/67457037-d5f0-4205-b463-b9837884f3ae

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_InvIntV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.InvIntVAux
open Formalism.G Formalism.G.LogCR
variable {K : Type u} [NormedField K]
namespace Formalism.FG.InvIntVAux
theorem _root_.solution {σ : Type*} [Fintype σ] [LinearOrder σ] (m : ℕ) (x : MvPowerSeries σ K)
    (hx : Low (m + 1) x) :
    ∃ y : σ → MvPowerSeries σ K, (∀ i, Low m (y i)) ∧ x = ∑ i, MvPowerSeries.X i * y i := by
  classical
  obtain ⟨y, hy⟩ : ∃ y : σ → MvPowerSeries σ K, ∀ i e, MvPowerSeries.coeff e (y i) =
      if (e + Finsupp.single i 1).support.min = (i : WithTop σ) then
        MvPowerSeries.coeff (e + Finsupp.single i 1) x else 0 :=
    ⟨fun i e => if (e + Finsupp.single i 1).support.min = (i : WithTop σ) then
        MvPowerSeries.coeff (e + Finsupp.single i 1) x else 0, fun i e => rfl⟩
  have hd0 : (0 : σ →₀ ℕ).degree = 0 := by
    first | rfl | simp
  refine ⟨y, fun i e he => ?_, ?_⟩
  · rw [hy]
    split_ifs with hmin
    · have hdeg : (e + Finsupp.single i 1).degree = e.degree + 1 := by
        first
          | rw [Finsupp.degree_add, Finsupp.degree_single]
          | simp
      exact hx _ (by omega)
    · rfl
  · ext d
    rw [map_sum]
    have hXm : ∀ i (φ : MvPowerSeries σ K), MvPowerSeries.coeff d (MvPowerSeries.X i * φ) =
        if Finsupp.single i 1 ≤ d then MvPowerSeries.coeff (d - Finsupp.single i 1) φ else 0 := by
      intro i φ
      first
        | rw [MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul, one_mul]
        | rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, one_mul]
        | simp [MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul]
    simp only [hXm]
    by_cases hdz : d = 0
    · subst hdz
      have h0 : MvPowerSeries.coeff (0 : σ →₀ ℕ) x = 0 := hx 0 (by rw [hd0]; omega)
      rw [h0]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      have hnle : ¬ Finsupp.single i 1 ≤ (0 : σ →₀ ℕ) := by
        intro hle
        have := hle i
        simp at this
      rw [if_neg hnle]
    · have hne : d.support.Nonempty := Finsupp.support_nonempty_iff.mpr hdz
      obtain ⟨i0, hmin⟩ := Finset.min_of_nonempty hne
      have hi0m : i0 ∈ d.support := Finset.mem_of_min hmin
      have hd1 : 1 ≤ d i0 := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi0m)
      have hle : Finsupp.single i0 1 ≤ d := by
        first
          | exact Finsupp.single_le_iff.mpr hd1
          | (intro j; by_cases hj : i0 = j; (subst hj; simpa using hd1); simp [Finsupp.single_apply, hj])
      rw [Finset.sum_eq_single i0]
      · rw [if_pos hle, hy, tsub_add_cancel_of_le hle, if_pos hmin]
      · intro i _ hi
        split_ifs with hle'
        · have hc : ¬ d.support.min = (i : WithTop σ) := by
            rw [hmin]
            intro h
            exact hi (WithTop.coe_injective h).symm
          rw [hy, tsub_add_cancel_of_le hle', if_neg hc]
        · rfl
      · intro h
        exact absurd (Finset.mem_univ i0) h
end Formalism.FG.InvIntVAux
