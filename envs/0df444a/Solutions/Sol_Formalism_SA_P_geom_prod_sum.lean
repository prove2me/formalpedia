-- Prove2me | solution 1 for Formalism.SA.P.geom_prod_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:36:35.354484+00:00
-- url     : https://prove2.me/submissions/adbbd634-723e-409d-be36-13e3b6650f3e

import Definitions.Def_Formalism_LatticeRigidity_StatementC
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_SqrtAbsNormLeProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SA Formalism.SA.P
open NumberField Finset
variable {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
namespace Formalism.SA.P
theorem _root_.solution {ι : Type} [Fintype ι] (T : Finset (ι → ℕ)) :
    ∑ k ∈ T, ∏ i, (1 / 2 : ℝ) ^ (k i) ≤ 2 ^ Fintype.card ι := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ k ∈ T, ∀ i, k i < N := by
    refine ⟨(T.sup fun k => Finset.univ.sup k) + 1, fun k hk i => ?_⟩
    have h1 : k i ≤ Finset.univ.sup k := Finset.le_sup (f := k) (Finset.mem_univ i)
    have h2 : Finset.univ.sup k ≤ T.sup fun k => Finset.univ.sup k :=
      Finset.le_sup (f := fun k => Finset.univ.sup k) hk
    omega
  have hsub : T ⊆ Fintype.piFinset (fun _ : ι => Finset.range N) := by
    intro k hk
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_range.mpr (hN k hk i)
  calc ∑ k ∈ T, ∏ i, (1 / 2 : ℝ) ^ (k i)
      ≤ ∑ k ∈ Fintype.piFinset (fun _ : ι => Finset.range N), ∏ i, (1 / 2 : ℝ) ^ (k i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ => Finset.prod_nonneg fun _ _ => by positivity)
    _ = ∏ _i : ι, ∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n := by rw [Finset.prod_univ_sum]
    _ ≤ ∏ _i : ι, (2 : ℝ) :=
        Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
          (fun _ _ => sum_geometric_two_le N)
    _ = 2 ^ Fintype.card ι := by simp
end Formalism.SA.P
