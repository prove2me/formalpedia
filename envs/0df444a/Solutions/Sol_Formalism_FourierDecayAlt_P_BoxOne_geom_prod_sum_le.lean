-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BoxOne.geom_prod_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:14.861729+00:00
-- url     : https://prove2.me/submissions/4b39a30a-7e86-4d3d-ba3d-7ae15a3e4541

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_SqrtAbsNormLeProd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BoxOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BoxOne
open NumberField Finset
namespace Formalism.FourierDecayAlt.P.BoxOne
theorem _root_.solution {ι : Type} [Fintype ι] (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (T : Finset (ι → ℕ)) :
    ∑ k ∈ T, ∏ i, q ^ (k i) ≤ (1 / (1 - q)) ^ Fintype.card ι := by
  classical
  set M := T.sup (fun k => Finset.univ.sup k) + 1 with hM
  have hsub : T ⊆ Fintype.piFinset (fun _ : ι => Finset.range M) := by
    intro k hk
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range, hM, Nat.lt_succ_iff]
    exact (Finset.le_sup (f := k) (Finset.mem_univ i)).trans
      (Finset.le_sup (f := fun k => Finset.univ.sup k) hk)
  have hgeom : ∑ n ∈ Finset.range M, q ^ n ≤ 1 / (1 - q) := by
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := M) hq0 hq1
    rwa [← Finset.range_eq_Ico, pow_zero] at h
  calc ∑ k ∈ T, ∏ i, q ^ (k i)
      ≤ ∑ k ∈ Fintype.piFinset (fun _ : ι => Finset.range M), ∏ i, q ^ (k i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ => Finset.prod_nonneg fun i _ => pow_nonneg hq0 _)
    _ = ∏ i : ι, ∑ n ∈ Finset.range M, q ^ n := by
        rw [Finset.prod_univ_sum]
    _ ≤ ∏ _i : ι, (1 / (1 - q)) :=
        Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun n _ => pow_nonneg hq0 n)
          (fun _ _ => hgeom)
    _ = (1 / (1 - q)) ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]
end Formalism.FourierDecayAlt.P.BoxOne
