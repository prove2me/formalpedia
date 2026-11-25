-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.OrthogonalSumAlt.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:00:46.840911+00:00
-- url     : https://prove2.me/submissions/0a91b2c8-1a84-4fba-85dc-8bc2533312d9

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_OrthSum
import Theorems.Thm_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_deg_bot
import Theorems.Thm_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_rkK_bot
import Theorems.Thm_P2M_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_finrank_pos__df67f6332271
import Theorems.Thm_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_orth_inner
import Theorems.Thm_Formalism_HN_HeightGram_realize_injective
import Theorems.Thm_Formalism_HN_PlaceLattice_realize_injective
import Theorems.Thm_Formalism_HN_degSupermod
import Theorems.Thm_Formalism_HN_hnSum
import Theorems.Thm_Formalism_HN_plLat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.BranchingDeterminantCap.OrthogonalSumAlt
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
namespace Formalism.BranchingDeterminantCap.OrthogonalSumAlt
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {S : Type} (A : S → Submodule (𝓞 K) V) (hA : ∀ s, (A s).FG)
    (horth : ∀ s t, s ≠ t → OrthAt b X (A s) (A t)) (s : Finset S) :
    (⨆ i ∈ s, A i).FG ∧ Formalism.HN.rkK (⨆ i ∈ s, A i) = ∑ i ∈ s, Formalism.HN.rkK (A i) ∧
      Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) (⨆ i ∈ s, A i) =
        ∑ i ∈ s, Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) (A i) ∧
      ∀ c : ℝ, (∀ i ∈ s, A i ≠ ⊥ → Formalism.HN.muMax (Formalism.HermitianLatticesTheory.realize b X) (A i) ≤ c) →
        (⨆ i ∈ s, A i) ≠ ⊥ → Formalism.HN.muMax (Formalism.HermitianLatticesTheory.realize b X) (⨆ i ∈ s, A i) ≤ c := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [rkK_bot, deg_bot b X hX, Submodule.fg_bot]
  | insert a s ha ih =>
    obtain ⟨ihfg, ihrk, ihdeg, ihmu⟩ := ih
    rw [Finset.iSup_insert]
    set B := ⨆ i ∈ s, A i with hB
    have ho : ∀ x ∈ A a, ∀ y ∈ B,
        inner ℝ (Formalism.HermitianLatticesTheory.realize b X x) (Formalism.HermitianLatticesTheory.realize b X y) = 0 := by
      intro x hx y hy
      obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum A y).1 hy
      rw [← hμ, map_sum, inner_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      exact orth_inner b X (horth a i (fun h => ha (h ▸ hi))) x hx _ (μ i).2
    have hlA := (Formalism.HN.plLat K V ι b X hX (A a) (hA a)).1
    have hlB := (Formalism.HN.plLat K V ι b X hX B ihfg).1
    obtain ⟨hl, hdeg, hmu⟩ :=
      (Formalism.HN.hnSum.{0, 0, 0, 0} (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X)).2 (A a) B hlA hlB ho
    have hfg : (A a ⊔ B).FG := (hA a).sup ihfg
    have hinf : A a ⊓ B = ⊥ := by
      refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
      have h1 := ho x hx.1 x hx.2
      rw [inner_self_eq_zero] at h1
      exact Formalism.HN.HeightGram.realize_injective b X hX (by rw [h1, map_zero])
    have hrk := (Formalism.HN.degSupermod (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) (A a ⊔ B) (A a) B hl
      le_sup_left le_sup_right).1
    rw [hinf, (Formalism.HN.plLat K V ι b X hX _ hfg).2.1, (Formalism.HN.plLat K V ι b X hX _ (hA a)).2.1,
      (Formalism.HN.plLat K V ι b X hX _ ihfg).2.1,
      (Formalism.HN.plLat K V ι b X hX _ Submodule.fg_bot).2.1, rkK_bot, mul_zero, add_zero,
      ← mul_add] at hrk
    have hrk' := Nat.eq_of_mul_eq_mul_left (finrank_pos' (K := K)) hrk
    refine ⟨hfg, ?_, ?_, ?_⟩
    · rw [hrk', Finset.sum_insert ha, ihrk]
    · rw [hdeg, Finset.sum_insert ha, ihdeg]
    · intro c hc hne
      have hcs : ∀ i ∈ s, A i ≠ ⊥ → Formalism.HN.muMax (Formalism.HermitianLatticesTheory.realize b X) (A i) ≤ c :=
        fun i hi => hc i (Finset.mem_insert_of_mem hi)
      by_cases h1 : A a = ⊥
      · rw [h1, bot_sup_eq] at hne ⊢
        exact ihmu c hcs hne
      · by_cases h2 : B = ⊥
        · rw [h2, sup_bot_eq]
          exact hc a (Finset.mem_insert_self a s) h1
        · rw [(hmu h1 h2).1]
          exact max_le (hc a (Finset.mem_insert_self a s) h1) (ihmu c hcs h2)
end Formalism.BranchingDeterminantCap.OrthogonalSumAlt
