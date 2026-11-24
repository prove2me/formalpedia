-- Prove2me | solution 1 for Formalism.REAL.maximal_compact_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:43:49.036695+00:00
-- url     : https://prove2.me/submissions/01e510e4-0dfc-4254-aeba-3b647172db75

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Theorems.Thm_Formalism_REAL_f1alg_inK_iff
import Theorems.Thm_Formalism_REAL_f1alg_unit_iff
import Theorems.Thm_Formalism_REAL_mem_unitaryGroup_iff_mul_conjTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
noncomputable section
namespace Formalism.REAL
private lemma Jm_mul_self_eq_oneRealPlaceTaylor {n : ℕ} (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num
private lemma Jm_conjTranspose_eq {n : ℕ} (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [diagonal_conjTranspose]
  congr 1
  funext a
  simp only [Pi.star_apply]
  split_ifs <;> simp
end Formalism.REAL
end
end

set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : KFacts := by
  intro n ε

  have h1 : ∀ g ∈ Kset ε, inUJ ε g := by
    rintro g ⟨hu, hc⟩
    unfold inUJ
    rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, (f1alg_unit_iff g).mp hu, Matrix.one_mul]

  have h5 : ∀ g, g ∈ Kset ε ↔ (inUJ ε g ∧ g ∈ Matrix.unitaryGroup (Fin n) ℂ) := by
    intro g
    constructor
    · intro hg
      exact ⟨h1 g hg, hg.1⟩
    · rintro ⟨hJ, hu⟩
      refine ⟨hu, ?_⟩
      unfold inUJ at hJ
      calc g * Jm ε = g * (gᴴ * Jm ε * g) := by rw [hJ]
        _ = (g * gᴴ) * Jm ε * g := by simp only [Matrix.mul_assoc]
        _ = Jm ε * g := by rw [(mem_unitaryGroup_iff_mul_conjTranspose g).mp hu, Matrix.one_mul]
  refine ⟨h1, ?_, ?_, ?_, h5⟩
  ·
    have hcl : IsClosed (Kset ε) := by
      have : Kset ε = {g | gᴴ * g = 1} ∩ {g | g * Jm ε = Jm ε * g} := by
        ext g
        simp only [Kset, Set.mem_setOf_eq, Set.mem_inter_iff, f1alg_unit_iff]
      rw [this]
      exact (isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const).inter
        (isClosed_eq (continuous_id.matrix_mul continuous_const) (continuous_const.matrix_mul continuous_id))
    have hsub : Kset ε ⊆ Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ
        (fun _ : Fin n => Metric.closedBall (0 : ℂ) 1)) := by
      intro g hg i _ j _
      rw [Metric.mem_closedBall, dist_zero_right]
      exact entry_norm_bound_of_unitary hg.1 i j
    exact IsCompact.of_isClosed_subset
      (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _) hcl hsub
  · refine ⟨?_, rfl⟩
    rw [f1alg_unit_iff, Jm_conjTranspose_eq, Jm_mul_self_eq_oneRealPlaceTaylor]
  · rintro X ⟨hG, hc⟩
    have hX : Xᴴ = -X := ((f1alg_inK_iff ε X).mp ⟨hG, hc⟩).1
    refine ⟨?_, ?_⟩
    · rw [f1alg_unit_iff, ← Matrix.exp_conjTranspose, hX,
        ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl X)), neg_add_cancel,
        NormedSpace.exp_zero]
    · exact ((Commute.exp_right (show Commute (Jm ε) X from hc.symm)).symm).eq
end Formalism.REAL
