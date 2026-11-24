-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.filtration_type_intersection_ofA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:11:01.251565+00:00
-- url     : https://prove2.me/submissions/a6905901-410a-491a-b436-1758c7a2fa4e

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsEqLattice
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationTypeIntersection
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_typeSum_mono
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_phQ_single
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_A_can
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_ev_phQ_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_ph_type
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_highest_vectors_rational_span_of
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_evL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_supp_in
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution : LemmaA → FiltrationTypeIntersection := by
  intro hA n _ M CF pi hpi x
  classical
  constructor
  · intro hx
    refine Submodule.span_induction (p := fun x _ => (fun i => (x i : ℚ)) ∈ typeSum M pi) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨j, hj, I, rfl⟩
      have h1 := qd_ph_type hA CF _ j le_rfl (Pi.single I 1)
      rw [qd_phQ_single] at h1
      exact qd_typeSum_mono M (show qd_low (CF.mu j) ⊆ pi from fun la hla => hpi.2 _ hj la hla.1 hla.2) h1
    · have : (fun i => (((0 : M.ι → ℤ) i : ℤ) : ℚ)) = 0 := by funext i; simp
      rw [this]; exact zero_mem _
    · intro x y _ _ hx hy
      have : (fun i => (((x + y) i : ℤ) : ℚ)) = (fun i => (x i : ℚ)) + fun i => (y i : ℚ) := by funext i; simp
      rw [this]; exact add_mem hx hy
    · intro c x _ hx
      have : (fun i => (((c • x) i : ℤ) : ℚ)) = (c : ℚ) • fun i => (x i : ℚ) := by funext i; simp
      rw [this]; exact Submodule.smul_mem _ _ hx
  · intro hx
    have hK : ∀ nu, Dominant nu → nu ∉ pi → typeSum M pi ≤ LinearMap.ker (qb_evL M ℚ nu) := by
      intro nu hnu hnot
      unfold typeSum
      rw [Submodule.span_le]
      rintro _ ⟨mu, hmu, v, hv, g, rfl⟩
      have hvs := highest_vectors_rational_span_of hA n M CF mu (hpi.1 mu hmu) v hv
      have : Submodule.span ℚ {y | ∃ j, CF.mu j = mu ∧ y = fun i => (CF.vec j (canT (CF.mu j)) i : ℚ)} ≤
          (LinearMap.ker (qb_evL M ℚ nu)).comap (Matrix.mulVecLin (M.A.map (evGL g))) := by
        rw [Submodule.span_le]
        rintro _ ⟨j, hj, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mem_ker, Matrix.mulVecLin_apply, qd_A_can, qb_evL_apply]
        exact qd_ev_phQ_zero CF j nu (fun hd => hnot (hpi.2 _ (by rw [hj]; exact hmu) nu hnu hd)) _
      exact this hvs
    obtain ⟨b, hb⟩ : ∃ b : qb_Idx CF → ℤ, ∑ y, b y • qb_vecF CF ℤ y = x := by
      have : x ∈ Submodule.span ℤ (Set.range (qb_vecF CF ℤ)) := by rw [(qb_basisR hA CF ℤ).2]; trivial
      exact (Submodule.mem_span_range_iff_exists_fun ℤ).1 this
    have hcast : (fun i => (x i : ℚ)) = ∑ y, (b y : ℚ) • qb_vecF CF ℚ y := by
      funext i
      rw [← hb]
      simp [qb_vecF, Finset.sum_apply]
    have hs := qb_supp_in hA CF ℚ (fun y => (b y : ℚ)) pi hpi (fun nu hnu hnot => by
      rw [← hcast]; exact hK nu hnu hnot hx)
    rw [← hb]
    refine Submodule.sum_mem _ fun y _ => ?_
    by_cases hy : b y = 0
    · rw [hy, zero_smul]; exact zero_mem _
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨y.1, hs y (by exact_mod_cast hy), y.2.1, ?_⟩
      funext i
      simp only [qb_vecF, Int.cast_id]
end Formalism.InvariantFactorPaths.ColumnFamilies
