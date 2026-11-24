-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.exists_short_linearIndependent_of_dualMinimum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:42:58.307629+00:00
-- url     : https://prove2.me/submissions/984cba84-f993-43d0-86fb-00407bf2b861

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ExistsNeZeroNormLeRankDivOfDualMinimum
import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SaturationProperties
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DegQuot
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShortIndependentVectorsOfDualMinimum
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_exists_starProjection_ne_zero_norm_le_of_dualMinimum
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_norm_add_sq_eq_of_inner_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace Formalism.NormUnitaryCountingLemmas
theorem _root_.solution (M : Submodule ℤ E) [hMd : DiscreteTopology M]
    (hspan : span ℝ (M : Set E) = ⊤) {l : ℝ} (hl : 0 < l)
    (hdual : ∀ y : E, y ≠ 0 → (∀ x ∈ M, ∃ z : ℤ, inner ℝ x y = (z : ℝ)) → l ≤ ‖y‖) :
    ∀ k, k ≤ finrank ℝ E → ∃ b : Fin k → E, (∀ i, b i ∈ M) ∧ LinearIndependent ℝ b ∧
      (∀ i, ‖b i‖ ^ 2 ≤ (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) / l) ^ 2) ∧
      (∀ w ∈ span ℝ (Set.range b), ∃ z ∈ span ℤ (Set.range b),
        ‖w - z‖ ^ 2 ≤ (k : ℝ) * ((finrank ℝ E : ℝ) / l) ^ 2 / 4) := by
  classical
  have hPzero : ∀ (W : Submodule ℝ E), ∀ x ∈ W, Wᗮ.starProjection x = 0 := by
    intro W x hx
    have h1 := Submodule.starProjection_add_starProjection_orthogonal (K := W) x
    rw [Submodule.starProjection_eq_self_iff.mpr hx] at h1
    simpa using h1
  have hsubW : ∀ (W : Submodule ℝ E) (m : E), m - Wᗮ.starProjection m ∈ W := by
    intro W m
    have h1 := Submodule.sub_starProjection_mem_orthogonal (K := Wᗮ) m
    rwa [Submodule.orthogonal_orthogonal] at h1
  have horth : ∀ (W : Submodule ℝ E) (u : E) (m : E), u ∈ W →
      inner ℝ u (Wᗮ.starProjection m) = 0 := by
    intro W u m hu
    exact Submodule.inner_right_of_mem_orthogonal hu (Submodule.starProjection_apply_mem _ _)
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨Fin.elim0, fun i => i.elim0, linearIndependent_empty_type, fun i => i.elim0, ?_⟩
    intro w hw
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    have hw0 : w = 0 := by simpa [Set.range_eq_empty] using hw
    subst hw0
    simp
  | succ k ih =>
    intro hk
    obtain ⟨b, hbM, hbli, hbn, hbd⟩ := ih (by omega)
    have hNM : span ℤ (Set.range b) ≤ M := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbM i)
    have hNW : span ℝ ((span ℤ (Set.range b) : Submodule ℤ E) : Set E) = span ℝ (Set.range b) :=
      Submodule.span_span_of_tower ℤ ℝ (Set.range b)
    have hWtop : span ℝ (Set.range b) ≠ ⊤ := by
      intro hW
      have h1 : finrank ℝ (span ℝ (Set.range b)) = k := by
        rw [finrank_span_eq_card hbli, Fintype.card_fin]
      rw [hW, finrank_top] at h1
      omega
    obtain ⟨m, hm, hp0, hple⟩ :=
      exists_starProjection_ne_zero_norm_le_of_dualMinimum M hspan hl hdual (span ℝ (Set.range b)) (span ℤ (Set.range b)) hNM hNW hWtop
    obtain ⟨z, hz, hzd⟩ := hbd (m - (span ℝ (Set.range b))ᗮ.starProjection m) (hsubW _ m)
    have hzW : z ∈ span ℝ (Set.range b) := by
      rw [← hNW]
      exact Submodule.subset_span hz
    have hcnn : 0 ≤ (finrank ℝ E : ℝ) / l := div_nonneg (Nat.cast_nonneg _) hl.le
    have hk1 : ((k : ℝ) + 1) ≤ (finrank ℝ E : ℝ) := by exact_mod_cast hk
    refine ⟨Fin.snoc b (m - z), ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last]
        exact M.sub_mem hm (hNM hz)
      · simp only [Fin.snoc_castSucc]
        exact hbM j
    · rw [linearIndependent_fin_snoc]
      refine ⟨hbli, fun hmem => hp0 ?_⟩
      have e : m = (m - z) + z := by abel
      rw [e, map_add, hPzero _ _ hmem, hPzero _ _ hzW, add_zero]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last]
        have e : m - z = (span ℝ (Set.range b))ᗮ.starProjection m +
            ((m - (span ℝ (Set.range b))ᗮ.starProjection m) - z) := by abel
        have hin : ((m - (span ℝ (Set.range b))ᗮ.starProjection m) - z) ∈ span ℝ (Set.range b) :=
          Submodule.sub_mem _ (hsubW _ m) hzW
        have hi : inner ℝ ((span ℝ (Set.range b))ᗮ.starProjection m)
            ((m - (span ℝ (Set.range b))ᗮ.starProjection m) - z) = 0 := by
          rw [real_inner_comm]
          exact horth _ _ m hin
        rw [e, norm_add_sq_eq_of_inner_eq_zero hi]
        have h2 : ‖(span ℝ (Set.range b))ᗮ.starProjection m‖ ^ 2 ≤ ((finrank ℝ E : ℝ) / l) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hple 2
        have hc2 : 0 ≤ ((finrank ℝ E : ℝ) / l) ^ 2 := sq_nonneg _
        nlinarith
      · simp only [Fin.snoc_castSucc]
        exact hbn j
    · intro w hw
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hw
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      have hu : ∑ j : Fin k, c j.castSucc • b j ∈ span ℝ (Set.range b) :=
        Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
      have hδ := abs_sub_round (c (Fin.last k))
      have hv : ∑ j : Fin k, c j.castSucc • b j +
          (c (Fin.last k) - (round (c (Fin.last k)) : ℝ)) •
            ((m - (span ℝ (Set.range b))ᗮ.starProjection m) - z) ∈ span ℝ (Set.range b) :=
        Submodule.add_mem _ hu (Submodule.smul_mem _ _ (Submodule.sub_mem _ (hsubW _ m) hzW))
      obtain ⟨z'', hz'', hz''d⟩ := hbd _ hv
      have hmem_last : m - z ∈ span ℤ (Set.range (Fin.snoc b (m - z) : Fin (k + 1) → E)) :=
        Submodule.subset_span ⟨Fin.last k, by simp⟩
      have hspan_le : span ℤ (Set.range b) ≤ span ℤ (Set.range (Fin.snoc b (m - z) : Fin (k + 1) → E)) :=
        Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact Submodule.subset_span ⟨j.castSucc, by simp⟩)
      refine ⟨(round (c (Fin.last k))) • (m - z) + z'', Submodule.add_mem _
        (Submodule.smul_mem _ _ hmem_last) (hspan_le hz''), ?_⟩
      have hdecomp : ∑ j : Fin k, c j.castSucc • b j + c (Fin.last k) • (m - z) -
          ((round (c (Fin.last k))) • (m - z) + z'') =
          (∑ j : Fin k, c j.castSucc • b j +
            (c (Fin.last k) - (round (c (Fin.last k)) : ℝ)) •
              ((m - (span ℝ (Set.range b))ᗮ.starProjection m) - z) - z'') +
          (c (Fin.last k) - (round (c (Fin.last k)) : ℝ)) • (span ℝ (Set.range b))ᗮ.starProjection m := by
        rw [← Int.cast_smul_eq_zsmul ℝ]
        simp only [sub_smul, smul_sub]
        abel
      have hz''W : z'' ∈ span ℝ (Set.range b) := by
        rw [← hNW]
        exact Submodule.subset_span hz''
      have hi : inner ℝ (∑ j : Fin k, c j.castSucc • b j +
            (c (Fin.last k) - (round (c (Fin.last k)) : ℝ)) •
              ((m - (span ℝ (Set.range b))ᗮ.starProjection m) - z) - z'')
          ((c (Fin.last k) - (round (c (Fin.last k)) : ℝ)) • (span ℝ (Set.range b))ᗮ.starProjection m) = 0 := by
        rw [real_inner_smul_right, horth _ _ m (Submodule.sub_mem _ hv hz''W), mul_zero]
      rw [hdecomp, norm_add_sq_eq_of_inner_eq_zero hi, norm_smul, mul_pow, Real.norm_eq_abs]
      have hδ2 : |c (Fin.last k) - (round (c (Fin.last k)) : ℝ)| ^ 2 ≤ 1 / 4 := by
        have h0 := abs_nonneg (c (Fin.last k) - (round (c (Fin.last k)) : ℝ))
        nlinarith
      have h2 : ‖(span ℝ (Set.range b))ᗮ.starProjection m‖ ^ 2 ≤ ((finrank ℝ E : ℝ) / l) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hple 2
      have hc2 : 0 ≤ ((finrank ℝ E : ℝ) / l) ^ 2 := sq_nonneg _
      have hp2 : 0 ≤ ‖(span ℝ (Set.range b))ᗮ.starProjection m‖ ^ 2 := sq_nonneg _
      push_cast
      nlinarith [mul_le_mul hδ2 h2 hp2 (by norm_num : (0 : ℝ) ≤ 1 / 4)]
end Formalism.NormUnitaryCountingLemmas
