-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.exists_starProjection_ne_zero_norm_le_of_dualMinimum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:33:59.113676+00:00
-- url     : https://prove2.me/submissions/4637863c-96c0-4c17-9182-c4bce71d9418

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ExistsNeZeroNormLeRankDivOfDualMinimum
import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SaturationProperties
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DegQuot
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShortIndependentVectorsOfDualMinimum
import Theorems.Thm_Formalism_F_degree_quotient
import Theorems.Thm_Formalism_F_saturation_properties
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_exists_ne_zero_norm_le_rank_div_of_dualMinimum


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
    (hdual : ∀ y : E, y ≠ 0 → (∀ x ∈ M, ∃ z : ℤ, inner ℝ x y = (z : ℝ)) → l ≤ ‖y‖)
    (W : Submodule ℝ E) (N : Submodule ℤ E) (hNM : N ≤ M) (hNW : span ℝ (N : Set E) = W)
    (hW : W ≠ ⊤) :
    ∃ m ∈ M, Wᗮ.starProjection m ≠ 0 ∧
      ‖Wᗮ.starProjection m‖ ≤ (finrank ℝ E : ℝ) / l := by
  classical
  obtain ⟨hSat, hNS, -⟩ := Formalism.F.saturation_properties E M N hMd hNM
  obtain ⟨hQd, hrk, -⟩ := Formalism.F.degree_quotient E M (Formalism.F.satur M N) hMd hSat
  have hSW : span ℝ ((Formalism.F.satur M N : Submodule ℤ E) : Set E) = W := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      rw [← hNW]
      exact (Submodule.mem_inf.mp hx).2
    · rw [← hNW]
      exact Submodule.span_mono (show (N : Set E) ⊆ Formalism.F.satur M N from hNS)
  have hQeq : ∀ q, q ∈ Formalism.F.quot M (Formalism.F.satur M N) ↔ ∃ m ∈ M, Wᗮ.starProjection m = q := by
    intro q
    simp [Formalism.F.quot, hSW, Submodule.mem_map]
  haveI := hQd
  have hPzero : ∀ x ∈ W, Wᗮ.starProjection x = 0 := by
    intro x hx
    have h1 := Submodule.starProjection_add_starProjection_orthogonal (K := W) x
    rw [Submodule.starProjection_eq_self_iff.mpr hx] at h1
    simpa using h1
  have hsubW : ∀ m : E, m - Wᗮ.starProjection m ∈ W := by
    intro m
    have h1 := Submodule.sub_starProjection_mem_orthogonal (K := Wᗮ) m
    rwa [Submodule.orthogonal_orthogonal] at h1
  have hQne : Formalism.F.quot M (Formalism.F.satur M N) ≠ ⊥ := by
    intro hQ0
    apply hW
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    intro m hm
    have hq : Wᗮ.starProjection m ∈ Formalism.F.quot M (Formalism.F.satur M N) := (hQeq _).mpr ⟨m, hm, rfl⟩
    rw [hQ0, Submodule.mem_bot] at hq
    have h1 := hsubW m
    rw [hq, sub_zero] at h1
    exact h1
  have hdual' : ∀ y ∈ span ℝ ((Formalism.F.quot M (Formalism.F.satur M N) : Submodule ℤ E) : Set E), y ≠ 0 →
      (∀ x ∈ Formalism.F.quot M (Formalism.F.satur M N), ∃ z : ℤ, inner ℝ x y = (z : ℝ)) → l ≤ ‖y‖ := by
    intro y hy hy0 hint
    apply hdual y hy0
    intro x hx
    obtain ⟨z, hz⟩ := hint _ ((hQeq _).mpr ⟨x, hx, rfl⟩)
    refine ⟨z, ?_⟩
    have hyW : y ∈ Wᗮ := by
      refine (Submodule.span_le.mpr ?_) hy
      intro q hq
      obtain ⟨m, -, rfl⟩ := (hQeq q).mp hq
      exact Submodule.starProjection_apply_mem _ _
    rw [← hz, Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hyW]
  obtain ⟨q, hqQ, hq0, hqle⟩ := exists_ne_zero_norm_le_rank_div_of_dualMinimum (Formalism.F.quot M (Formalism.F.satur M N)) hQne hl hdual'
  obtain ⟨m, hm, rfl⟩ := (hQeq q).mp hqQ
  refine ⟨m, hm, hq0, le_trans hqle ?_⟩
  have hMrk : Formalism.F.rk M = finrank ℝ E := by
    haveI : IsZLattice ℝ M := ⟨hspan⟩
    exact ZLattice.rank ℝ M
  have hle : Formalism.F.rk (Formalism.F.quot M (Formalism.F.satur M N)) ≤ finrank ℝ E := by
    rw [← hMrk, hrk]
    exact Nat.le_add_left _ _
  exact div_le_div_of_nonneg_right (by exact_mod_cast hle) hl.le
end Formalism.NormUnitaryCountingLemmas
