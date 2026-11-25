-- Prove2me | solution 1 for Formalism.F.discreteTopology_sup_and_covol_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:55:24.950512+00:00
-- url     : https://prove2.me/submissions/4f38678f-69e3-4aed-bae3-bd49476d92c8

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolPos
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DegQuot
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_GramDetLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopesBdd
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopeLeMuMaxOf
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopeInequality
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_OrthSum
import Theorems.Thm_Formalism_F_discreteTopology_span_range_and_covol
import Theorems.Thm_Formalism_F_covol_eq_gram
import Theorems.Thm_Formalism_F_det_gram_basis_pos
import Theorems.Thm_P2M_Formalism_F_linearIndependent_coe_basis____9cab7951c4f4
import Theorems.Thm_P2M_Formalism_F_span_range_coe_basis__24da96608575


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
open Formalism Formalism.F
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace Formalism.F
theorem _root_.solution (L₁ L₂ : Submodule ℤ E) [DiscreteTopology L₁] [DiscreteTopology L₂]
    (h : ∀ x ∈ L₁, ∀ y ∈ L₂, inner ℝ x y = 0) :
    DiscreteTopology (L₁ ⊔ L₂ : Submodule ℤ E) ∧ covol (L₁ ⊔ L₂) = covol L₁ * covol L₂ := by
  classical

  let b₁ := Module.finBasis ℤ L₁
  let b₂ := Module.finBasis ℤ L₂
  let v₁ : Fin (Module.finrank ℤ L₁) → E := fun i => (b₁ i : E)
  let v₂ : Fin (Module.finrank ℤ L₂) → E := fun i => (b₂ i : E)
  have hv₁ : LinearIndependent ℝ v₁ := linearIndependent_coe_basis''' L₁ b₁
  have hv₂ : LinearIndependent ℝ v₂ := linearIndependent_coe_basis''' L₂ b₂
  have horth : ∀ i j, inner ℝ (v₁ i) (v₂ j) = 0 := fun i j => h _ (b₁ i).2 _ (b₂ j).2
  have horth' : ∀ i j, inner ℝ (v₂ i) (v₁ j) = 0 := fun i j => by
    rw [real_inner_comm]; exact horth j i
  have hdisj : Disjoint (span ℝ (Set.range v₁)) (span ℝ (Set.range v₂)) := by
    apply Submodule.IsOrtho.disjoint
    rw [Submodule.isOrtho_span]
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact horth i j
  have hli := hv₁.sum_type hv₂ hdisj
  have hs₁ : span ℤ (Set.range v₁) = L₁ := span_range_coe_basis' L₁ b₁
  have hs₂ : span ℤ (Set.range v₂) = L₂ := span_range_coe_basis' L₂ b₂
  have hspan : span ℤ (Set.range (Sum.elim v₁ v₂)) = L₁ ⊔ L₂ := by
    rw [Set.Sum.elim_range, Submodule.span_union, hs₁, hs₂]
  obtain ⟨hd, hc⟩ := discreteTopology_span_range_and_covol _ hli
  rw [hspan] at hd hc
  refine ⟨hd, ?_⟩
  have hc₁ : covol L₁ = Real.sqrt (Matrix.gram ℝ v₁).det := covol_eq_gram E L₁ _ b₁
  have hc₂ : covol L₂ = Real.sqrt (Matrix.gram ℝ v₂).det := covol_eq_gram E L₂ _ b₂
  have hp₁ : 0 ≤ (Matrix.gram ℝ v₁).det := (det_gram_basis_pos L₁ b₁).le
  have hg : Matrix.gram ℝ (Sum.elim v₁ v₂) =
      Matrix.fromBlocks (Matrix.gram ℝ v₁) 0 0 (Matrix.gram ℝ v₂) := by
    ext (i | i) (j | j) <;> simp [Matrix.gram_apply, horth, horth']
  rw [hc, hc₁, hc₂, hg, Matrix.det_fromBlocks_zero₂₁, Real.sqrt_mul hp₁]
end Formalism.F
