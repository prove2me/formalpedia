-- Prove2me | solution 1 for Formalism.F.covol_anti_same_rank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:07.923259+00:00
-- url     : https://prove2.me/submissions/dab01f6e-e346-4b2f-9811-9901b6a67cc0

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopeInequality
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SaturationProperties
import Theorems.Thm_Formalism_F_rank_eq_finrank_span
import Theorems.Thm_Formalism_F_det_gram_basis_eq
import Theorems.Thm_Formalism_F_gram_sum_smul_eq_transpose_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Submodule
noncomputable section
namespace Formalism.F
private theorem linearIndependent_coe_basis_of_discrete {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] {ι : Type*} [Fintype ι]
    (e : Basis ι ℤ L) : LinearIndependent ℝ (fun i => (e i : E)) := by
  have hspanZ : span ℤ (Set.range fun i => (e i : E)) = L := by
    have : (Set.range fun i => (e i : E)) = L.subtype '' Set.range e := Set.range_comp _ _
    rw [this, ← Submodule.map_span, e.span_eq, Submodule.map_subtype_top]
  have hspanR : span ℝ (Set.range fun i => (e i : E)) = span ℝ (L : Set E) := by
    rw [← Submodule.span_span_of_tower ℤ ℝ (Set.range fun i => (e i : E)), hspanZ]
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspanR,
    ← rank_eq_finrank_span L]
  exact (Module.finrank_eq_card_basis e).symm
end Formalism.F
end
end

set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.F
namespace Formalism.F
theorem _root_.solution : CovolAntiSameRank := by
  intro E _ _ _ N N' hN' hle hrk
  haveI := hN'
  haveI hN : DiscreteTopology N := DiscreteTopology.of_subset (s := (N' : Set E)) hN' hle
  let e := Module.finBasis ℤ N'
  let f : Basis (Fin (Module.finrank ℤ N')) ℤ N := (Module.finBasis ℤ N).reindex (finCongr hrk)
  let M : Matrix (Fin (Module.finrank ℤ N')) (Fin (Module.finrank ℤ N')) ℤ :=
    fun i j => e.repr ⟨(f j : E), hle (f j).2⟩ i
  have hfj : ∀ j, (f j : E) = ∑ i, (M.map (Int.cast : ℤ → ℝ)) i j • (e i : E) := by
    intro j
    have h := congrArg Subtype.val (e.sum_repr ⟨(f j : E), hle (f j).2⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    show (f j : E) = ∑ i, ((M i j : ℤ) : ℝ) • (e i : E)
    simp only [M, Int.cast_smul_eq_zsmul]
    exact h.symm

  have hgram : Matrix.gram ℝ (fun j => (f j : E))
      = (M.map (Int.cast : ℤ → ℝ)).transpose * Matrix.gram ℝ (fun i => (e i : E))
        * M.map (Int.cast : ℤ → ℝ) := by
    rw [← gram_sum_smul_eq_transpose_mul]
    congr 1
    funext j
    exact hfj j
  have hdetM : (M.map (Int.cast : ℤ → ℝ)).det = ((M.det : ℤ) : ℝ) := by
    rw [← eq_intCast (Int.castRingHom ℝ), RingHom.map_det]
    rfl
  have hdet : (Matrix.gram ℝ (fun j => (f j : E))).det
      = ((M.det : ℤ) : ℝ) ^ 2 * (Matrix.gram ℝ (fun i => (e i : E))).det := by
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdetM]
    ring
  have hfpos : 0 < (Matrix.gram ℝ (fun j => (f j : E))).det :=
    (Matrix.posDef_gram_of_linearIndependent (linearIndependent_coe_basis_of_discrete N f)).det_pos
  have hepos : 0 < (Matrix.gram ℝ (fun i => (e i : E))).det :=
    (Matrix.posDef_gram_of_linearIndependent (linearIndependent_coe_basis_of_discrete N' e)).det_pos
  have hM0 : M.det ≠ 0 := by
    intro h0
    rw [hdet, h0] at hfpos
    simp at hfpos
  have hM1 : (1 : ℝ) ≤ ((M.det : ℤ) : ℝ) ^ 2 := by
    have h1 : (1 : ℤ) ≤ |M.det| := Int.one_le_abs hM0
    have h2 : (1 : ℤ) ≤ M.det ^ 2 := by
      rw [← sq_abs]
      nlinarith
    exact_mod_cast h2
  have hcovN' : covol N' = Real.sqrt (Matrix.gram ℝ (fun i => (e i : E))).det := by
    rw [covol, dif_pos hN']
  have hcovN : covol N = Real.sqrt (Matrix.gram ℝ (fun j => (f j : E))).det := by
    rw [covol, dif_pos hN, det_gram_basis_eq N (Module.finBasis ℤ N) f]
  rw [hcovN', hcovN, hdet]
  apply Real.sqrt_le_sqrt
  nlinarith
end Formalism.F
