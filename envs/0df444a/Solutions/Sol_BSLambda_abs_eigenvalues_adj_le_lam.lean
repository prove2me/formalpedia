-- Prove2me | solution 1 for BSLambda.abs_eigenvalues_adj_le_lam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:36:20.999475+00:00
-- url     : https://prove2.me/submissions/87030508-8227-45f1-9c8a-2e94df2af1e5

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Theorems.Thm_BSLambda_le_lam_of_eigenvector
public import Theorems.Thm_BSLambda_exists_neg_eigenvector

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input V → Bool) (i : Input V) :
    |(isHermitian_adj f).eigenvalues i| ≤ lam f := by
  have hne : (⇑((isHermitian_adj f).eigenvectorBasis i) : Input V → ℝ) ≠ 0 :=
    (WithLp.ofLp_eq_zero 2).ne.2 <|
      (isHermitian_adj f).eigenvectorBasis.orthonormal.ne_zero i
  have hev : adj f *ᵥ ⇑((isHermitian_adj f).eigenvectorBasis i)
      = (isHermitian_adj f).eigenvalues i • ⇑((isHermitian_adj f).eigenvectorBasis i) :=
    (isHermitian_adj f).mulVec_eigenvectorBasis i
  refine abs_le.2 ⟨?_, le_ciSup (Finite.bddAbove_range _) i⟩
  obtain ⟨w, hw, hwev⟩ := exists_neg_eigenvector f hne hev
  exact neg_le.2 (le_lam_of_eigenvector f hw hwev)
end BSLambda
