-- Prove2me | solution 1 for Formalism.DegreeFormula.PermutationPointDegree.permExp_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:13:40.487393+00:00
-- url     : https://prove2.me/submissions/2437d0af-06c8-4d1f-b3c6-4fce1c717ccb

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PermExpInj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.DegreeFormula Formalism.DegreeFormula.PermutationPointDegree
open Formalism.DegreeFormula
namespace Formalism.DegreeFormula.PermutationPointDegree
theorem _root_.solution {ι : Type} [Fintype ι] {N : ℕ} (σ ρ : ι → Equiv.Perm (Fin N))
    (h : permExp σ = permExp ρ) : σ = ρ := by
  funext τ
  ext i
  have := DFunLike.congr_fun h (τ, i)
  simp only [permExp, Finsupp.equivFunOnFinite_symm_apply_apply] at this
  have h1 := (σ τ i).isLt
  have h2 := (ρ τ i).isLt
  omega
end Formalism.DegreeFormula.PermutationPointDegree
