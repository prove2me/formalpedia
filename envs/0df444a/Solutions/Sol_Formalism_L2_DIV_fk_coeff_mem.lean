-- Prove2me | solution 1 for Formalism.L2.DIV.fk_coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:14.01952+00:00
-- url     : https://prove2.me/submissions/489e382f-1f18-4630-8586-bd3017a50e45

import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open scoped Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] (K0 : Subfield K)
namespace Formalism.L2.DIV
theorem _root_.solution {σ : Type} {P : MvPolynomial σ K} (hP : P ∈ (map (σ := σ) K0.subtype).range) (m : σ →₀ ℕ) :
    coeff m P ∈ K0 := by
  obtain ⟨Q, rfl⟩ := hP
  rw [MvPolynomial.coeff_map]
  exact (coeff m Q).2
end Formalism.L2.DIV
