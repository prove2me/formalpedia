-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.jn_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:58:15.10925+00:00
-- url     : https://prove2.me/submissions/06279cc7-5943-4643-9b71-b349a64c5ee0

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
open scoped ComplexOrder
namespace Formalism.FourierDecayAlt.P.Jx7
theorem _root_.solution {E W : Type} [Field E] (D : TB.Data E W) (jn : ℝ) (hG : D.GramPSD) (hE : D.EstE jn) :
    0 ≤ jn := by
  have hmem : D.emp ∈ D.Wb D.Ntop := by
    unfold TB.Data.Wb
    rw [Finset.mem_filter]
    exact ⟨D.emp_mem, by rw [D.cnt_emp]; exact Nat.zero_le _⟩
  have ht := hE D.emp hmem
  refine ge_of_tendsto ht ?_
  refine eventually_nhdsWithin_of_forall ?_
  intro ε hε
  have hp := hG ε hε 0 D.emp {([] : TB.Pt E)}
  unfold TB.PSDOn at hp
  have hd := hp.diag_nonneg (i := ⟨[], by simp⟩)
  have hre : 0 ≤ (D.gram ε 0 D.emp [] []).re := by
    have := (Complex.le_def.1 hd).1
    simpa using this
  rw [D.wt_emp, div_one]; exact hre
end Formalism.FourierDecayAlt.P.Jx7
