-- Prove2me | solution 1 for Formalism.L2.NCov.finrank_finset_sup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:19.442506+00:00
-- url     : https://prove2.me/submissions/af9c2968-5218-49c6-938f-a73e0d55a0de

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftLast_Pz
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.NCov
open Module Module.End
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
namespace Formalism.L2.NCov
theorem _root_.solution [FiniteDimensional K V] {ι : Type*} {p : ι → Submodule K V} (hp : iSupIndep p)
    (s : Finset ι) : finrank K ↥(s.sup p) = ∑ i ∈ s, finrank K ↥(p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hd : Disjoint (p a) (s.sup p) := by
      have := hp.disjoint_biSup (y := (s : Set ι)) (by simpa using ha)
      rw [Finset.sup_eq_iSup]
      simpa using this
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq (p a) (s.sup p)
    rw [hd.eq_bot, finrank_bot, add_zero] at h2
    rw [Finset.sup_insert, Finset.sum_insert ha, h2, ih]
end Formalism.L2.NCov
