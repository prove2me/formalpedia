-- Prove2me | solution 1 for Formalism.HN.exists_smul_mem_of_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:19.264074+00:00
-- url     : https://prove2.me/submissions/ca52c39f-97ee-4a2f-a4bd-46300942806a

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq

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
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution {E : Type*} [AddCommGroup E] (S N : Submodule ℤ E) [Module.Finite ℤ S]
    (hNS : N ≤ S) (hrk : finrank ℤ S = finrank ℤ N) :
    ∀ x ∈ S, ∃ a : ℤ, a ≠ 0 ∧ a • x ∈ N := by
  intro x hx
  set P : Submodule ℤ S := N.comap S.subtype with hP
  have hPr : finrank ℤ P = finrank ℤ N :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hNS)
  have h := P.finrank_quotient_add_finrank
  have h0 : finrank ℤ (S ⧸ P) = 0 := by omega
  obtain ⟨a, ha, hax⟩ := (Module.finrank_eq_zero_iff.1 h0) (Submodule.Quotient.mk ⟨x, hx⟩)
  refine ⟨a, ha, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hax
  exact hax
end Formalism.HN
