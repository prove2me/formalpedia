-- Prove2me | solution 1 for Formalism.L2.Th1.F.zetaQuasi_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:00:49.161803+00:00
-- url     : https://prove2.me/submissions/67aa1921-aa1b-4c5c-9505-d3443b2aba7d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ZetaQuasi
import Theorems.Thm_Formalism_L2_Th1_F_WeierstrassZetaQuasiPeriod_add_notMem
import Theorems.Thm_Formalism_L2_Th1_F_WeierstrassZetaQuasiPeriod_diff_eq
import Theorems.Thm_P2M_Formalism_L2_Th1_F_WeierstrassZetaQuasiPeriod_wEta____42cf7b73a011
import Theorems.Thm_P2M_Formalism_L2_Th1_F_WeierstrassZetaQuasiPeriod_wEta____81bf5efe9be8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open WeierstrassZetaQuasiPeriod
namespace Formalism.L2.Th1.F
theorem _root_.solution (hd : ZetaHasDeriv) (ho : ZetaOdd) : ZetaQuasi := by
  intro L ω z hω hz
  let G : AddSubgroup ℂ :=
    { carrier := { w | w ∈ L.lattice ∧
        ∀ x, x ∉ L.lattice → wZeta L (x + w) = wZeta L x + wEta L w }
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨add_mem ha hb, fun x hx => ?_⟩
        rw [← add_assoc, hb' _ (add_notMem ha hx), ha' x hx, map_add, add_assoc]
      zero_mem' := ⟨zero_mem _, fun x _ => by simp⟩
      neg_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨neg_mem ha, fun x hx => ?_⟩
        have h := ha' (x + -a) (add_notMem (neg_mem ha) hx)
        rw [neg_add_cancel_right] at h
        rw [map_neg, h]; ring }
  have hG : L.lattice ≤ G.toIntSubmodule := by
    rw [PeriodPair.lattice, Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact ⟨L.ω₁_mem_lattice, fun x hx => by
        rw [wEta_ω₁]; exact diff_eq hd ho L L.ω₁_mem_lattice L.ω₁_div_two_notMem_lattice hx⟩
    · exact ⟨L.ω₂_mem_lattice, fun x hx => by
        rw [wEta_ω₂]; exact diff_eq hd ho L L.ω₂_mem_lattice L.ω₂_div_two_notMem_lattice hx⟩
  exact (hG hω).2 z hz
end Formalism.L2.Th1.F
