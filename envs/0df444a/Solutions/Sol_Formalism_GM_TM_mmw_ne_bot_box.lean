-- Prove2me | solution 1 for Formalism.GM.TM.mmw_ne_bot_box
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:32:34.044065+00:00
-- url     : https://prove2.me/submissions/7bc413e6-e30c-4708-88ab-40fcb0868d54

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Theorems.Thm_Formalism_GM_TM_wt_abs_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.GM.TM
theorem _root_.solution {K r : ℕ} [NeZero r] (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (ρ : Fin r) (w : Fin r → ℤ) (h : MMw p LLw J M ρ w ≠ ⊥) :
    w ∈ Fintype.piFinset (fun _ : Fin r => Icc (-(LLw.total : ℤ)) LLw.total) := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨m, hm⟩ : ∃ m, m ∈ x.support := by
    by_contra hc; push Not at hc
    exact hx0 (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))
  unfold MMw at hx
  have hY := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hx).1).1
  have hW := (Submodule.mem_inf.mp hx).2
  have hP : x ∈ Pol p r LLw := (Submodule.mem_inf.mp hY).1
  rw [Pol, mem_restrictSupport_iff] at hP
  rw [WtSpC, mem_restrictSupport_iff] at hW
  have hmd : MultiDeg LLw m := hP (Finset.mem_coe.mpr hm)
  have hwt : ∀ c ∈ (univ : Finset (Fin r)), wt LLw K c m = w c := hW (Finset.mem_coe.mpr hm)
  rw [Fintype.mem_piFinset]
  intro c
  have := wt_abs_le LLw K c m hmd
  rw [hwt c (mem_univ _)] at this
  rw [mem_Icc]; constructor <;> linarith [abs_le.mp this]
end Formalism.GM.TM
