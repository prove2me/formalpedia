-- Prove2me | solution 1 for ClauseBound.ParityChecks.Run.Inv.step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:19:51.371459+00:00
-- url     : https://prove2.me/submissions/a5bbccf9-ad0a-416d-9814-00a51d9149cb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_Num
import Definitions.Def_ClauseBound_ParityChecks_Congr
import Definitions.Def_ClauseBound_ParityChecks_Run
import Theorems.Thm_ClauseBound_ParityChecks_Run_chkOK_mono
import Theorems.Thm_ClauseBound_ParityChecks_Run_chkOK_snoc
import Theorems.Thm_ClauseBound_ParityChecks_Run_mem_Dset
import Theorems.Thm_ClauseBound_ParityChecks_Run_Dset_succ
import Theorems.Thm_ClauseBound_ParityChecks_Run_lam_putIn
import Theorems.Thm_ClauseBound_ParityChecks_Run_abs_tUU_sub
import Theorems.Thm_ClauseBound_ParityChecks_Run_numO_div_den
import Theorems.Thm_ClauseBound_ParityChecks_Run_Inv_tent
import Theorems.Thm_ClauseBound_ParityChecks_Approx_abs_le
import Theorems.Thm_ClauseBound_ParityChecks_den_pos
import Theorems.Thm_ClauseBound_ParityChecks_isState


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m)) (orcA : List Chk → ℤ) (orcB : List Chk → Chk → ℕ → ℕ → ℤ)
open ClauseBound.ParityChecks.Run
variable {q}
variable {V} {orcA orcB} {ε : ℚ}
namespace ClauseBound.ParityChecks.Run
namespace Inv
theorem _root_.solution (H2 : ChoiceByPotential) (hq : Hyp q (Fintype.card X) ε) (ho : OrcOK q V orcA orcB) {Ls : List Chk} {cur : Chk} {e : ℕ} (h : Inv q V ε Ls cur e)
    (he : e < q.m) : Inv q V ε Ls (q.decide1 orcA orcB Ls cur e) (e + 1) := by
  obtain ⟨hTi, hTo⟩ := h.tent H2 hq he
  have hci : ChkOK (e + 1) (cur ++ [e]) := chkOK_snoc h.okc
  have hco : ChkOK (e + 1) cur := chkOK_mono (Nat.le_succ e) h.okc
  have hni := numO_div_den H2 hq ho h.lt h.done hci he hTi
  have hno := numO_div_den H2 hq ho h.lt h.done hco he hTo
  have hden : (0 : ℚ) < q.den Ls.length := by
    exact_mod_cast den_pos q (by have := hq.nb_two; omega) hq.m_pos hq.r_pos Ls.length
  -- the old potential is a mean of the two new ones
  have hmart : pr q.nb * UU q V Ls (cur ++ [e]) (e + 1) + (1 - pr q.nb) * UU q V Ls cur (e + 1) = UU q V Ls cur e := by
    have := H2.martingale X (Fin q.m) V q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) ⟨e, he⟩ hq.nb_two (isState q h.lt h.okc) (mem_Dset he)
    unfold UU
    rw [lam_putIn Ls cur he, Dset_succ he]
    exact this
  have hp0 : 0 < pr q.nb := by
    unfold pr
    have : (0 : ℚ) < q.nb := by exact_mod_cast (by have := hq.nb_two; omega : 0 < q.nb)
    positivity
  have hp1 : pr q.nb ≤ 1 / 2 := by
    unfold pr
    have : (2 : ℚ) ≤ q.nb := by exact_mod_cast hq.nb_two
    exact one_div_le_one_div_of_le (by norm_num) this
  have hai := abs_le.1 (abs_tUU_sub (V := V) H2 hq Ls (cur ++ [e]) (e + 1))
  have hao := abs_le.1 (abs_tUU_sub (V := V) H2 hq Ls cur (e + 1))
  have hpot := h.pot
  have hcast : ((Ls.length * q.m + (e + 1) : ℕ) : ℚ) = ((Ls.length * q.m + e : ℕ) : ℚ) + 1 := by push_cast; ring
  have key : ∀ c : Chk, ChkOK (e + 1) c → tUU q V Ls c (e + 1) ≤ tUU q V Ls (cur ++ [e]) (e + 1) → tUU q V Ls c (e + 1) ≤ tUU q V Ls cur (e + 1) →
      |tUU q V Ls c (e + 1) - UU q V Ls c (e + 1)| ≤ 1 / 2 * ε * NN X q → Inv q V ε Ls c (e + 1) := by
    intro c hc h1 h2 h3
    refine ⟨h.lt, h.done, hc, he, ?_⟩
    rw [hcast]
    have h3' := abs_le.1 h3
    have hmin : UU q V Ls (cur ++ [e]) (e + 1) ≤ UU q V Ls cur e ∨ UU q V Ls cur (e + 1) ≤ UU q V Ls cur e := by
      by_contra hcon
      push Not at hcon
      nlinarith [hcon.1, hcon.2]
    rcases hmin with hm | hm <;> linarith [h3'.1, h3'.2, hai.1, hai.2, hao.1, hao.2]
  unfold Par.decide1
  split_ifs with hle
  · refine key _ hci le_rfl ?_ (abs_tUU_sub H2 hq _ _ _)
    rw [← hni, ← hno]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hle) hden.le
  · refine key _ hco ?_ le_rfl (abs_tUU_sub H2 hq _ _ _)
    rw [← hni, ← hno]
    exact div_le_div_of_nonneg_right (by exact_mod_cast (not_le.1 hle).le) hden.le
end Inv
end ClauseBound.ParityChecks.Run
