-- Prove2me | solution 1 for ClauseBound.ParityChecks.Run.numO_div_den
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:13:27.855204+00:00
-- url     : https://prove2.me/submissions/67946a74-bf64-48d0-8584-50c4db16e71e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_Num
import Definitions.Def_ClauseBound_ParityChecks_Congr
import Definitions.Def_ClauseBound_ParityChecks_Run
import Theorems.Thm_ClauseBound_ParityChecks_Run_num_congr
import Theorems.Thm_ClauseBound_ParityChecks_Approx_abs_le
import Theorems.Thm_ClauseBound_ParityChecks_bal_eq
import Theorems.Thm_ClauseBound_ParityChecks_num_div_den


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
theorem _root_.solution (H2 : ChoiceByPotential) (hq : Hyp q (Fintype.card X) ε) (ho : OrcOK q V orcA orcB) {Ls : List Chk} {cur : Chk} {e : ℕ} (hj : Ls.length < q.r)
    (hL : ∀ L ∈ Ls, ChkOK q.m L) (hc : ChkOK e cur) (he : e ≤ q.m) (hT : Tent q (lam q.m (Ls ++ [cur]))) :
    (q.numO orcA orcB Ls cur e : ℚ) / q.den Ls.length = tUU q V Ls cur e := by
  obtain ⟨hA, hB⟩ := ho Ls cur e hj hL hc he hT
  have hβ : 1 ≤ q.β := by have := hq.β_pos; omega
  have hpow : (2 : ℤ) ^ (q.β - 2) < 2 ^ (q.β - 1) := pow_lt_pow_right₀ (by norm_num) (by have := hq.β_pos; omega)
  have habs := fun i => H2.abs_le X (Fin q.m) V q.nb i Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e)
  simp only [Fintype.card_fin] at habs
  have hA' : bal q.β (orcA Ls) = Aint V q.nb Ls.length (lam q.m (Ls ++ [cur])) := by
    refine bal_eq hβ (lt_of_le_of_lt ((habs 0).1.trans ?_) hpow) hA
    have := hq.small 0 (Nat.zero_le _)
    rw [Nat.choose_zero_right, Nat.mul_one] at this
    exact_mod_cast this
  have hB' : ∀ i ≤ q.i₀, bal q.β (orcB Ls cur e i) = Bint V q.nb i Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) := fun i hi => by
    refine bal_eq hβ (lt_of_le_of_lt ((habs i).2.trans ?_) hpow) (hB i hi)
    exact_mod_cast hq.small i hi
  unfold Par.numO
  rw [hA', num_congr _ hB']
  exact num_div_den q V (by have := hq.nb_two; omega) hq.m_pos hj hL hc he
end ClauseBound.ParityChecks.Run
