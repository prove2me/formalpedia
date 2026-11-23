-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.edge_factor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:38.834221+00:00
-- url     : https://prove2.me/submissions/e03fe1ef-ec29-460a-9ba2-4036ec21f9d0

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_u_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz4
theorem _root_.solution (c : Cfg) (de : ℕ → ℝ) (hc : c.Ok) (hw : IsWord c.k de) (i : ℕ) (h2 : 2 ≤ i)
    (hik : i ≤ c.k) (h : i < c.k ∨ c.top = false) :
    c.a - c.v 1 ≤ c.a - c.u de i ∧ c.a - c.u de i ≤ 2 * (c.a - c.v 1) := by
  obtain ⟨l, rfl⟩ : ∃ l, i = l + 1 := ⟨i - 1, by omega⟩
  have h' : l + 2 ≤ c.k ∨ c.top = false := by
    rcases h with h | h
    · left; omega
    · right; exact h
  rw [u_succ c de hw l (by omega) hik h']
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
  have hlk : (l : ℝ) + 1 ≤ c.k := by exact_mod_cast hik
  have hD := hc.hDel
  have ha := hc.ha
  have hv : c.v l = c.v 1 - 4 * c.Del * ((l : ℝ) - 1) := by unfold Cfg.v; push_cast; ring
  rw [hv]
  have m1 : 0 ≤ c.Del * ((l : ℝ) - 1) := mul_nonneg (by linarith) (by linarith)
  have m2 : 0 ≤ c.Del * ((c.k : ℝ) - 1 - l) := mul_nonneg (by linarith) (by linarith)
  rcases hw.1 l with e | e <;> rw [e] <;> constructor <;> nlinarith
end Formalism.FourierDecayAlt.P.Sz4
