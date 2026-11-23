-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.nodeBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:33.511038+00:00
-- url     : https://prove2.me/submissions/a874710b-0a84-4853-9796-003894bf563c

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaFactorisation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.Sz Finset
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : NodeBound := by
  intro c Y l h hl hlk hY
  obtain ⟨hY1, hY2⟩ := hY
  have hD := h.hDel
  have hD0 : 0 < c.Del := by linarith
  have hb1 := h.hb1
  have hbj : ∀ j : ℕ, 1 ≤ j → j ≤ c.m → c.b 1 ≤ c.b j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ n hn ih =>
      intro hm
      have i1 := ih (by omega)
      have i2 := h.hgap n hn (by omega)
      linarith
  have hl1 : (1:ℝ) ≤ l := by exact_mod_cast hl
  have hlR : (l:ℝ) + 2 ≤ c.k := by exact_mod_cast hlk
  have hvl : c.v l ≤ c.v 1 := by simp only [Cfg.v]; push_cast; nlinarith
  have hvl' : c.v l = c.vlast + 4 * c.Del * ((c.k:ℝ) - 1 - l) := rfl
  have m1 : 4 * c.Del * 1 ≤ 4 * c.Del * ((c.k:ℝ) - 1 - l) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hv0 := h.hv0
  have hv1 := h.hv1
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = -Y := ⟨_, rfl⟩
  rw [← hy]
  have hy1 : 1 ≤ y := by rw [hy]; linarith
  have hy2 : y ≤ 4 * c.k * c.Del := by rw [hy]; linarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (4 * c.k * c.Del / c.b 1) := ⟨_, rfl⟩
  have hterm : ∀ j ∈ Icc 1 c.m, Real.sqrt ((c.b j + y) * (c.b j + y - 1)) ≤ c.b j * E := by
    intro j hj
    rw [mem_Icc] at hj
    have hb := hbj j hj.1 hj.2
    have hbpos : 0 < c.b j := by linarith
    have s1 : Real.sqrt ((c.b j + y) * (c.b j + y - 1)) ≤ c.b j + y := by
      rw [Real.sqrt_le_iff]; exact ⟨by linarith, by nlinarith⟩
    have s2 : c.b j + y ≤ c.b j * E := by
      have t1 : 1 + 4 * c.k * c.Del / c.b 1 ≤ E := by
        have := Real.add_one_le_exp (4 * c.k * c.Del / c.b 1); rw [hE]; linarith
      have t2 : y / c.b j ≤ 4 * c.k * c.Del / c.b 1 :=
        div_le_div₀ (by positivity) hy2 (by linarith) hb
      calc c.b j + y = c.b j * (1 + y / c.b j) := by field_simp
        _ ≤ c.b j * E := mul_le_mul_of_nonneg_left (by linarith) hbpos.le
    exact s1.trans s2
  simp only [Cfg.Nd, Cfg.prodb]
  calc ∏ j ∈ Icc 1 c.m, Real.sqrt ((c.b j + y) * (c.b j + y - 1))
      ≤ ∏ j ∈ Icc 1 c.m, (c.b j * E) := prod_le_prod (fun _ _ => Real.sqrt_nonneg _) hterm
    _ = (∏ j ∈ Icc 1 c.m, c.b j) * E ^ c.m := by
        rw [prod_mul_distrib, prod_const, Nat.card_Icc]; simp
    _ = Real.exp c.vth * ∏ j ∈ Icc 1 c.m, c.b j := by
        rw [mul_comm]; congr 1
        rw [hE, ← Real.exp_nat_mul]; congr 1; simp only [Cfg.vth]; ring
end Formalism.FourierDecayAlt.P
