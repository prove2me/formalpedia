-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.orig_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:48:00.430291+00:00
-- url     : https://prove2.me/submissions/b333261f-b771-48b1-9d20-908289562a35

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFun
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_mem_ordGE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
theorem _root_.solution (R ι : Type) [CommRing R] (n : ℕ) : orig R ι ^ n ≤ ordGE R ι n := by
  induction n with
  | zero =>
    intro p _
    rw [mem_ordGE]
    intro e _
    exact Nat.zero_le _
  | succ n ih =>
    rw [pow_succ]
    refine le_trans (Ideal.mul_mono_left ih) ?_
    unfold orig
    rw [Ideal.mul_le]
    intro p hp q hq
    induction hq using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [mem_ordGE] at hp ⊢
      intro e he
      rw [MvPolynomial.support_mul_X, Finset.mem_map] at he
      obtain ⟨d, hd, rfl⟩ := he
      have h1 := hp d hd
      have h2 : (d + Finsupp.single i 1).degree = d.degree + 1 := by
        simp [map_add]
      simp only [addRightEmbedding_apply, h2]
      omega
    | zero => simp
    | add x y _ _ hx hy =>
      rw [mul_add]
      exact Ideal.add_mem _ hx hy
    | smul a x _ hx =>
      rw [smul_eq_mul, mul_left_comm]
      exact Ideal.mul_mem_left _ a hx
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
