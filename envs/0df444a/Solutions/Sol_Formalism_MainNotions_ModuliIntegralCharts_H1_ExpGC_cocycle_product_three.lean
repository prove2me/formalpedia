-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC.cocycle_product_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:44:11.141516+00:00
-- url     : https://prove2.me/submissions/6a25617f-1c3f-4abd-a390-e6aba2baf824

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CocycleProductThree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
private theorem padd_eq_lemma_2 {T : Over Xo.X} (a b : T ⟶ Xo.univ.t.G) :
    padd Xo.univ.t.G a b = a * b := rfl
private theorem pzero_eq_lemma_3 (T : Over Xo.X) : pzero Xo.univ.t.G T = 1 := rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
set_option maxHeartbeats 800000
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC
theorem _root_.solution {T : Over Xo.X} {U : Type} [CommGroup U] (h : (T.left ⟶ Xo.univ.t.G.left) → U)
    (xs : Fin 3 → (T ⟶ Xo.univ.t.G)) :
    ∏ I : thK, h (thφ Xo.univ.t.G xs I) ^ thε I =
      (h (1 : T ⟶ Xo.univ.t.G).left)⁻¹ * h (xs 0 * 1).left * h (xs 1 * 1).left * h (xs 2 * 1).left *
        (h (xs 0 * (xs 1 * 1)).left)⁻¹ * (h (xs 0 * (xs 2 * 1)).left)⁻¹ * (h (xs 1 * (xs 2 * 1)).left)⁻¹ *
          h (xs 0 * (xs 1 * (xs 2 * 1))).left := by
  have hsum : ∀ F : thK → U, ∏ I : thK, F I = ∏ s : Finset (Fin 3), F (ULift.up s) :=
    fun F => Fintype.prod_equiv (Equiv.ulift : thK ≃ Finset (Fin 3)) _ _ (fun _ => rfl)
  have hU : (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  have f0 : (List.finRange 3).filter (· ∈ (∅ : Finset (Fin 3))) = [] := by decide
  have f1 : (List.finRange 3).filter (· ∈ ({0} : Finset (Fin 3))) = [0] := by decide
  have f2 : (List.finRange 3).filter (· ∈ ({1} : Finset (Fin 3))) = [1] := by decide
  have f3 : (List.finRange 3).filter (· ∈ ({2} : Finset (Fin 3))) = [2] := by decide
  have f4 : (List.finRange 3).filter (· ∈ ({0, 1} : Finset (Fin 3))) = [0, 1] := by decide
  have f5 : (List.finRange 3).filter (· ∈ ({0, 2} : Finset (Fin 3))) = [0, 2] := by decide
  have f6 : (List.finRange 3).filter (· ∈ ({1, 2} : Finset (Fin 3))) = [1, 2] := by decide
  have f7 : (List.finRange 3).filter (· ∈ ({0, 1, 2} : Finset (Fin 3))) = [0, 1, 2] := by decide
  have c4 : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  have c5 : ({0, 2} : Finset (Fin 3)).card = 2 := by decide
  have c6 : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
  have c7 : ({0, 1, 2} : Finset (Fin 3)).card = 3 := by decide
  rw [hsum, hU, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [thφ, thε, psum, f0, f1, f2, f3, f4, f5, f6, f7, c4, c5, c6, c7, List.foldr_cons,
    List.foldr_nil, padd_eq_lemma_2, pzero_eq_lemma_3, Finset.card_empty, Finset.card_singleton]
  clear hsum hU f0 f1 f2 f3 f4 f5 f6 f7 c4 c5 c6 c7
  try norm_num only
  try simp only [zpow_one, zpow_neg, zpow_neg_one]
  repeat rw [mul_assoc (h (1 : T ⟶ Xo.univ.t.G).left)⁻¹]
  repeat rw [mul_assoc (h (xs 0 * 1).left)]
  repeat rw [mul_assoc (h (xs 1 * 1).left)]
  repeat rw [mul_assoc (h (xs 2 * 1).left)]
  repeat rw [mul_assoc (h (xs 0 * (xs 1 * 1)).left)⁻¹]
  repeat rw [mul_assoc (h (xs 0 * (xs 2 * 1)).left)⁻¹]
  all_goals exact (rfl : (0 : ℕ) = 0)
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC
