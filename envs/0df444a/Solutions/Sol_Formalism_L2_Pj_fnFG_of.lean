-- Prove2me | solution 1 for Formalism.L2.Pj.fnFG_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:28:23.306353+00:00
-- url     : https://prove2.me/submissions/691cb300-855a-4d74-a924-b1784d49e60f

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompHt
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FnTrdegOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)
namespace Formalism.L2.Pj
theorem _root_.solution (h : KapFG Xo c) : FnFG Xo c := by
  intro Z
  classical
  obtain ⟨s, hs⟩ := h Z
  have hfin : (Set.range fun i : FlagVar Dw =>
      algebraMap (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z) (MvPolynomial.X i)).Finite := Set.finite_range _
  refine ⟨s.image (algebraMap (kap Z) (Om Z)) ∪ hfin.toFinset, ?_⟩
  set K := IntermediateField.adjoin c.F
    ((s.image (algebraMap (kap Z) (Om Z)) ∪ hfin.toFinset : Finset (Om Z)) : Set (Om Z)) with hK
  have hC : ∀ a : kap Z, algebraMap (kap Z) (Om Z) a ∈ K := by
    intro a
    have ha : a ∈ IntermediateField.adjoin c.F (s : Set (kap Z)) := by
      rw [hs]
      exact IntermediateField.mem_top
    have h1 : IsScalarTower.toAlgHom c.F (kap Z) (Om Z) a ∈
        (IntermediateField.adjoin c.F (s : Set (kap Z))).map (IsScalarTower.toAlgHom c.F (kap Z) (Om Z)) :=
      by
        first
          | exact ⟨a, ha, rfl⟩
          | (rw [← SetLike.mem_coe, IntermediateField.coe_map]; exact Set.mem_image_of_mem _ ha)
    rw [IntermediateField.adjoin_map] at h1
    refine IntermediateField.adjoin.mono _ _ _ ?_ h1
    rintro _ ⟨b, hb, rfl⟩
    exact Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb))
  have hP : ∀ q : MvPolynomial (FlagVar Dw) (kap Z),
      algebraMap (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z) q ∈ K := by
    intro q
    induction q using MvPolynomial.induction_on
    next a =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact hC a
    next p₁ p₂ h₁ h₂ =>
      rw [map_add]
      exact K.add_mem h₁ h₂
    next p₁ i h₁ =>
      rw [map_mul]
      refine K.mul_mem h₁ (IntermediateField.subset_adjoin c.F _ ?_)
      exact Finset.mem_coe.mpr (Finset.mem_union_right _ (hfin.mem_toFinset.mpr ⟨i, rfl⟩))
  rw [eq_top_iff]
  rintro x -
  obtain ⟨⟨p₁, p₂⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (nonZeroDivisors (MvPolynomial (FlagVar Dw) (kap Z))) x
  dsimp only
  rw [IsFractionRing.mk'_eq_div]
  exact K.div_mem (hP p₁) (hP p₂)
end Formalism.L2.Pj
