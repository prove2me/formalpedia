-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.exists_value
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:46:59.912541+00:00
-- url     : https://prove2.me/submissions/ea3e0307-3783-41ce-8694-f05500887ff5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDVal

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
theorem _root_.solution (hL : L.IsLB) (a : ℤ) {T : Over S0} (s : LB.Sec (LPow A L a T)) (z : T ⟶ A)
    (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))) (hτ : τ.IsGen) :
    ∃ v, IsValueAt A L a s z τ v := by
  have hpz : (ptSecT A z).left ≫ (snd T A).left = z.left := by
    rw [← Over.comp_left]
    simp [ptSecT]
  obtain ⟨w, hw⟩ : ∃ w : ∀ j : Fin 1 → L.ι, Γ(T.left, LB.wchart L (fun _ : Fin 1 => z.left) j),
      ∀ j, w j = (T.left.presheaf.map (homOfLE (val_le A L z j)).op).hom (((ptSecT A z).left.app _).hom (s.f j)) *
        (show Γ(T.left, LB.wchart L (fun _ : Fin 1 => z.left) j) from ((τ.s j)⁻¹).val) := ⟨_, fun _ => rfl⟩
  have loc : ∀ j x, x ∈ LB.wchart L (fun _ : Fin 1 => z.left) j →
      gs (𝟙 _) x _ (w j) = gs (𝟙 _ ≫ (ptSecT A z).left) x _ (s.f j) * ((gm (𝟙 _) x _ (τ.s j))⁻¹).val := by
    intro j x hx
    rw [hw j]
    refine (gs_mul _ x _ hx _ _).trans (congrArg₂ (· * ·) ((gs_res (𝟙 _) x (val_le A L z j) hx _).trans
      (gs_pull (𝟙 _) (ptSecT A z).left x _ (val_le A L z j hx) _)) ?_)
    exact (gs_unit (𝟙 _) x _ hx ((τ.s j)⁻¹)).trans (congrArg Units.val (map_inv _ _))
  have hcompat : TopCat.Presheaf.IsCompatible T.left.sheaf.val (fun j : Fin 1 → L.ι => LB.wchart L (fun _ : Fin 1 => z.left) j) w := by
    intro j j'
    apply fn_ext
    intro x hx
    change gs (𝟙 _) x _ ((T.left.presheaf.map (homOfLE inf_le_left).op).hom (w j)) =
      gs (𝟙 _) x _ ((T.left.presheaf.map (homOfLE inf_le_right).op).hom (w j'))
    rw [gs_res _ x _ hx, gs_res _ x _ hx, loc j x hx.1, loc j' x hx.2]
    rw [show gs (𝟙 _ ≫ (ptSecT A z).left) x ((LPow A L a T).U j) (s.f j) = _ from
      sec_trans (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s _ x
        (val_le A L z j hx.1) (val_le A L z j' hx.2)]
    rw [show gm (𝟙 _) x ((LB.LinComb L (fun _ : Fin 1 => z.left) fun _ => a).U j) (τ.s j) = _ from
      gen_trans hτ (𝟙 _) x hx.1 hx.2]
    have ht : trF (L := L) (fun _ : Fin 1 => (snd T A).left) (fun _ => a) (𝟙 _ ≫ (ptSecT A z).left) x j j' =
        trF (L := L) (fun _ : Fin 1 => z.left) (fun _ => a) (𝟙 _) x j j' := by
      simp only [trF, Category.assoc, hpz]
    rw [ht, mul_inv_rev, Units.val_mul]
    have key : ∀ (t G : (T.left.presheaf.stalk x)ˣ) (P : T.left.presheaf.stalk x),
        (t : T.left.presheaf.stalk x) * P * (((G⁻¹ : (T.left.presheaf.stalk x)ˣ) : T.left.presheaf.stalk x) *
          ((t⁻¹ : (T.left.presheaf.stalk x)ˣ) : T.left.presheaf.stalk x)) =
          P * ((G⁻¹ : (T.left.presheaf.stalk x)ˣ) : T.left.presheaf.stalk x) := by
      intro t G P
      linear_combination (P * ((G⁻¹ : (T.left.presheaf.stalk x)ˣ) : T.left.presheaf.stalk x)) * Units.mul_inv t
    exact key _ _ _
  have hcov : (⊤ : T.left.Opens) ≤ ⨆ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => z.left) j := by
    intro x _
    have hx : z.left x ∈ (⨆ i, L.U i) := by
      rw [hL.cover]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, Set.mem_iInter.2 fun _ => hi⟩
  obtain ⟨v, hv, -⟩ := TopCat.Sheaf.existsUnique_gluing' T.left.sheaf
    (fun j : Fin 1 → L.ι => LB.wchart L (fun _ : Fin 1 => z.left) j) ⊤ (fun j => homOfLE le_top) hcov w hcompat
  refine ⟨v, fun j => ?_⟩
  have e : (T.left.presheaf.map (homOfLE le_top).op).hom v = w j := hv j
  have key : ∀ (R : Type) [CommRing R] (p : R) (t : Rˣ), p = p * ((t⁻¹ : Rˣ) : R) * (t : R) := by
    intro R _ p t
    rw [mul_assoc, Units.inv_mul, mul_one]
  rw [e, hw j]
  exact key _ _ (τ.s j)
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
