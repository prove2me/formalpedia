-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.exists_series
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:14:36.159938+00:00
-- url     : https://prove2.me/submissions/6dd1b4f1-e346-4dff-8b63-d77a52b91095

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBFr
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_val_scale
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_exists_ratio
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_exists_ps_of_jets
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_exists_chart
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_to__injective_2d1b9ff55e5a
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
theorem _root_.solution {n : ℕ} {K K' : Type} [Fintype K] [Fintype K']
    (φ : ∀ m, K → ((jOG x0 d m n).left ⟶ t.G.left)) (ε : K → ℤ)
    (φ' : ∀ m, K' → ((jOG x0 d m n).left ⟶ t.G.left)) (ε' : K' → ℤ)
    (A : ∀ m, LB.Gen (LB.LinComb t.PP.L (φ m) ε)) (hA : ∀ m, (A m).IsGen)
    (B : ∀ m, LB.Gen (LB.LinComb t.PP.L (φ' m) ε')) (hB : ∀ m, (B m).IsGen)
    (hF : ∀ m, FormEq (φ m) ε (φ' m) ε')
    (hAt : ∀ m y J, Good t.PP.L y J → val (A (m + 1)) (ρn x0 d n m).left y J = val (A m) (𝟙 _) y J)
    (hBt : ∀ m y J, Good t.PP.L y J → val (B (m + 1)) (ρn x0 d n m).left y J = val (B m) (𝟙 _) y J) :
    ∃ ph : MvPowerSeries (Fin n × Fin d) S, ∀ m, ∃ u : (Jet S (Fin n × Fin d) m)ˣ,
      (u : Jet S (Fin n × Fin d) m) = psJet m ph ∧
      LB.Gen.Corr t.PP.L _ _ _ _ (A m) (scaleGenG t _ _ (unitΓ u) (B m)) := by
  have hL := t.PP.isLB
  choose U hU using fun m => exists_ratio t.PP.L hL (hF m) (A m) (hA m) (B m) (hB m)
  have hv : ∀ m, ∃ v : (Jet S (Fin n × Fin d) m)ˣ, unitΓ v = U m := fun m =>
    ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of (Jet S (Fin n × Fin d) m))).hom.hom.toMonoidHom (U m),
      Units.ext (congrArg (fun f => CommRingCat.Hom.hom f (U m).val)
        (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of (Jet S (Fin n × Fin d) m)))))⟩
  choose v hv using hv
  have hUc : ∀ m, U m = pullU (ρn x0 d n m).left ⊤ (U (m + 1)) := by
    intro m
    refine unit_ext (V := ⊤) fun y _ => ?_
    choose I hI using fun χ : (jOG x0 d m n).left ⟶ t.G.left => exists_chart hL (χ y)
    have e1 := hU m _ (𝟙 _) y I hI
    have e2 := hU (m + 1) _ (ρn x0 d n m).left y I hI
    have e3 := gm_pull (𝟙 _) (ρn x0 d n m).left y ⊤ trivial (U (m + 1))
    rw [Category.id_comp] at e3
    refine Eq.trans ?_ e3.symm
    exact (mul_inv_eq_iff_eq_mul.2 e1).symm.trans ((congrArg₂ (fun a b => a * b⁻¹) (hAt m y I hI).symm
      (hBt m y I hI).symm).trans (mul_inv_eq_iff_eq_mul.2 e2))
  have hac : ∀ m, (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] _) (v (m + 1)) = v m := by
    intro m
    apply toΓ_injective
    have e1 := congrArg Units.val (hv m)
    have e2 := congrArg Units.val (hv (m + 1))
    have nat := congrArg (fun f => CommRingCat.Hom.hom f ((v (m + 1) : Jet S (Fin n × Fin d) (m + 1))))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ((jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] _) :
        Jet S (Fin n × Fin d) (m + 1) →+* Jet S (Fin n × Fin d) m)))
    refine nat.trans (Eq.trans ?_ e1.symm)
    refine (congrArg (fun a => ((ρn x0 d n m).left.appTop).hom a) e2).trans ?_
    rw [hUc m]
    rfl
  obtain ⟨ph, hph⟩ := exists_ps_of_jets (fun m => (v m : Jet S (Fin n × Fin d) m)) hac
  refine ⟨ph, fun m => ⟨v m, (hph m).symm, corr_of_val hL fun y J hJ => ?_⟩⟩
  exact (hU m _ (𝟙 _) y J hJ).trans ((congrArg (fun u => gm (𝟙 _) y ⊤ u * val (B m) (𝟙 _) y J) (hv m).symm).trans
    (val_scale t _ _ _ _ _ y J hJ).symm)
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
