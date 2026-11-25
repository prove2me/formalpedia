-- Prove2me | solution 1 for Formalism.L2.Pj.lieFree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:27:45.705005+00:00
-- url     : https://prove2.me/submissions/4ff51646-130d-4a91-8ef9-1d6eac501ebd

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntFrames
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LieAlg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LieRel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LieFreePf
import Theorems.Thm_Formalism_L2_Pj_int_val
import Theorems.Thm_Formalism_L2_Pj_LieAlg_eig_basis
import Theorems.Thm_Formalism_L2_Pj_LieAlg_tri_basis
import Theorems.Thm_Formalism_L2_Pj_LieRel_comb_iff
import Theorems.Thm_Formalism_L2_Pj_LieRel_cvV_left
import Theorems.Thm_Formalism_L2_Pj_LieRel_eigV_iff
import Theorems.Thm_Formalism_L2_Pj_LieRel_isTan_cvV
import Theorems.Thm_Formalism_L2_Pj_LieRel_prod_tvec
import Theorems.Thm_Formalism_L2_Pj_LieRel_relA_eig
import Theorems.Thm_Formalism_L2_Pj_LieRel_relA_exists_v
import Theorems.Thm_Formalism_L2_Pj_LieRel_relA_exists_y
import Theorems.Thm_Formalism_L2_Pj_LieRel_relA_prod
import Theorems.Thm_Formalism_L2_Pj_LieRel_relA_scl
import Theorems.Thm_Formalism_L2_Pj_LieRel_relA_tan
import Theorems.Thm_Formalism_L2_Pj_LieRel_relA_uniq
import Theorems.Thm_Formalism_L2_Pj_LieRel_tan_eq_cvV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tanBC_alg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_spec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_eig_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_tmap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_univChartLoc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap tvec_inj tvec_eig_iff isTan_tvec tcoord tcoord_spec univChartLoc tanBC_alg
  pushR pushR_left pushR_inj pushR_map tvec_tmap fB scaleD IsUnivChart dualMapA)
open Formalism.L2.Pj.LieRel Formalism.L2.Pj.LieAlg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
set_option maxHeartbeats 800000
namespace Formalism.L2.Pj
theorem _root_.solution : LieFreeSt Xo c := by
  intro T io G t' x m1 m2 _ u₀ hu₀t hu₀e hu₀b
  let _ := io.toAlgebra
  have := G.semi.smooth
  have : ∀ a, IsMonHom (G.act.act a) := G.act.hom
  obtain ⟨n, xc, hxc⟩ := univChartLoc G.G
  obtain ⟨x', hx', hcomp⟩ := tanBC_alg (R := T.V) (R' := T.Fr) G.G n xc hxc
  have hpt : ∀ cc : Fin n → T.V, pushR G.G (tvec (x := x') (algebraMap T.V T.Fr ∘ cc)) =
      ReciprocityTheory.ChartRestriction.G.Chart.spMap (dualMapA T.V T.Fr) ≫ tvec (x := xc) cc := fun cc =>
    Over.OverMorphism.ext (by rw [pushR_left, hcomp cc]; rfl)
  have hM0 : ∀ (a : 𝓞 E) (cc : Fin n → T.V),
      tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) (algebraMap T.V T.Fr ∘ cc) =
        algebraMap T.V T.Fr ∘ tmap hxc (G.act.act a) cc := by
    intro a cc
    apply tvec_inj hx'
    apply pushR_inj G.G
    rw [tvec_tmap hx', pushR_map, hpt, hpt, tvec_tmap hxc, Category.assoc]
  have hM : ∀ (a : 𝓞 E) (cc : Fin n → T.V),
      tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) (fun j => algebraMap T.V T.Fr (cc j)) =
        fun j => algebraMap T.V T.Fr (tmap hxc (G.act.act a) cc j) := hM0
  have h1 := m1.cart
  have h2 : IsGrpPullback t'.G G.G (fB T.V T.Fr) m2.φ := m2.cart
  choose vA hvA using fun e : Fin n → T.Fr => relA_exists_v x h1 h2 (tvec (x := x') e)
  have coordA : ∀ w, IsTanAt x w → ∃ e : Fin n → T.Fr, (vA e).left = w := by
    intro w hw
    let v0 : epsAt x ⟶ Xo.univ.t.G := Over.homMk w hw.1
    obtain ⟨y0, hy0⟩ := relA_exists_y x h1 h2 v0
    have ht : ReciprocityTheory.ChartRestriction.G.Chart.IsTan y0 := (relA_tan x h1 h2 hy0).1 hw.2
    refine ⟨tcoord hx' y0 ht, ?_⟩
    exact congrArg (fun q => q.left) ((relA_uniq x h1 h2 (hvA _) hy0).2 (tcoord_spec hx' y0 ht).symm)
  have tanA : ∀ e, IsTanAt x (vA e).left := fun e =>
    ⟨Over.w (vA e), (relA_tan x h1 h2 (hvA e)).2 (isTan_tvec hx' e)⟩
  have eigA : ∀ (τ : E →+* ℂ) e, IsEigAt c τ (vA e).left ↔
      ∀ a, tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) e = io (embK c τ a) • e := by
    intro τ e
    unfold IsEigAt
    refine forall_congr' fun a => ?_
    rw [← tvec_eig_iff hx']
    exact relA_eig x h1 h2 (hvA e) (t'.act.act a) (Xo.univ.t.act.act a) (G.act.act a) (m1.act a) (m2.act a) _
  have combA : ∀ {m : ℕ} (d : Fin m → Fin n → T.Fr) (cf : Fin m → T.Fr) (e : Fin n → T.Fr),
      IsCombAt x (fun i => (vA (d i)).left) cf (vA e).left ↔ e = ∑ i, cf i • d i := by
    intro m d cf e
    have hr : ∀ i, RelA x m1.φ m2.φ (sclA x (cf i) ≫ vA (d i))
        (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (cf i)) ≫ tvec (x := x') (d i)) :=
      fun i => relA_scl x (hvA (d i)) (cf i)
    have hp := relA_prod x h1 h2 _ _ hr
    rw [prod_tvec hx'] at hp
    constructor
    · rintro ⟨u, hu, hw⟩
      have hu' : u = fun i => sclA x (cf i) ≫ vA (d i) := funext fun i => Over.OverMorphism.ext (hu i)
      subst hu'
      exact tvec_inj hx' ((relA_uniq x h1 h2 (hvA e) hp).1 (Over.OverMorphism.ext hw.symm))
    · rintro rfl
      exact ⟨fun i => sclA x (cf i) ≫ vA (d i), fun i => rfl,
        congrArg (fun q => q.left) ((relA_uniq x h1 h2 hp (hvA _)).2 rfl)⟩
  choose χ hχ using fun τ a => int_val c T io τ a
  have key : ∀ τ : E →+* ℂ, ∃ (ub : Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G))
      (u : Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left)),
      (∀ i, IsTan (ub i)) ∧ (∀ i, IsEigV c io G τ (ub i)) ∧
      (∀ (w : epsOver T.V T.V ⟶ G.G), IsTan w → IsEigV c io G τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb ub a w) ∧
      (∀ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ t'.G.left, u' ≫ m1.φ = u i ∧
        u' ≫ m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub i).left) ∧
      (∀ i, IsTanAt x (u i)) ∧ (∀ i, IsEigAt c τ (u i)) ∧
      (∀ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → T.Fr, IsCombAt x u a w) ∧
      ∀ i, ∃ cf : Fin (Dw.mult τ) → T.Fr, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧ IsCombAt x (u₀ τ) cf (u i) := by
    intro τ
    choose v hv using fun i => coordA (u₀ τ i) (hu₀t τ i)
    have hu₀ : u₀ τ = fun i => (vA (v i)).left := funext fun i => (hv i).symm
    have eigM : ∀ e, IsEigAt c τ (vA e).left ↔
        ∀ a, tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) e = algebraMap T.V T.Fr (χ τ a) • e := by
      intro e
      rw [eigA τ e]
      simp only [hχ τ]
    have hvM : ∀ a i, tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) (v i) =
        algebraMap T.V T.Fr (χ τ a) • v i := fun a i => (eigM (v i)).1 (by rw [hv i]; exact hu₀e τ i) a
    have hbM : ∀ w, (∀ a, tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) w =
        algebraMap T.V T.Fr (χ τ a) • w) → ∃! cf : Fin (Dw.mult τ) → T.Fr, w = ∑ i, cf i • v i := by
      intro w hw
      obtain ⟨cf, hcf, hu⟩ := hu₀b τ (vA w).left (tanA w) ((eigM w).2 hw)
      rw [hu₀] at hcf hu
      exact ⟨cf, (combA v cf w).1 hcf, fun cf' h' => hu cf' ((combA v cf' w).2 h')⟩
    obtain ⟨b, hbe, hbb, hbt⟩ := eig_basis (fun a => tmap hxc (G.act.act a)) (χ τ)
      (fun a => tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a))) hM v hvM hbM
    choose C hCd hCz hCb using hbt
    refine ⟨fun i => cvV (tvec (x := xc) (b i)), fun i => (vA (fun j => algebraMap T.V T.Fr (b i j))).left,
      fun i => isTan_cvV (isTan_tvec hxc (b i)), fun i a z hz => ?_, fun w hw he => ?_, fun i => ?_, fun i => tanA _,
      fun i => ?_, fun w hw he => ?_, fun i => ⟨C i, isUnit_iff_ne_zero.2 (hCd i), hCz i, ?_⟩⟩
    · have hz' : z = χ τ a := IsFractionRing.injective T.V T.Fr (hz.trans (hχ τ a).symm)
      subst hz'
      exact (eigV_iff hxc (G.act.act a) (b i) _).2 (hbe a i)
    · obtain ⟨cc, rfl⟩ := tan_eq_cvV hxc hw
      have hcc : ∀ a, tmap hxc (G.act.act a) cc = χ τ a • cc := fun a =>
        (eigV_iff hxc (G.act.act a) cc _).1 (he a (χ τ a) (hχ τ a))
      obtain ⟨r, hr, hru⟩ := hbb cc hcc
      exact ⟨r, (comb_iff hxc b r cc).2 hr, fun r' h' => hru r' ((comb_iff hxc b r' cc).1 h')⟩
    · obtain ⟨w, hw, hwl⟩ := hvA (fun j => algebraMap T.V T.Fr (b i j))
      have hw' : w.left ≫ m2.φ = (tvec (x := x') (fun j => algebraMap T.V T.Fr (b i j))).left ≫
          pullback.fst G.G.hom (fB T.V T.Fr) := hw
      refine ⟨w.left, hwl.symm, ?_⟩
      rw [cvV_left]
      exact hw'.trans (hcomp (b i))
    · refine (eigA τ _).2 fun a => ?_
      rw [hM a (b i), hbe a i, ← hχ τ a]
      funext j
      simp [Pi.smul_apply, smul_eq_mul, map_mul]
    · obtain ⟨e, rfl⟩ := coordA w hw
      have hP : ∀ a, tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) e =
          algebraMap T.V T.Fr (χ τ a) • e := (eigM e).1 he
      obtain ⟨d, hd, hdu⟩ := tri_basis (fun w => ∀ a, tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) w =
          algebraMap T.V T.Fr (χ τ a) • w) v hbM C hCz hCd e hP
      have hCb' : ∀ i, (∑ j, C i j • v j) = fun j => algebraMap T.V T.Fr (b i j) := fun i => (hCb i).symm
      simp only [hCb'] at hd hdu
      exact ⟨d, (combA _ d e).2 hd, fun d' h' => hdu d' ((combA _ d' e).1 h')⟩
    · rw [hu₀]
      exact (combA v (C i) _).2 (hCb i)
  choose ub u hub using key
  exact ⟨ub, u, ⟨fun τ i => (hub τ).1 i, fun τ i => (hub τ).2.1 i, fun τ w hw he => (hub τ).2.2.1 w hw he,
    fun τ i => (hub τ).2.2.2.1 i⟩, fun τ i => (hub τ).2.2.2.2.1 i, fun τ i => (hub τ).2.2.2.2.2.1 i,
    fun τ w hw he => (hub τ).2.2.2.2.2.2.1 w hw he, fun τ i => (hub τ).2.2.2.2.2.2.2 i⟩
end Formalism.L2.Pj
