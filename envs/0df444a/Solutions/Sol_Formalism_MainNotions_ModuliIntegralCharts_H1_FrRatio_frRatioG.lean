-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio.frRatioG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:42:58.749404+00:00
-- url     : https://prove2.me/submissions/37c4a6f5-7c31-4db5-9489-0db810404a34

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFixAsm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrRatio
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrRatio_psJet_trunc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrRatio_triple_lift_truncation
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrRatio_pair_lift_truncation
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrRatio_pe_tr
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrRatio_alg1
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrRatio_alg2
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrRatio_alg3
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrRatio_gm_map
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrRatio_exists_ratioU
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_psIn_succ_sub
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_val_scale
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_exists_chart
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_to__injective_2d1b9ff55e5a
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}
set_option maxHeartbeats 4000000
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio
theorem _root_.solution (hch : IsChartG t x0 d F act tg uvec x) {ph1 ph2 sy ad} {e : ∀ m, FrTyG t x0 d x m}
    (hfr : IsFrameG t x0 d x F act ph1 ph2 sy ad e) (m : ℕ) :
    ∃ U : (Jet S (Fin 2 × Fin d) m)ˣ,
      LB.Gen.Corr t.PP.L _ _ _ _
        (LB.pullGen t.PP.L _ _ (e (m + 1)) (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _)).left)
        (scaleGenG t _ _ (unitΓ U) (e m)) ∧
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => psIn d m (![0, 1] : Fin 2 → Fin 3) (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m) = jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m) * jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m) ∧
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m) = U ∧
      ∀ a : 𝓞 E, jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => psIn d m ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m) = jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m) := by
  have hL := t.PP.isLB
  obtain ⟨U, hU⟩ := exists_ratioU hch e hfr.gen m
  have hσ : ∀ {n : ℕ} (v : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S) (y : (jOG x0 d m n).left)
      (J : ((jOG x0 d m n).left ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L y J →
      val (e (m + 1)) ((homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => v p.1 p.2)).left ≫
        (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _)).left) y J =
      gm (𝟙 _) y ⊤ (unitΓ (Units.map ((jetSubstP m fun p : Fin 2 × Fin d => v p.1 p.2 :
          Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m) : _ →* _) U)) *
        val (peG t x0 d x e m v) (𝟙 _) y J := fun v y J hJ =>
    (hU _ _ y J hJ).trans (congrArg₂ (· * ·) (gm_map _ U y)
      ((congrArg (fun r => val (e m) r y J) (Category.id_comp _).symm).trans (val_pull hJ _ _ _).symm))
  have hXX : ∀ {n : ℕ} (k : Fin n) (j : Fin d),
      (MvPolynomial.X (k, j) : MvPolynomial (Fin n × Fin d) S) - MvPolynomial.X (k, j) ∈
        orig S (Fin n × Fin d) ^ (m + 1) := fun k j => by simp
  have hunit : ∀ {A : Type} [CommRing A] [Algebra S A] (a b c : Aˣ),
      (∀ y, gm (𝟙 (overAt x0 A).left) y ⊤ (unitΓ a) = gm (𝟙 _) y ⊤ (unitΓ b) * gm (𝟙 _) y ⊤ (unitΓ c)) →
      (a : A) = b * c := by
    intro A _ _ a b c h
    have hu : unitΓ a = unitΓ b * unitΓ c := unit_ext (V := ⊤) fun y _ => (h y).trans (map_mul _ _ _).symm
    exact toΓ_injective A ((congrArg Units.val hu).trans (map_mul _ _ _).symm)
  have hunit2 : ∀ {A : Type} [CommRing A] [Algebra S A] (a b : Aˣ),
      (∀ y, gm (𝟙 (overAt x0 A).left) y ⊤ (unitΓ a) = gm (𝟙 _) y ⊤ (unitΓ b)) → (a : A) = b := by
    intro A _ _ a b h
    have hu : unitΓ a = unitΓ b := unit_ext (V := ⊤) fun y _ => h y
    exact toΓ_injective A (congrArg Units.val hu)
  have htr : ∀ {n : ℕ} (u' : (Jet S (Fin n × Fin d) (m + 1))ˣ) (u : (Jet S (Fin n × Fin d) m)ˣ) (f),
      (u' : Jet S (Fin n × Fin d) (m + 1)) = psJet (m + 1) f → (u : Jet S (Fin n × Fin d) m) = psJet m f →
      ∀ y, gm (ρn x0 d n m).left y ⊤ (unitΓ u') = gm (𝟙 _) y ⊤ (unitΓ u) := by
    intro n u' u f h' h y
    refine (gm_map _ u' y).trans (congrArg (fun w => gm (𝟙 _) y ⊤ (unitΓ w)) (Units.ext ?_))
    simp only [Units.coe_map, MonoidHom.coe_coe]
    rw [h', h]
    exact psJet_trunc m f
  refine ⟨U, corr_of_val hL fun y J hJ => ?_, ?_, ?_, fun a => ?_⟩
  · exact (val_pull hJ _ _ _).trans ((hU _ (𝟙 _) y J hJ).trans (val_scale t _ _ _ _ _ y J hJ).symm)
  · refine hunit (Units.map ((jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => psIn d m (![0, 1] : Fin 2 → Fin 3) (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 3 × Fin d) m) : Jet S (Fin 2 × Fin d) m →* Jet S (Fin 3 × Fin d) m) U) (Units.map ((jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 3 × Fin d) m) : Jet S (Fin 2 × Fin d) m →* Jet S (Fin 3 × Fin d) m) U) (Units.map ((jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 3 × Fin d) m) : Jet S (Fin 2 × Fin d) m →* Jet S (Fin 3 × Fin d) m) U) fun y => ?_
    choose J hJ using fun χ : (jOG x0 d m 3).left ⟶ t.G.left => exists_chart hL (χ y)
    obtain ⟨u1, hu1, hc1⟩ := hfr.ph1 m
    obtain ⟨u1', hu1', hc1'⟩ := hfr.ph1 (m + 1)
    have E0 := (val_corr hJ hc1 (𝟙 _)).trans (val_scale t _ _ _ _ _ y J hJ)
    have E1 := (val_corr hJ hc1' (ρn x0 d 3 m).left).trans (val_scale t _ _ _ _ _ y J hJ)
    rw [val_mul hJ, val_mul hJ, val_inv, val_inv] at E0 E1
    have hth : val (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (lift (jptG t x0 d x (m + 1) (0 : Fin 3))
        (lift (jptG t x0 d x (m + 1) (1 : Fin 3)) (jptG t x0 d x (m + 1) (2 : Fin 3)))).left) (ρn x0 d 3 m).left y J =
        val (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (lift (jptG t x0 d x m (0 : Fin 3))
          (lift (jptG t x0 d x m (1 : Fin 3)) (jptG t x0 d x m (2 : Fin 3)))).left) (𝟙 _) y J :=
      (val_pull hJ _ _ _).trans ((congrArg (fun r => val t.cub.t r y J)
        ((triple_lift_truncation hch m 0 1 2).trans (Category.id_comp _).symm)).trans (val_pull hJ _ _ _).symm)
    rw [hth, htr u1' u1 ph1 hu1' hu1 y,
      pe_tr e m (![fun j => psIn d (m + 1) (![0, 1] : Fin 2 → Fin 3) (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) (![fun j => psIn d m (![0, 1] : Fin 2 → Fin 3) (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) (fun i j => by fin_cases i; exacts [psIn_succ_sub m _ _, hXX _ j]) y J hJ,
      pe_tr e m (![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) (![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) (fun i j => by fin_cases i <;> exact hXX _ j) y J hJ,
      pe_tr e m (![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) (![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) (fun i j => by fin_cases i <;> exact hXX _ j) y J hJ,
      hσ (![fun j => psIn d m (![0, 1] : Fin 2 → Fin 3) (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) y J hJ, hσ (![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) y J hJ, hσ (![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) y J hJ] at E1
    exact alg1 _ _ _ _ _ _ _ (E0.symm.trans E1)
  · refine hunit2 (Units.map ((jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 2 × Fin d) m) : Jet S (Fin 2 × Fin d) m →* Jet S (Fin 2 × Fin d) m) U) U fun y => ?_
    choose J hJ using fun χ : (jOG x0 d m 2).left ⟶ t.G.left => exists_chart hL (χ y)
    obtain ⟨s, hs, hcs⟩ := hfr.sy m
    obtain ⟨s', hs', hcs'⟩ := hfr.sy (m + 1)
    have E0 := (val_corr hJ hcs (𝟙 _)).trans (val_scale t _ _ _ _ _ y J hJ)
    have E1 := (val_corr hJ hcs' (ρn x0 d 2 m).left).trans (val_scale t _ _ _ _ _ y J hJ)
    have hinv : ∀ {k n : ℕ} (w : (Jet S (Fin n × Fin d) k)ˣ), unitΓ w⁻¹ = (unitΓ w)⁻¹ := fun w => map_inv _ w
    have hsi : gm (ρn x0 d 2 m).left y ⊤ (unitΓ s'⁻¹) = gm (𝟙 _) y ⊤ (unitΓ s⁻¹) := by
      rw [hinv, hinv, map_inv, map_inv, htr s' s sy hs' hs y]
    have hL0 : val (e (m + 1)) (ρn x0 d 2 m).left y J = gm (𝟙 _) y ⊤ (unitΓ U) * val (e m) (𝟙 _) y J :=
      (congrArg (fun r => val (e (m + 1)) r y J) (Category.id_comp _).symm).trans (hU _ (𝟙 _) y J hJ)
    rw [hL0, hsi, pe_tr e m (![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) (![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) (fun i j => by fin_cases i <;> exact hXX _ j) y J hJ, hσ (![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) y J hJ] at E1
    exact (alg2 _ _ _ _ _ E0 E1).symm
  · refine hunit2 (Units.map ((jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => psIn d m ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 2 × Fin d) m) : Jet S (Fin 2 × Fin d) m →* Jet S (Fin 2 × Fin d) m) U) (Units.map ((jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 2 × Fin d) m) : Jet S (Fin 2 × Fin d) m →* Jet S (Fin 2 × Fin d) m) U) fun y => ?_
    choose J hJ using fun χ : (jOG x0 d m 2).left ⟶ t.G.left => exists_chart hL (χ y)
    obtain ⟨wL, -, hwL⟩ := hfr.ad a
    obtain ⟨ua, hua, hca⟩ := hwL m
    obtain ⟨ua', hua', hca'⟩ := hwL (m + 1)
    have E0 := (val_corr hJ hca (𝟙 _)).trans (val_scale t _ _ _ _ _ y J hJ)
    have E1 := (val_corr hJ hca' (ρn x0 d 2 m).left).trans (val_scale t _ _ _ _ _ y J hJ)
    rw [val_mul hJ] at E0 E1
    have hw : val (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x (m + 1) (0 : Fin 2))
        (jptG t x0 d x (m + 1) (1 : Fin 2))).left) (ρn x0 d 2 m).left y J =
        val (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left) (𝟙 _) y J :=
      (val_pull hJ _ _ _).trans ((congrArg (fun r => val wL r y J) ((pair_lift_truncation hch m).trans (Category.id_comp _).symm)).trans
        (val_pull hJ _ _ _).symm)
    rw [hw, htr ua' ua (ad a) hua' hua y,
      pe_tr e m (![fun j => psIn d (m + 1) ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) (![fun j => psIn d m ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) (fun i j => by fin_cases i; exacts [psIn_succ_sub m _ _, hXX _ j]) y J hJ,
      pe_tr e m (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d (m + 1) ![1] (act (H.bar a) j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) (fun i j => by fin_cases i; exacts [hXX _ j, psIn_succ_sub m _ _]) y J hJ,
      hσ (![fun j => psIn d m ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) y J hJ, hσ (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) y J hJ] at E1
    exact alg3 _ _ _ _ _ _ E0 E1
end Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio
