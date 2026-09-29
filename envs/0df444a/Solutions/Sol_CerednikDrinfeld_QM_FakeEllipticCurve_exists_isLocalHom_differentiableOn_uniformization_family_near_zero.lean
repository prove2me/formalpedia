-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_isLocalHom_differentiableOn_uniformization_family_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/67dd500e-576f-5243-ae60-84d8b1fdd88e

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relChart_one_differentiableOn_mul_of_analyticChart
import Theorems.Thm_Algebra_ker_smul_top_sup_span_kaehlerDifferentialD_eq_top_of_bijOn_of_differentiableOn
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_smoothOfRelativeDimension_of_forall_topologicalKrullDim_eq
import Theorems.Thm_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc
import Theorems.Thm_LocalGroupLaw_exists_ball_eq_localExp_comp_fderiv_of_map_add
import Theorems.Thm_Matrix_exists_differentiableOn_det_ne_zero_forall_intertwiner_eq_smul
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_span_range_map_algebraMap_eq_top_of_isMaximalOrder
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_hasFDerivAt_appLE_comp_of_hasFDerivAt_appLE
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isLocalHom_differentiableOn_uniformization_family_near_zero
p2m_attr_erase "instance" "PresheafOfModules.ExteriorPower.instModulePresheafAb TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise

namespace RelExpLocalAux

universe u

theorem mul_val_congr {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s')
    (P Q : SchemeHomOver s f) :
    (L.mul s P Q).1 = (L.mul s' ⟨P.1, h ▸ P.2⟩ ⟨Q.1, h ▸ Q.2⟩).1 := by
  subst h; rfl

theorem one_val_congr {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') :
    (L.one s).1 = (L.one s').1 := by
  subst h; rfl

theorem eq_one_of_mul_self {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (u : SchemeHomOver s f)
    (h : L.mul s u u = u) : u = L.one s := by
  have h1 : L.mul s (L.inv s u) (L.mul s u u) = L.mul s (L.inv s u) u := by rw [h]
  rw [← L.mul_assoc, L.inv_mul_cancel, L.one_mul] at h1
  exact h1

theorem eqOn_ball_of_map_add {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (op : X → X → X) (Lf Rf : E → X) {r s : ℝ} (hs : 0 < s)
    (hL : ∀ a b : E, Lf (a + b) = op (Lf a) (Lf b))
    (hR : ∀ a b : E, a ∈ Metric.ball (0 : E) r → b ∈ Metric.ball (0 : E) r → a + b ∈ Metric.ball (0 : E) r →
      Rf (a + b) = op (Rf a) (Rf b))
    (hagree : ∀ a ∈ Metric.ball (0 : E) s, Lf a = Rf a) :
    ∀ w ∈ Metric.ball (0 : E) r, Lf w = Rf w := by
  intro w hw
  rw [Metric.mem_ball, dist_zero_right] at hw

  obtain ⟨n, hn⟩ := exists_nat_gt (‖w‖ / s)
  have hnpos : 0 < (n : ℝ) := lt_of_le_of_lt (div_nonneg (norm_nonneg _) hs.le) hn
  have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
  set u : E := (n : ℝ)⁻¹ • w with hu
  have hnorm_u : ‖u‖ = ‖w‖ / n := by
    rw [hu, norm_smul, norm_inv, Real.norm_natCast, div_eq_inv_mul]
  have hus : u ∈ Metric.ball (0 : E) s := by
    rw [Metric.mem_ball, dist_zero_right, hnorm_u, div_lt_iff₀ hnpos]
    have h1 : ‖w‖ = ‖w‖ / s * s := by field_simp
    have h2 : ‖w‖ / s * s < n * s := mul_lt_mul_of_pos_right hn hs
    linarith

  have hk : ∀ k : ℕ, k ≤ n → (k : ℝ) • u ∈ Metric.ball (0 : E) r := by
    intro k hkn
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_natCast, hnorm_u]
    calc (k : ℝ) * (‖w‖ / n) ≤ n * (‖w‖ / n) := by
          exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkn) (div_nonneg (norm_nonneg _) hnpos.le)
      _ = ‖w‖ := by field_simp
      _ < r := hw

  have key : ∀ k : ℕ, k ≤ n → Lf ((k : ℝ) • u) = Rf ((k : ℝ) • u) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [Nat.cast_zero, zero_smul]
      exact hagree 0 (Metric.mem_ball_self hs)
    | succ k ih =>
      intro hk1
      have hkle : k ≤ n := Nat.le_of_succ_le hk1
      have hsplit : ((k + 1 : ℕ) : ℝ) • u = (k : ℝ) • u + u := by
        rw [Nat.cast_succ, add_smul, one_smul]
      rw [hsplit, hL, ih hkle, hagree u hus]
      have h1u : u ∈ Metric.ball (0 : E) r := by simpa using hk 1 (Nat.one_le_iff_ne_zero.mpr (by
        rintro rfl; simp at hnpos))
      rw [hR _ _ (hk k hkle) h1u (by rw [← hsplit]; exact hk (k+1) hk1)]
  have hw' : w = (n : ℝ) • u := by rw [hu, smul_smul, mul_inv_cancel₀ hn0, one_smul]
  rw [hw']
  exact key n le_rfl

theorem clm_eq_of_eqOn_ball {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] (A B : E →L[ℂ] F) {s : ℝ} (hs : 0 < s)
    (h : ∀ v ∈ Metric.ball (0 : E) s, A v = B v) : A = B := by
  ext v
  by_cases hv : v = 0
  · subst hv; simp
  ·
    set c : ℂ := (((s / 2) / ‖v‖ : ℝ) : ℂ) with hc
    have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hc0 : c ≠ 0 := by
      rw [hc, Complex.ofReal_ne_zero]; exact (div_pos (half_pos hs) hvn).ne'
    have hmem : c • v ∈ Metric.ball (0 : E) s := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul, hc, Complex.norm_real, Real.norm_of_nonneg
        (div_nonneg (half_pos hs).le hvn.le), div_mul_cancel₀ _ hvn.ne']
      linarith
    have := h _ hmem
    rw [map_smul, map_smul] at this
    exact smul_right_injective F hc0 this

theorem eval_comp {X Y : Scheme.{0}} (P : Spec (CommRingCat.of ℂ) ⟶ X) (φ : X ⟶ Y) (V : Y.Opens) (q : Γ(Y, V))
    (h : ⊤ ≤ P ⁻¹ᵁ (φ ⁻¹ᵁ V)) (h' : ⊤ ≤ (P ≫ φ) ⁻¹ᵁ V) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((P ≫ φ).appLE V ⊤ h') q) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.appLE (φ ⁻¹ᵁ V) ⊤ h) (φ.app V q)) := by
  rw [Scheme.Hom.comp_appLE]
  rfl

section
open Filter

theorem appLE_eq_of_eq' {X Y : Scheme.{0}} {a b : X ⟶ Y} (h : a = b) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ a ⁻¹ᵁ U) : a.appLE U V e = b.appLE U V (h ▸ e) := by
  subst h; rfl

theorem exists_localCoord_of_pointFamily
    {R : Type} [CommRing R] {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (s : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of R))

    (φ : (Fin 2 → ℂ) → (Spec (CommRingCat.of ℂ) ⟶ G)) (hφs : ∀ v : Fin 2 → ℂ, φ v ≫ f = s)
    (hφan : ∀ (W : G.Opens) (q : Γ(G, W)), IsOpen {v : Fin 2 → ℂ | ⊤ ≤ (φ v) ⁻¹ᵁ W} ∧
      ∃ Fq : (Fin 2 → ℂ) → ℂ, DifferentiableOn ℂ Fq {v : Fin 2 → ℂ | ⊤ ≤ (φ v) ⁻¹ᵁ W} ∧
        ∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ (φ v) ⁻¹ᵁ W), Fq v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((φ v).appLE W ⊤ h) q))
    (hφmul : ∀ v w : Fin 2 → ℂ, (L.mul s ⟨φ v, hφs v⟩ ⟨φ w, hφs w⟩).1 = φ (v + w))
    (hφone : φ 0 = (L.one s).1)
    (hφinj : ∃ τ : ℝ, 0 < τ ∧ ∀ v ∈ Metric.ball (0 : Fin 2 → ℂ) τ, ∀ v' ∈ Metric.ball (0 : Fin 2 → ℂ) τ, φ v = φ v' → v = v')

    (U : G.Opens) (crd : Fin 2 → Γ(G, U)) (v₁ : Fin 2 → ℂ) (ρ' : ℝ) (ψ : (Fin 2 → ℂ) → SchemeHomOver s f)
    (hU : ∀ v ∈ Metric.ball v₁ ρ', ⊤ ≤ (ψ v).1 ⁻¹ᵁ U)
    (hcoord : ∀ (v : Fin 2 → ℂ) (hv : v ∈ Metric.ball v₁ ρ') (i : Fin 2), (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((ψ v).1).appLE U ⊤ (hU v hv)) (crd i)) = v i)
    (c₀ : Fin 2 → ℂ) (hc₀ : c₀ ∈ Metric.ball v₁ ρ') (hψc₀ : ψ c₀ = L.one s)
    (fs : Finset ↑(Γ(G, U))) (η : ℝ) (hη : 0 < η)
    (hsurj : ∀ (P : SchemeHomOver s f) (hP : ⊤ ≤ P.1 ⁻¹ᵁ U),
      (∀ q ∈ fs, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((P.1).appLE U ⊤ hP) q) - (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((ψ c₀).1).appLE U ⊤ (hU c₀ hc₀)) q)‖ < η) →
      ∃ v ∈ Metric.ball v₁ ρ', ψ v = P)

    (ρ₂ : ℝ) (hρ₂ : 0 < ρ₂) (hρ₂' : ρ₂ ≤ ρ') (Mz : (Fin 2 → ℂ) → (Fin 2 → ℂ) → (Fin 2 → ℂ))
    (hMz : ∀ v ∈ Metric.ball v₁ ρ₂, ∀ w ∈ Metric.ball v₁ ρ₂,
      Mz v w ∈ Metric.ball v₁ ρ' ∧ ψ (Mz v w) = L.mul s (ψ v) (ψ w))

    (ρ₄ : ℝ) (hρ₄ : 0 < ρ₄) (hρ₄₂ : ρ₄ ≤ ρ₂) (hc₀₄ : c₀ ∈ Metric.ball v₁ ρ₄) :
    ∃ (τ : ℝ) (h : (Fin 2 → ℂ) → (Fin 2 → ℂ)), 0 < τ ∧ h 0 = 0 ∧
      DifferentiableOn ℂ h (Metric.ball (0 : Fin 2 → ℂ) τ) ∧
      Set.InjOn h (Metric.ball (0 : Fin 2 → ℂ) τ) ∧
      (∀ v ∈ Metric.ball (0 : Fin 2 → ℂ) τ, h v + c₀ ∈ Metric.ball v₁ ρ₄ ∧ φ v = (ψ (h v + c₀)).1) ∧
      (∀ v w : Fin 2 → ℂ, v ∈ Metric.ball (0 : Fin 2 → ℂ) τ → w ∈ Metric.ball (0 : Fin 2 → ℂ) τ →
        v + w ∈ Metric.ball (0 : Fin 2 → ℂ) τ → h (v + w) + c₀ = Mz (h v + c₀) (h w + c₀)) := by
  classical

  have hopenU : IsOpen {v : Fin 2 → ℂ | ⊤ ≤ (φ v) ⁻¹ᵁ U} := (hφan U (crd 0)).1
  set A : Set (Fin 2 → ℂ) := {v : Fin 2 → ℂ | ⊤ ≤ (φ v) ⁻¹ᵁ U} with hA
  have hAval := fun q : Γ(G, U) => (hφan U q).2
  choose Fq hFq_d hFq_v using hAval

  have hφ0 : φ 0 = (ψ c₀).1 := by rw [hφone, hψc₀]
  have h0A : (0 : Fin 2 → ℂ) ∈ A := by
    show ⊤ ≤ (φ 0) ⁻¹ᵁ U; rw [hφ0]; exact hU c₀ hc₀

  have hF0 : ∀ i : Fin 2, Fq (crd i) 0 = c₀ i := by
    intro i
    rw [hFq_v (crd i) 0 h0A, ← hcoord c₀ hc₀ i, appLE_eq_of_eq' hφ0 U ⊤ _]

  let hcrd : (Fin 2 → ℂ) → (Fin 2 → ℂ) := fun v => ![Fq (crd 0) v, Fq (crd 1) v]
  let h : (Fin 2 → ℂ) → (Fin 2 → ℂ) := fun v => hcrd v - c₀
  have hhcrd_d : DifferentiableOn ℂ hcrd A := by
    rw [differentiableOn_pi]; intro i; fin_cases i
    · exact (hFq_d (crd 0)).congr (fun x _ => by simp [hcrd])
    · exact (hFq_d (crd 1)).congr (fun x _ => by simp [hcrd])
  have hh_d : DifferentiableOn ℂ h A := hhcrd_d.sub_const c₀
  have hhcrd0 : hcrd 0 = c₀ := by
    funext i; fin_cases i
    · simpa [hcrd] using hF0 0
    · simpa [hcrd] using hF0 1
  have hh0 : h 0 = 0 := by show hcrd 0 - c₀ = 0; rw [hhcrd0, sub_self]

  let T : Set (Fin 2 → ℂ) := (A ∩ hcrd ⁻¹' Metric.ball v₁ ρ₄) ∩ ⋂ q ∈ fs, (A ∩ (Fq q) ⁻¹' Metric.ball (Fq q 0) η)
  have hT_open : IsOpen T := by
    refine (hhcrd_d.continuousOn.isOpen_inter_preimage hopenU Metric.isOpen_ball).inter ?_
    exact isOpen_biInter_finset fun q _ => (hFq_d q).continuousOn.isOpen_inter_preimage hopenU Metric.isOpen_ball
  have h0T : (0 : Fin 2 → ℂ) ∈ T := by
    refine ⟨⟨h0A, ?_⟩, ?_⟩
    · show hcrd 0 ∈ Metric.ball v₁ ρ₄; rw [hhcrd0]; exact hc₀₄
    · simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage]
      intro q _; exact ⟨h0A, Metric.mem_ball_self hη⟩
  obtain ⟨τ₀, hτ₀, hτ₀T⟩ := Metric.isOpen_iff.1 hT_open 0 h0T
  obtain ⟨τ₁, hτ₁, hinj⟩ := hφinj
  set τ := min τ₀ τ₁ with hτdef
  have hτ : 0 < τ := lt_min hτ₀ hτ₁
  have hτT : ∀ v ∈ Metric.ball (0 : Fin 2 → ℂ) τ, v ∈ T := fun v hv =>
    hτ₀T (Metric.ball_subset_ball (min_le_left _ _) hv)
  have hτinj : ∀ v ∈ Metric.ball (0 : Fin 2 → ℂ) τ, v ∈ Metric.ball (0 : Fin 2 → ℂ) τ₁ := fun v hv =>
    Metric.ball_subset_ball (min_le_right _ _) hv

  have hchart : ∀ v ∈ T, hcrd v ∈ Metric.ball v₁ ρ₄ ∧ ψ (hcrd v) = ⟨φ v, hφs v⟩ := by
    intro v hv
    obtain ⟨⟨hvA, hv4⟩, hclose⟩ := hv
    have hv4' : hcrd v ∈ Metric.ball v₁ ρ₄ := hv4
    refine ⟨hv4', ?_⟩
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage] at hclose
    obtain ⟨v', hv', hψv'⟩ := hsurj ⟨φ v, hφs v⟩ hvA (fun q hq => by
      have hc := (hclose q hq).2
      rw [Metric.mem_ball, dist_eq_norm, hFq_v q v hvA, hFq_v q 0 h0A] at hc
      have e0 : (φ 0).appLE U ⊤ h0A = (ψ c₀).1.appLE U ⊤ (hU c₀ hc₀) := appLE_eq_of_eq' hφ0 U ⊤ _
      rw [e0] at hc
      exact hc)
    have hvv : v' = hcrd v := by
      have hψ1 : (ψ v').1 = φ v := congrArg Subtype.val hψv'
      funext i
      rw [← hcoord v' hv' i, appLE_eq_of_eq' hψ1 U ⊤ _, ← hFq_v (crd i) v hvA]
      fin_cases i <;> simp [hcrd]
    rw [← hvv]; exact hψv'

  have hψinj : ∀ a ∈ Metric.ball v₁ ρ', ∀ b ∈ Metric.ball v₁ ρ', ψ a = ψ b → a = b := by
    intro a ha b hb hab
    funext i
    rw [← hcoord a ha i, ← hcoord b hb i, appLE_eq_of_eq' (congrArg Subtype.val hab) U ⊤ _]
  have hρ₄' : Metric.ball v₁ ρ₄ ⊆ Metric.ball v₁ ρ' := Metric.ball_subset_ball (hρ₄₂.trans hρ₂')
  have hρ₄₂' : Metric.ball v₁ ρ₄ ⊆ Metric.ball v₁ ρ₂ := Metric.ball_subset_ball hρ₄₂
  refine ⟨τ, h, hτ, hh0, hh_d.mono (fun v hv => (hτT v hv).1.1), ?_, ?_, ?_⟩
  ·
    intro v hv v' hv' hvv'
    have h1 : hcrd v = hcrd v' := by
      have : hcrd v - c₀ = hcrd v' - c₀ := hvv'
      exact sub_left_injective this
    have h2 : φ v = φ v' := by
      have a := congrArg Subtype.val (hchart v (hτT v hv)).2
      have b := congrArg Subtype.val (hchart v' (hτT v' hv')).2
      simp only at a b
      rw [← a, ← b, h1]
    exact hinj v (hτinj v hv) v' (hτinj v' hv') h2
  ·
    intro v hv
    obtain ⟨h4, hψ⟩ := hchart v (hτT v hv)
    have e1 : h v + c₀ = hcrd v := by show hcrd v - c₀ + c₀ = hcrd v; rw [sub_add_cancel]
    rw [e1]
    exact ⟨h4, (congrArg Subtype.val hψ).symm⟩
  ·
    intro v w hv hw hvw
    obtain ⟨hv4, hψv⟩ := hchart v (hτT v hv)
    obtain ⟨hw4, hψw⟩ := hchart w (hτT w hw)
    obtain ⟨hvw4, hψvw⟩ := hchart (v + w) (hτT (v + w) hvw)
    have e1 : ∀ u : Fin 2 → ℂ, h u + c₀ = hcrd u := fun u => by
      show hcrd u - c₀ + c₀ = hcrd u; rw [sub_add_cancel]
    rw [e1, e1, e1]
    obtain ⟨hM1, hM2⟩ := hMz (hcrd v) (hρ₄₂' hv4) (hcrd w) (hρ₄₂' hw4)
    apply hψinj _ (hρ₄' hvw4) _ hM1
    rw [hM2, hψv, hψw, hψvw]
    apply Subtype.ext
    exact (hφmul v w).symm

end

open Filter Set in

theorem differentiableOn_matrix_of_localConj
    {n : ℕ} (z₀ : ℂ) {ε r δ : ℝ} (hε : 0 < ε) (hr : 0 < r) (hδ : 0 < δ)
    (e ℓ : ℂ → (Fin n → ℂ) → (Fin n → ℂ))
    (he : DifferentiableOn ℂ (fun q : ℂ × (Fin n → ℂ) => e q.1 q.2) (Metric.ball z₀ ε ×ˢ Metric.ball (0 : Fin n → ℂ) r))
    (hℓ : DifferentiableOn ℂ (fun q : ℂ × (Fin n → ℂ) => ℓ q.1 q.2) (Metric.ball z₀ ε ×ˢ Metric.ball (0 : Fin n → ℂ) δ))
    (he0 : ∀ z ∈ Metric.ball z₀ ε, e z 0 = 0)
    (hℓe : ∀ z ∈ Metric.ball z₀ ε, ∀ v ∈ Metric.ball (0 : Fin n → ℂ) r, ℓ z (e z v) = v)
    (R : ℂ → (Fin n → ℂ) → (Fin n → ℂ)) (O : Set (ℂ × (Fin n → ℂ))) (hO : IsOpen O)
    (hO0 : ∀ z ∈ Metric.ball z₀ ε, (z, (0 : Fin n → ℂ)) ∈ O)
    (hR : DifferentiableOn ℂ (fun q : ℂ × (Fin n → ℂ) => R q.1 q.2) O)
    (hR0 : ∀ z ∈ Metric.ball z₀ ε, R z 0 = 0)
    (B : ℂ → Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ z ∈ Metric.ball z₀ ε, ∃ τ : ℝ, 0 < τ ∧
      ∀ u ∈ Metric.ball (0 : Fin n → ℂ) τ, e z ((B z).mulVec u) = R z (e z u)) :
    ∀ i j : Fin n, DifferentiableOn ℂ (fun z : ℂ => B z i j) (Metric.ball z₀ ε) := by
  classical

  suffices H : ∀ z₁ ∈ Metric.ball z₀ ε, ∀ i j : Fin n, DifferentiableAt ℂ (fun z : ℂ => B z i j) z₁ by
    intro i j z hz; exact (H z hz i j).differentiableWithinAt
  intro z₁ hz₁ i j

  let E₁ : Set (ℂ × (Fin n → ℂ)) := Metric.ball z₀ ε ×ˢ Metric.ball (0 : Fin n → ℂ) r
  have hE₁ : IsOpen E₁ := Metric.isOpen_ball.prod Metric.isOpen_ball
  let em : ℂ × (Fin n → ℂ) → ℂ × (Fin n → ℂ) := fun q => (q.1, e q.1 q.2)
  let Rm : ℂ × (Fin n → ℂ) → ℂ × (Fin n → ℂ) := fun q => (q.1, R q.1 q.2)
  have hem : DifferentiableOn ℂ em E₁ := differentiableOn_fst.prodMk he
  have hRm : DifferentiableOn ℂ Rm O := differentiableOn_fst.prodMk hR
  let W : Set (ℂ × (Fin n → ℂ)) := E₁ ∩ em ⁻¹' (O ∩ Rm ⁻¹' (Metric.ball z₀ ε ×ˢ Metric.ball (0 : Fin n → ℂ) δ))
  have hW : IsOpen W := by
    refine hem.continuousOn.isOpen_inter_preimage hE₁ ?_
    exact hRm.continuousOn.isOpen_inter_preimage hO (Metric.isOpen_ball.prod Metric.isOpen_ball)
  have hz₁W : ((z₁, (0 : Fin n → ℂ)) : ℂ × (Fin n → ℂ)) ∈ W := by
    refine ⟨⟨hz₁, Metric.mem_ball_self hr⟩, ?_⟩
    show em (z₁, 0) ∈ O ∩ Rm ⁻¹' (Metric.ball z₀ ε ×ˢ Metric.ball (0 : Fin n → ℂ) δ)
    have h1 : em (z₁, 0) = (z₁, 0) := by simp [em, he0 z₁ hz₁]
    rw [h1]
    refine ⟨hO0 z₁ hz₁, ?_⟩
    show Rm (z₁, 0) ∈ Metric.ball z₀ ε ×ˢ Metric.ball (0 : Fin n → ℂ) δ
    have h2 : Rm (z₁, 0) = (z₁, 0) := by simp [Rm, hR0 z₁ hz₁]
    rw [h2]; exact ⟨hz₁, Metric.mem_ball_self hδ⟩
  let K : ℂ × (Fin n → ℂ) → (Fin n → ℂ) := fun q => ℓ q.1 (R q.1 (e q.1 q.2))
  have hK : DifferentiableOn ℂ K W := by
    have h1 : DifferentiableOn ℂ (Rm ∘ em) W :=
      hRm.comp (hem.mono Set.inter_subset_left) (fun q hq => hq.2.1)
    have h2 : DifferentiableOn ℂ ((fun q : ℂ × (Fin n → ℂ) => ℓ q.1 q.2) ∘ (Rm ∘ em)) W :=
      hℓ.comp h1 (fun q hq => hq.2.2)
    exact h2
  obtain ⟨γ, hγ, hγW⟩ := Metric.isOpen_iff.1 hW _ hz₁W

  have hball_prod : ∀ (z : ℂ) (u : Fin n → ℂ), z ∈ Metric.ball z₁ γ → u ∈ Metric.ball (0 : Fin n → ℂ) γ →
      ((z, u) : ℂ × (Fin n → ℂ)) ∈ W := by
    intro z u hz hu
    apply hγW
    rw [← ball_prod_same]; exact ⟨hz, hu⟩

  have hlin : ∀ z ∈ Metric.ball z₁ γ, ∃ τ' : ℝ, 0 < τ' ∧ ∀ u ∈ Metric.ball (0 : Fin n → ℂ) τ',
      K (z, u) = (B z).mulVec u := by
    intro z hz
    have hzε : z ∈ Metric.ball z₀ ε := (hball_prod z 0 hz (Metric.mem_ball_self hγ)).1.1
    obtain ⟨τ, hτ, hτB⟩ := hB z hzε

    have hcont : ContinuousAt (fun u : Fin n → ℂ => (B z).mulVec u) 0 :=
      ((B z).mulVecLin : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)).continuous_of_finiteDimensional.continuousAt
    have hpre : (fun u : Fin n → ℂ => (B z).mulVec u) ⁻¹' Metric.ball 0 r ∈ 𝓝 (0 : Fin n → ℂ) := by
      apply hcont.preimage_mem_nhds
      rw [Matrix.mulVec_zero]; exact Metric.ball_mem_nhds _ hr
    obtain ⟨τ₂, hτ₂, hτ₂s⟩ := Metric.mem_nhds_iff.1 hpre
    refine ⟨min τ τ₂, lt_min hτ hτ₂, fun u hu => ?_⟩
    have hu1 : u ∈ Metric.ball (0 : Fin n → ℂ) τ := Metric.ball_subset_ball (min_le_left _ _) hu
    have hu2 : (B z).mulVec u ∈ Metric.ball (0 : Fin n → ℂ) r := hτ₂s (Metric.ball_subset_ball (min_le_right _ _) hu)
    show ℓ z (R z (e z u)) = (B z).mulVec u
    rw [← hτB u hu1, hℓe z hzε _ hu2]

  let uj : Fin n → ℂ := Pi.single j 1
  have huj_norm : ∀ s : ℂ, ‖s • uj‖ = ‖s‖ := by
    intro s; rw [norm_smul, Pi.norm_single, norm_one, mul_one]
  have hslice : ∀ z ∈ Metric.ball z₁ γ, ∀ s ∈ Metric.ball (0 : ℂ) γ,
      K (z, s • uj) i = s * B z i j := by
    intro z hz
    obtain ⟨τ', hτ', hτ'K⟩ := hlin z hz

    have hg : DifferentiableOn ℂ (fun s : ℂ => K (z, s • uj) i) (Metric.ball (0 : ℂ) γ) := by
      have hpath : DifferentiableOn ℂ (fun s : ℂ => ((z, s • uj) : ℂ × (Fin n → ℂ))) (Metric.ball (0 : ℂ) γ) := by
        fun_prop
      have := hK.comp hpath (fun s hs => hball_prod z _ hz (by
        rw [mem_ball_zero_iff, huj_norm]; exact mem_ball_zero_iff.1 hs))
      exact (differentiableOn_pi.1 this) i
    have hl : DifferentiableOn ℂ (fun s : ℂ => s * B z i j) (Metric.ball (0 : ℂ) γ) := by fun_prop
    have heq : (fun s : ℂ => K (z, s • uj) i) =ᶠ[𝓝 (0 : ℂ)] (fun s : ℂ => s * B z i j) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hτ'] with s hs
      have hs' : s • uj ∈ Metric.ball (0 : Fin n → ℂ) τ' := by
        rw [mem_ball_zero_iff, huj_norm]; exact mem_ball_zero_iff.1 hs
      rw [hτ'K _ hs', Matrix.mulVec_smul, Pi.smul_apply, Matrix.mulVec_single_one, smul_eq_mul]
      rfl
    exact (hg.analyticOnNhd Metric.isOpen_ball).eqOn_of_preconnected_of_eventuallyEq
      (hl.analyticOnNhd Metric.isOpen_ball) (convex_ball (0 : ℂ) γ).isPreconnected
      (Metric.mem_ball_self hγ) heq

  set s₀ : ℂ := ((γ / 2 : ℝ) : ℂ) with hs₀
  have hs₀mem : s₀ ∈ Metric.ball (0 : ℂ) γ := by
    rw [mem_ball_zero_iff, hs₀, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hs₀ne : s₀ ≠ 0 := by
    rw [hs₀]; exact_mod_cast (by positivity : (γ / 2 : ℝ) ≠ 0)
  have hformula : ∀ z ∈ Metric.ball z₁ γ, B z i j = K (z, s₀ • uj) i / s₀ := by
    intro z hz
    rw [hslice z hz s₀ hs₀mem, mul_div_cancel_left₀ _ hs₀ne]

  have hKz : DifferentiableAt ℂ (fun z : ℂ => K (z, s₀ • uj) i) z₁ := by
    have hpath : DifferentiableOn ℂ (fun z : ℂ => ((z, s₀ • uj) : ℂ × (Fin n → ℂ))) (Metric.ball z₁ γ) := by
      fun_prop
    have hmem : s₀ • uj ∈ Metric.ball (0 : Fin n → ℂ) γ := by
      rw [mem_ball_zero_iff, huj_norm]; exact mem_ball_zero_iff.1 hs₀mem
    have := hK.comp hpath (fun z hz => hball_prod z _ hz hmem)
    exact ((differentiableOn_pi.1 this) i).differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hγ))
  have heqz : (fun z : ℂ => B z i j) =ᶠ[𝓝 z₁] (fun z : ℂ => K (z, s₀ • uj) i / s₀) := by
    filter_upwards [Metric.ball_mem_nhds z₁ hγ] with z hz
    exact hformula z hz
  exact (heqz.differentiableAt_iff).2 (hKz.div_const s₀)

theorem exists_ball_mulVec_mem_ball
    (z₀ : ℂ) {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (Nm : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (hN : ∀ i j : Fin 2, DifferentiableOn ℂ (fun z : ℂ => Nm z i j) (Metric.ball z₀ ε)) :
    ∃ ε' r' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧ 0 < r' ∧
      ∀ z ∈ Metric.ball z₀ ε', ∀ w ∈ Metric.ball (0 : Fin 2 → ℂ) r', (Nm z).mulVec w ∈ Metric.ball (0 : Fin 2 → ℂ) ρ := by
  set S : Set (ℂ × (Fin 2 → ℂ)) := Metric.ball z₀ ε ×ˢ (Set.univ : Set (Fin 2 → ℂ)) with hS
  have hSo : IsOpen S := Metric.isOpen_ball.prod isOpen_univ
  have hmem : ((z₀, (0 : Fin 2 → ℂ)) : ℂ × (Fin 2 → ℂ)) ∈ S := ⟨Metric.mem_ball_self hε, Set.mem_univ _⟩
  have hcont : ContinuousOn (fun q : ℂ × (Fin 2 → ℂ) => (Nm q.1).mulVec q.2) S := by
    refine continuousOn_pi.2 fun i => ?_
    have : (fun q : ℂ × (Fin 2 → ℂ) => (Nm q.1).mulVec q.2 i) =
        fun q => ∑ j : Fin 2, Nm q.1 i j * q.2 j := by
      funext q; simp [Matrix.mulVec, dotProduct]
    rw [this]
    refine continuousOn_finsetSum _ fun j _ => ?_
    refine ContinuousOn.mul ?_ ?_
    · exact (hN i j).continuousOn.comp continuousOn_fst (fun q hq => hq.1)
    · exact ((continuous_apply j).comp continuous_snd).continuousOn
  have hcA : ContinuousAt (fun q : ℂ × (Fin 2 → ℂ) => (Nm q.1).mulVec q.2) (z₀, 0) :=
    hcont.continuousAt (hSo.mem_nhds hmem)
  have hpre : (fun q : ℂ × (Fin 2 → ℂ) => (Nm q.1).mulVec q.2) ⁻¹' Metric.ball (0 : Fin 2 → ℂ) ρ ∈ 𝓝 ((z₀, (0 : Fin 2 → ℂ)) : ℂ × (Fin 2 → ℂ)) :=
    hcA.preimage_mem_nhds (by
      show Metric.ball (0 : Fin 2 → ℂ) ρ ∈ 𝓝 ((Nm z₀).mulVec 0)
      rw [Matrix.mulVec_zero]; exact Metric.ball_mem_nhds _ hρ)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨min δ ε, δ, lt_min hδ hε, min_le_right _ _, hδ, fun z hz w hw => ?_⟩
  have hq : ((z, w) : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((z₀, (0 : Fin 2 → ℂ)) : ℂ × (Fin 2 → ℂ)) δ := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    refine ⟨lt_of_lt_of_le hz (min_le_left _ _), ?_⟩
    rw [dist_zero_right]; exact mem_ball_zero_iff.mp hw
  have h' : ((z, w) : ℂ × (Fin 2 → ℂ)) ∈ (fun q : ℂ × (Fin 2 → ℂ) => (Nm q.1).mulVec q.2) ⁻¹' Metric.ball (0 : Fin 2 → ℂ) ρ :=
    hsub hq
  rw [Set.mem_preimage] at h'
  exact h'

theorem differentiableOn_exp_mulVec_add
    (z₀ : ℂ) {ε ε' r r' : ℝ} (hε'ε : ε' ≤ ε)
    (ex : ℂ → (Fin 2 → ℂ) → (Fin 2 → ℂ)) (Nm : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (o : ℂ → (Fin 2 → ℂ))
    (hexD : DifferentiableOn ℂ (fun q : ℂ × (Fin 2 → ℂ) => ex q.1 q.2) (Metric.ball z₀ ε ×ˢ Metric.ball (0 : Fin 2 → ℂ) r))
    (hN : ∀ i j : Fin 2, DifferentiableOn ℂ (fun z : ℂ => Nm z i j) (Metric.ball z₀ ε'))
    (ho : DifferentiableOn ℂ o (Metric.ball z₀ ε'))
    (hNr : ∀ z ∈ Metric.ball z₀ ε', ∀ w ∈ Metric.ball (0 : Fin 2 → ℂ) r', (Nm z).mulVec w ∈ Metric.ball (0 : Fin 2 → ℂ) r) :
    DifferentiableOn ℂ (fun p : ℂ × (Fin 2 → ℂ) => ex p.1 ((Nm p.1).mulVec p.2) + o p.1)
      (Metric.ball z₀ ε' ×ˢ Metric.ball (0 : Fin 2 → ℂ) r') := by
  set T : Set (ℂ × (Fin 2 → ℂ)) := Metric.ball z₀ ε' ×ˢ Metric.ball (0 : Fin 2 → ℂ) r' with hT

  have hmv : DifferentiableOn ℂ (fun p : ℂ × (Fin 2 → ℂ) => (Nm p.1).mulVec p.2) T := by
    refine differentiableOn_pi.2 fun i => ?_
    have : (fun p : ℂ × (Fin 2 → ℂ) => (Nm p.1).mulVec p.2 i) =
        fun p => ∑ j : Fin 2, Nm p.1 i j * p.2 j := by
      funext p; simp [Matrix.mulVec, dotProduct]
    rw [this]
    refine DifferentiableOn.fun_sum fun j _ => ?_
    refine DifferentiableOn.mul ?_ ?_
    · exact (hN i j).comp differentiableOn_fst (fun p hp => hp.1)
    · exact (differentiable_pi.mp (differentiable_snd (𝕜 := ℂ) (E := ℂ) (F := Fin 2 → ℂ)) j).differentiableOn
  have hinner : DifferentiableOn ℂ (fun p : ℂ × (Fin 2 → ℂ) => ((p.1, (Nm p.1).mulVec p.2) : ℂ × (Fin 2 → ℂ))) T :=
    differentiableOn_fst.prodMk hmv
  have hmaps : Set.MapsTo (fun p : ℂ × (Fin 2 → ℂ) => ((p.1, (Nm p.1).mulVec p.2) : ℂ × (Fin 2 → ℂ))) T
      (Metric.ball z₀ ε ×ˢ Metric.ball (0 : Fin 2 → ℂ) r) :=
    fun p hp => ⟨Metric.ball_subset_ball hε'ε hp.1, hNr p.1 hp.1 p.2 hp.2⟩
  have h1 : DifferentiableOn ℂ (fun p : ℂ × (Fin 2 → ℂ) => ex p.1 ((Nm p.1).mulVec p.2)) T :=
    hexD.comp hinner hmaps
  have h2 : DifferentiableOn ℂ (fun p : ℂ × (Fin 2 → ℂ) => o p.1) T :=
    ho.comp differentiableOn_fst (fun p hp => hp.1)
  exact h1.add h2

theorem le_of_ball_subset_ball {z₀ : ℂ} {ε r : ℝ} (hε : 0 < ε) (h : Metric.ball z₀ ε ⊆ Metric.ball z₀ r) : ε ≤ r := by
  by_contra hlt
  push_neg at hlt

  have hr0 : 0 ≤ r ∨ r < 0 := le_or_gt 0 r
  set s : ℝ := max ((r + ε) / 2) (ε / 2) with hs
  have hsε : s < ε := by
    rw [hs, max_lt_iff]; constructor <;> linarith
  have hsr : r ≤ s := by
    rw [hs]; rcases hr0 with h0 | h0
    · exact le_max_of_le_left (by linarith)
    · exact le_max_of_le_right (by linarith)
  have hs0 : 0 ≤ s := le_max_of_le_right (by linarith)
  have hmem : z₀ + (s : ℂ) ∈ Metric.ball z₀ ε := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hs0]; exact hsε
  have := h hmem
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hs0] at this
  linarith

section
open Filter

theorem appLE_eq_of_eq'' {X Y : Scheme.{0}} {a b : X ⟶ Y} (h : a = b) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ a ⁻¹ᵁ U) : a.appLE U V e = b.appLE U V (h ▸ e) := by
  subst h; rfl

theorem locAn_of_chart_reparam
    (Sc : Type) [CommRing Sc] [Algebra ℂ Sc] (t : Sc) (σ₀ : Sc →ₐ[ℂ] ℂ) (𝒰 : Set (Sc →ₐ[ℂ] ℂ))
    {G : Scheme.{0}} {fG : G ⟶ Spec (CommRingCat.of Sc)}
    (ε₁ ρ' : ℝ) (v₁ : Fin 2 → ℂ)
    (ψ₁ : (σ : Sc →ₐ[ℂ] ℂ) → (Fin 2 → ℂ) → SchemeHomOver (Spec.map (CommRingCat.ofHom σ.toRingHom)) fG)

    (hAN₁ : (∀ (V : G.Opens) (φ : Γ(G, V)),
        IsOpen {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε₁ ∧ p.2 ∈ Metric.ball v₁ ρ' ∧
          ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (ψ₁ σ p.2).1 ⁻¹ᵁ V} ∧
        ∃ F : ℂ × (Fin 2 → ℂ) → ℂ,
          DifferentiableOn ℂ F {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε₁ ∧ p.2 ∈ Metric.ball v₁ ρ' ∧
            ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (ψ₁ σ p.2).1 ⁻¹ᵁ V} ∧
          ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₀ t) ε₁ → ∀ v ∈ Metric.ball v₁ ρ', ∀ (hV : ⊤ ≤ (ψ₁ σ v).1 ⁻¹ᵁ V),
            F (σ t, v) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((ψ₁ σ v).1.appLE V ⊤ hV) φ)))

    (Θ₂ : ℂ → (Fin 2 → ℂ) → (Fin 2 → ℂ)) (ε r' : ℝ) (hε : 0 < ε) (hεε₁ : ε ≤ ε₁) (hr' : 0 < r')
    (hΘ : DifferentiableOn ℂ (fun p : ℂ × (Fin 2 → ℂ) => Θ₂ p.1 p.2)
      (Metric.ball (σ₀ t) ε ×ˢ Metric.ball (0 : Fin 2 → ℂ) r'))
    (hΘmem : ∀ z ∈ Metric.ball (σ₀ t) ε, ∀ w ∈ Metric.ball (0 : Fin 2 → ℂ) r', Θ₂ z w ∈ Metric.ball v₁ ρ')

    (Pf : (Sc →ₐ[ℂ] ℂ) → (Fin 2 → ℂ) → (Spec (CommRingCat.of ℂ) ⟶ G))
    (hkey : ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₀ t) ε → ∀ w ∈ Metric.ball (0 : Fin 2 → ℂ) r',
      Pf σ w = (ψ₁ σ (Θ₂ (σ t) w)).1) :
    (∀ (V : G.Opens) (f : Γ(G, V)),
      IsOpen {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε ∧ p.2 ∈ Metric.ball (0 : Fin 2 → ℂ) r' ∧
        ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (Pf σ p.2) ⁻¹ᵁ V} ∧
      ∃ F : ℂ × (Fin 2 → ℂ) → ℂ,
        DifferentiableOn ℂ F {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε ∧ p.2 ∈ Metric.ball (0 : Fin 2 → ℂ) r' ∧
          ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (Pf σ p.2) ⁻¹ᵁ V} ∧
        ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₀ t) ε → ∀ w ∈ Metric.ball (0 : Fin 2 → ℂ) r', ∀ (hV : ⊤ ≤ (Pf σ w) ⁻¹ᵁ V),
          F (σ t, w) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((Pf σ w)).appLE V ⊤ hV) f)) := by
  classical
  intro V φ
  obtain ⟨hopen₁, F₁, hF₁d, hF₁v⟩ := hAN₁ V φ
  let box : Set (ℂ × (Fin 2 → ℂ)) := Metric.ball (σ₀ t) ε ×ˢ Metric.ball (0 : Fin 2 → ℂ) r'
  have hbox : IsOpen box := Metric.isOpen_ball.prod Metric.isOpen_ball
  let Θ : ℂ × (Fin 2 → ℂ) → ℂ × (Fin 2 → ℂ) := fun p => (p.1, Θ₂ p.1 p.2)
  have hΘd : DifferentiableOn ℂ Θ box := differentiableOn_fst.prodMk hΘ
  set L₁ : Set (ℂ × (Fin 2 → ℂ)) := {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε₁ ∧ p.2 ∈ Metric.ball v₁ ρ' ∧
      ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (ψ₁ σ p.2).1 ⁻¹ᵁ V} with hL₁
  set L : Set (ℂ × (Fin 2 → ℂ)) := {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε ∧ p.2 ∈ Metric.ball (0 : Fin 2 → ℂ) r' ∧
      ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (Pf σ p.2) ⁻¹ᵁ V} with hL

  have hkey' : ∀ (σ : Sc →ₐ[ℂ] ℂ) (hσ : σ ∈ 𝒰) (z : ℂ) (hz : z ∈ Metric.ball (σ₀ t) ε) (hσz : σ t = z)
      (w : Fin 2 → ℂ) (hw : w ∈ Metric.ball (0 : Fin 2 → ℂ) r'), Pf σ w = (ψ₁ σ (Θ₂ z w)).1 := by
    intro σ hσ z hz hσz w hw
    rw [← hσz]; exact hkey σ hσ (hσz ▸ hz) w hw
  have hLeq : L = box ∩ Θ ⁻¹' L₁ := by
    ext p
    constructor
    · rintro ⟨hp1, hp2, σ, hσ, hσt, hV⟩
      refine ⟨⟨hp1, hp2⟩, ?_⟩
      show Θ p ∈ L₁
      refine ⟨Metric.ball_subset_ball hεε₁ hp1, hΘmem _ hp1 _ hp2, σ, hσ, hσt, ?_⟩
      show ⊤ ≤ (ψ₁ σ (Θ₂ p.1 p.2)).1 ⁻¹ᵁ V
      rw [← hkey' σ hσ p.1 hp1 hσt p.2 hp2]; exact hV
    · rintro ⟨⟨hp1, hp2⟩, hp1', hp2', σ, hσ, hσt, hV⟩
      refine ⟨hp1, hp2, σ, hσ, hσt, ?_⟩
      rw [hkey' σ hσ p.1 hp1 hσt p.2 hp2]; exact hV
  have hLopen : IsOpen L := by
    rw [hLeq]; exact hΘd.continuousOn.isOpen_inter_preimage hbox hopen₁
  refine ⟨hLopen, F₁ ∘ Θ, ?_, ?_⟩
  · rw [hLeq]
    exact hF₁d.comp (hΘd.mono Set.inter_subset_left) (fun p hp => hp.2)
  · intro σ hσ hz w hw hV
    have hmem := hΘmem _ hz _ hw
    have hV' : ⊤ ≤ (ψ₁ σ (Θ₂ (σ t) w)).1 ⁻¹ᵁ V := by rw [← hkey σ hσ hz w hw]; exact hV
    show F₁ (σ t, Θ₂ (σ t) w) = _
    rw [hF₁v σ hσ (Metric.ball_subset_ball hεε₁ hz) _ hmem hV',
      appLE_eq_of_eq'' (hkey σ hσ hz w hw).symm V ⊤ _]

end

end RelExpLocalAux

set_option maxHeartbeats 3200000 in
open RelExpLocalAux in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) (hqq' : q' ≠ q)
    {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)

    (latt : FakeEllipticCurve Λ N ℂ → Submodule ℤ (Fin 2 → ℂ))
    (e : ∀ E : FakeEllipticCurve Λ N ℂ,
      SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f ≃ ((Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))

    (hL1 : ∀ E : FakeEllipticCurve Λ N ℂ,
        (∃ b₀ : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), latt E = Submodule.span ℤ (Set.range b₀)) ∧
        (∀ x ∈ Λ, ∀ v ∈ latt E, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ latt E))

    (hE1 : ∀ (E : FakeEllipticCurve Λ N ℂ) (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f),
        e E (E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e E P + e E Q)

    (hE2 : ∀ (E : FakeEllipticCurve Λ N ℂ) (x : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
        e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
        e E (pushPt (E.act x) (E.act_over x) P) =
          ((((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))

    (hH1 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
          mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
        (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) →
        ∃ c : ℂ, (∀ v ∈ latt E, c • v ∈ latt E') ∧
          ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
            e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
            e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup))

    (hH2 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (c : ℂ), (∀ v ∈ latt E, c • v ∈ latt E') →
        ∃ (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
            mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
          (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧
          ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
            e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
            e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup))

    (hH3 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (φ ψ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (hψ : ψ ≫ E'.f = E.f),
        (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f, mapPt φ hφ P = mapPt ψ hψ P) → φ = ψ)

    (hAN : ∀ (E : FakeEllipticCurve Λ N ℂ) (U : E.A.Opens) (f : Γ(E.A, U)),
        IsOpen {v : Fin 2 → ℂ | ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U} ∧
        ∃ F : (Fin 2 → ℂ) → ℂ,
          DifferentiableOn ℂ F {v : Fin 2 → ℂ | ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U} ∧
          ∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U),
            F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
              ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f))

    (hCOV : ∀ (E : FakeEllipticCurve Λ N ℂ) (v₀ : Fin 2 → ℂ),
        ∃ (U : E.A.Opens) (f₁ f₂ : Γ(E.A, U)) (ε : ℝ) (D : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ))
          (F : (Fin 2 → ℂ) → (Fin 2 → ℂ)),
          0 < ε ∧
          (∀ v ∈ Metric.ball v₀ ε, ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U) ∧
          (∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U),
            v ∈ Metric.ball v₀ ε →
            F v = ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
                      ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f₁),
                    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
                      ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f₂)]) ∧
          HasFDerivAt F (D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) v₀)

    (Sc : Type) [CommRing Sc] [IsDomain Sc] [Algebra ℂ Sc] [Algebra.FiniteType ℂ Sc]
    (hSc : Algebra.Smooth ℂ Sc) (hΩ : Module.rank Sc (KaehlerDifferential ℂ Sc) = 1)
    (t : Sc) (σ₀ : Sc →ₐ[ℂ] ℂ) (r : ℝ) (𝒰 : Set (Sc →ₐ[ℂ] ℂ)) (hr : 0 < r) (hσ₀ : σ₀ ∈ 𝒰)
    (hbij : Set.BijOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r))
    (hhol : ∀ s : Sc, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧ ∀ σ ∈ 𝒰, σ s = F (σ t))

    (𝒜 : FakeEllipticCurve Λ N Sc)
    (E : ℂ → FakeEllipticCurve Λ N ℂ) (g : ∀ z : ℂ, (E z).A ⟶ 𝒜.A)
    (hg : ∀ σ ∈ 𝒰,
      ∃ hc : CategoryTheory.IsPullback (g (σ t)) (E (σ t)).f 𝒜.f (Spec.map (CommRingCat.ofHom σ.toRingHom)),

        (∀ (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (E (σ t)).f),
          ((E (σ t)).L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q).1 ≫ g (σ t) =
            (𝒜.L.mul (𝟙 (Spec (CommRingCat.of ℂ)) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))
              ⟨P.1 ≫ g (σ t), by rw [Category.assoc, hc.w, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ g (σ t), by rw [Category.assoc, hc.w, ← Category.assoc, Q.2]⟩).1) ∧

        (∀ x : ↥Λ, (E (σ t)).act x ≫ g (σ t) = g (σ t) ≫ 𝒜.act x)) :
    ∃ (ε : ℝ) (κ : ℂ → ℂ) (r' : ℝ), 0 < ε ∧ ε ≤ r ∧ 0 < r' ∧ (∀ z ∈ Metric.ball (σ₀ t) ε, κ z ≠ 0) ∧

      (∀ σ ∈ 𝒰, ∀ (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (E (σ t)).f),
        P.1 ≫ g (σ t) = Q.1 ≫ g (σ t) → P = Q) ∧

      (∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₀ t) ε → ∀ w : Fin 2 → ℂ,
        (((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) = (𝒜.L.one (Spec.map (CommRingCat.ofHom σ.toRingHom))).1 ↔
          κ (σ t) • w ∈ latt (E (σ t))) ∧

      (∀ σ ∈ 𝒰, ∀ w : Fin 2 → ℂ, (((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) ≫ 𝒜.f = Spec.map (CommRingCat.ofHom σ.toRingHom)) ∧

      (∀ σ ∈ 𝒰, ∀ (w w' : Fin 2 → ℂ)
        (hw : (((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) ≫ 𝒜.f = Spec.map (CommRingCat.ofHom σ.toRingHom))
        (hw' : (((e (E (σ t))).symm ((κ (σ t) • w' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) ≫ 𝒜.f = Spec.map (CommRingCat.ofHom σ.toRingHom)),
        (𝒜.L.mul (Spec.map (CommRingCat.ofHom σ.toRingHom)) ⟨(((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)), hw⟩ ⟨(((e (E (σ t))).symm ((κ (σ t) • w' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)), hw'⟩).1 =
          (((e (E (σ t))).symm ((κ (σ t) • (w + w') : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t))) ∧

      (∀ (V : 𝒜.A.Opens) (f : Γ(𝒜.A, V)),
        IsOpen {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε ∧ p.2 ∈ Metric.ball (0 : Fin 2 → ℂ) r' ∧
          ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (((e (E (σ t))).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V} ∧
        ∃ F : ℂ × (Fin 2 → ℂ) → ℂ,
          DifferentiableOn ℂ F {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε ∧ p.2 ∈ Metric.ball (0 : Fin 2 → ℂ) r' ∧
            ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (((e (E (σ t))).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V} ∧
          ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₀ t) ε → ∀ w ∈ Metric.ball (0 : Fin 2 → ℂ) r', ∀ (hV : ⊤ ≤ (((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V),
            F (σ t, w) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t))).appLE V ⊤ hV) f)) ∧

      (∀ σ₁ ∈ 𝒰, σ₁ t ∈ Metric.ball (σ₀ t) ε → ∀ w₁ : Fin 2 → ℂ,
        ∃ (V : 𝒜.A.Opens) (f₂ f₃ : Γ(𝒜.A, V)) (δ : ℝ) (D : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ))
          (F : (Fin 2 → ℂ) → (Fin 2 → ℂ)),
          0 < δ ∧
          (∀ w ∈ Metric.ball w₁ δ, ⊤ ≤ (((e (E (σ₁ t))).symm ((κ (σ₁ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ₁ t))).toAddSubgroup)).1 ≫ g (σ₁ t)) ⁻¹ᵁ V) ∧
          (∀ (w : Fin 2 → ℂ) (hV : ⊤ ≤ (((e (E (σ₁ t))).symm ((κ (σ₁ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ₁ t))).toAddSubgroup)).1 ≫ g (σ₁ t)) ⁻¹ᵁ V), w ∈ Metric.ball w₁ δ →
            F w = ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((((e (E (σ₁ t))).symm ((κ (σ₁ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ₁ t))).toAddSubgroup)).1 ≫ g (σ₁ t))).appLE V ⊤ hV) f₂),
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((((e (E (σ₁ t))).symm ((κ (σ₁ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ₁ t))).toAddSubgroup)).1 ≫ g (σ₁ t))).appLE V ⊤ hV) f₃)]) ∧
          HasFDerivAt F (D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) w₁) := by
  classical

  have hone_E : ∀ E' : FakeEllipticCurve Λ N ℂ, e E' (E'.L.one (𝟙 _)) = 0 := by
    intro E'
    have h := hE1 E' (E'.L.one (𝟙 _)) (E'.L.one (𝟙 _))
    rw [E'.L.one_mul] at h

    have : e E' (E'.L.one (𝟙 _)) + e E' (E'.L.one (𝟙 _)) = e E' (E'.L.one (𝟙 _)) + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel this
  have hpi_zero : ∀ E' : FakeEllipticCurve Λ N ℂ,
      (e E').symm ((0 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup) = E'.L.one (𝟙 _) := by
    intro E'
    rw [Equiv.symm_apply_eq, QuotientAddGroup.mk_zero]
    exact (hone_E E').symm
  have hpi_add : ∀ (E' : FakeEllipticCurve Λ N ℂ) (v w : Fin 2 → ℂ),
      (e E').symm ((v + w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup) =
        E'.L.mul (𝟙 _) ((e E').symm (v : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup))
          ((e E').symm (w : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup)) := by
    intro E' v w
    rw [Equiv.symm_apply_eq, hE1, Equiv.apply_symm_apply, Equiv.apply_symm_apply, QuotientAddGroup.mk_add]
  have hpi_eq_one_iff : ∀ (E' : FakeEllipticCurve Λ N ℂ) (v : Fin 2 → ℂ),
      (e E').symm (v : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup) = E'.L.one (𝟙 _) ↔ v ∈ latt E' := by
    intro E' v
    rw [Equiv.symm_apply_eq, hone_E]
    first
      | exact QuotientAddGroup.eq_zero_iff v

  have hc : ∀ σ ∈ 𝒰, CategoryTheory.IsPullback (g (σ t)) (E (σ t)).f 𝒜.f (Spec.map (CommRingCat.ofHom σ.toRingHom)) :=
    fun σ hσ => (hg σ hσ).elim fun h _ => h
  have hact : ∀ σ ∈ 𝒰, ∀ x : ↥Λ, (E (σ t)).act x ≫ g (σ t) = g (σ t) ≫ 𝒜.act x :=
    fun σ hσ => (hg σ hσ).elim fun _ h => h.2

  have hover0 : ∀ σ ∈ 𝒰, ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (E (σ t)).f),
      (P.1 ≫ g (σ t)) ≫ 𝒜.f = Spec.map (CommRingCat.ofHom σ.toRingHom) := by
    intro σ hσ P
    rw [Category.assoc, (hc σ hσ).w, ← Category.assoc, P.2, Category.id_comp]

  have hsurjσ : ∀ σ : Sc →ₐ[ℂ] ℂ, Function.Surjective σ.toRingHom :=
    fun σ c => ⟨algebraMap ℂ Sc c, by simp⟩
  have hmono : ∀ σ ∈ 𝒰, Mono (g (σ t)) := by
    intro σ hσ
    have hci : IsClosedImmersion (Spec.map (CommRingCat.ofHom σ.toRingHom)) :=
      IsClosedImmersion.spec_of_surjective _ (hsurjσ σ)
    have : IsClosedImmersion (g (σ t)) :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) (hc σ hσ).flip hci
    infer_instance
  have hinj0 : ∀ σ ∈ 𝒰, ∀ (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (E (σ t)).f),
      P.1 ≫ g (σ t) = Q.1 ≫ g (σ t) → P = Q := by
    intro σ hσ P Q h
    haveI := hmono σ hσ
    exact Subtype.ext ((cancel_mono (g (σ t))).mp h)

  have hgmul : ∀ σ (hσ : σ ∈ 𝒰) (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (E (σ t)).f),
      ((E (σ t)).L.mul (𝟙 _) P Q).1 ≫ g (σ t) =
        (𝒜.L.mul (Spec.map (CommRingCat.ofHom σ.toRingHom))
          ⟨P.1 ≫ g (σ t), hover0 σ hσ P⟩ ⟨Q.1 ≫ g (σ t), hover0 σ hσ Q⟩).1 := by
    intro σ hσ P Q
    obtain ⟨hc', hmul', -⟩ := hg σ hσ
    rw [hmul' P Q]
    exact mul_val_congr 𝒜.L (Category.id_comp _) _ _
  have hgone : ∀ σ (hσ : σ ∈ 𝒰),
      ((E (σ t)).L.one (𝟙 _)).1 ≫ g (σ t) = (𝒜.L.one (Spec.map (CommRingCat.ofHom σ.toRingHom))).1 := by
    intro σ hσ
    set u : SchemeHomOver (Spec.map (CommRingCat.ofHom σ.toRingHom)) 𝒜.f :=
      ⟨((E (σ t)).L.one (𝟙 _)).1 ≫ g (σ t), hover0 σ hσ _⟩ with hu
    have hmulu : 𝒜.L.mul _ u u = u := by
      apply Subtype.ext
      have := hgmul σ hσ ((E (σ t)).L.one (𝟙 _)) ((E (σ t)).L.one (𝟙 _))
      rw [(E (σ t)).L.one_mul] at this
      exact this.symm
    have := eq_one_of_mul_self 𝒜.L _ u hmulu
    exact congrArg Subtype.val this

  have hgact : ∀ σ (hσ : σ ∈ 𝒰) (x : ↥Λ) (v : Fin 2 → ℂ),
      ((e (E (σ t))).symm (v : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t) ≫ 𝒜.act x =
        ((e (E (σ t))).symm ((((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v : Fin 2 → ℂ) :
          (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t) := by
    intro σ hσ x v
    have h2 := hE2 (E (σ t)) x ((e (E (σ t))).symm (v : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)) v
      (Equiv.apply_symm_apply _ _)
    rw [Equiv.apply_eq_iff_eq_symm_apply] at h2

    rw [← h2, CerednikDrinfeld.QM.mapPt_coe, Category.assoc, hact σ hσ x]

  have hdt₀ := Algebra.ker_smul_top_sup_span_kaehlerDifferentialD_eq_top_of_bijOn_of_differentiableOn
    Sc hSc hΩ t σ₀ r 𝒰 hr hσ₀ hbij hhol σ₀ hσ₀
  haveI hSm : Smooth 𝒜.f := 𝒜.bundle.smooth
  have hsm : SmoothOfRelativeDimension 2 𝒜.f :=
    GoodReductionJacobian.RelativeGroupLaw.smoothOfRelativeDimension_of_forall_topologicalKrullDim_eq 𝒜.L 2
      (fun s => by simpa using 𝒜.dim_fibre s)
  obtain ⟨ε₁, ρ', hε₁, hρ', hball₁, U₁, hU₁aff, s₁, v₁, ψ₁, hU₁, h1U₁, hCEN, hCOORD, hAN₁, hSURJ₁, ⟨o, ho, ho₁⟩,
      ⟨ρ₂, M, hρ₂, hρ₂', hM, hM₁⟩⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_relChart_one_differentiableOn_mul_of_analyticChart
      Sc hSc hΩ t σ₀ r 𝒰 hr hσ₀ hbij hhol 𝒜.L hsm σ₀ hσ₀ hdt₀

  have analytic : ∃ (ε : ℝ) (κ : ℂ → ℂ) (r' : ℝ), 0 < ε ∧ ε ≤ r ∧ 0 < r' ∧ (∀ z ∈ Metric.ball (σ₀ t) ε, κ z ≠ 0) ∧

        (∀ (V : 𝒜.A.Opens) (f : Γ(𝒜.A, V)),
          IsOpen {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε ∧ p.2 ∈ Metric.ball (0 : Fin 2 → ℂ) r' ∧
            ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (((e (E (σ t))).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V} ∧
          ∃ F : ℂ × (Fin 2 → ℂ) → ℂ,
            DifferentiableOn ℂ F {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε ∧ p.2 ∈ Metric.ball (0 : Fin 2 → ℂ) r' ∧
              ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (((e (E (σ t))).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V} ∧
            ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₀ t) ε → ∀ w ∈ Metric.ball (0 : Fin 2 → ℂ) r', ∀ (hV : ⊤ ≤ (((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V),
              F (σ t, w) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t))).appLE V ⊤ hV) f)) := by

    have ev_congr : ∀ (P P' : Spec (CommRingCat.of ℂ) ⟶ 𝒜.A) (W : 𝒜.A.Opens) (h : ⊤ ≤ P ⁻¹ᵁ W) (h' : ⊤ ≤ P' ⁻¹ᵁ W)
        (s : Γ(𝒜.A, W)), P = P' →
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.appLE W ⊤ h) s) =
          (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P'.appLE W ⊤ h') s) := by
      rintro P P' W h h' s rfl; rfl
    have ψinj : ∀ (σ : Sc →ₐ[ℂ] ℂ) (hσ : σ ∈ 𝒰) (hz : σ t ∈ Metric.ball (σ₀ t) ε₁) (v v' : Fin 2 → ℂ)
        (hv : v ∈ Metric.ball v₁ ρ') (hv' : v' ∈ Metric.ball v₁ ρ'), ψ₁ σ v = ψ₁ σ v' → v = v' := by
      intro σ hσ hz v v' hv hv' h
      funext i
      rw [← hCOORD σ hσ hz v hv i, ← hCOORD σ hσ hz v' hv' i]
      exact ev_congr _ _ _ _ _ _ (congrArg Subtype.val h)
    have ho₀ : o (σ₀ t) = v₁ := by
      have h1 := ho₁ σ₀ hσ₀ (Metric.mem_ball_self hε₁)
      exact ψinj σ₀ hσ₀ (Metric.mem_ball_self hε₁) _ _ h1.1 (Metric.mem_ball_self hρ') (h1.2.trans hCEN.symm)
    have hρ₂4 : 0 < ρ₂ / 4 := by positivity
    obtain ⟨ε₂, hε₂, hε₂₁, ho₂⟩ : ∃ ε₂ : ℝ, 0 < ε₂ ∧ ε₂ ≤ ε₁ ∧
        ∀ z ∈ Metric.ball (σ₀ t) ε₂, o z ∈ Metric.ball v₁ (ρ₂ / 4) := by
      have hcont : ContinuousAt o (σ₀ t) :=
        ho.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε₁))
      have hev : ∀ᶠ z in 𝓝 (σ₀ t), o z ∈ Metric.ball v₁ (ρ₂ / 4) :=
        hcont.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (by rw [ho₀]; exact Metric.mem_ball_self hρ₂4))
      obtain ⟨ε₂, hε₂, hsub⟩ := Metric.eventually_nhds_iff_ball.1 hev
      exact ⟨min ε₂ ε₁, lt_min hε₂ hε₁, min_le_right _ _,
        fun z hz => hsub z (Metric.ball_subset_ball (min_le_left _ _) hz)⟩
    have hballε₂ : Metric.ball (σ₀ t) ε₂ ⊆ Metric.ball (σ₀ t) r :=
      (Metric.ball_subset_ball hε₂₁).trans hball₁

    set F : ℂ → (Fin 2 → ℂ) → (Fin 2 → ℂ) → (Fin 2 → ℂ) := fun z v w => M z (v + o z) (w + o z) - o z with hFdef
    have hρ₃ : 0 < ρ₂ / 2 := half_pos hρ₂

    have hshift : ∀ z ∈ Metric.ball (σ₀ t) ε₂, ∀ v ∈ Metric.ball (0 : Fin 2 → ℂ) (ρ₂ / 2),
        v + o z ∈ Metric.ball v₁ ρ₂ := by
      intro z hz v hv
      rw [Metric.mem_ball] at hv ⊢
      have h1 := ho₂ z hz
      rw [Metric.mem_ball] at h1
      calc dist (v + o z) v₁ ≤ dist (v + o z) (o z) + dist (o z) v₁ := dist_triangle _ _ _
        _ = dist v 0 + dist (o z) v₁ := by rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, add_sub_cancel_right, sub_zero]
        _ < ρ₂ / 2 + ρ₂ / 4 := add_lt_add hv h1
        _ ≤ ρ₂ := by linarith
    have hρ₂ρ' : Metric.ball v₁ ρ₂ ⊆ Metric.ball v₁ ρ' := Metric.ball_subset_ball hρ₂'
    have hF_diff : DifferentiableOn ℂ (fun q : ℂ × ((Fin 2 → ℂ) × (Fin 2 → ℂ)) => F q.1 q.2.1 q.2.2)
        (Metric.ball (σ₀ t) ε₂ ×ˢ (Metric.ball (0 : Fin 2 → ℂ) (ρ₂ / 2) ×ˢ Metric.ball (0 : Fin 2 → ℂ) (ρ₂ / 2))) := by
      have hofst : DifferentiableOn ℂ (fun q : ℂ × ((Fin 2 → ℂ) × (Fin 2 → ℂ)) => o q.1)
          (Metric.ball (σ₀ t) ε₂ ×ˢ (Metric.ball (0 : Fin 2 → ℂ) (ρ₂ / 2) ×ˢ Metric.ball (0 : Fin 2 → ℂ) (ρ₂ / 2))) := by
        refine (ho.mono (Metric.ball_subset_ball hε₂₁)).comp differentiableOn_fst ?_
        intro q hq; exact hq.1
      have hΨ : DifferentiableOn ℂ
          (fun q : ℂ × ((Fin 2 → ℂ) × (Fin 2 → ℂ)) => (q.1, (q.2.1 + o q.1, q.2.2 + o q.1)))
          (Metric.ball (σ₀ t) ε₂ ×ˢ (Metric.ball (0 : Fin 2 → ℂ) (ρ₂ / 2) ×ˢ Metric.ball (0 : Fin 2 → ℂ) (ρ₂ / 2))) := by
        refine differentiableOn_fst.prodMk ((?_ : DifferentiableOn ℂ _ _).prodMk ?_)
        · exact (differentiableOn_snd.fst).add hofst
        · exact (differentiableOn_snd.snd).add hofst
      have hmaps : Set.MapsTo (fun q : ℂ × ((Fin 2 → ℂ) × (Fin 2 → ℂ)) => (q.1, (q.2.1 + o q.1, q.2.2 + o q.1)))
          (Metric.ball (σ₀ t) ε₂ ×ˢ (Metric.ball (0 : Fin 2 → ℂ) (ρ₂ / 2) ×ˢ Metric.ball (0 : Fin 2 → ℂ) (ρ₂ / 2)))
          (Metric.ball (σ₀ t) ε₁ ×ˢ (Metric.ball v₁ ρ₂ ×ˢ Metric.ball v₁ ρ₂)) := by
        intro q hq
        have hz : q.1 ∈ Metric.ball (σ₀ t) ε₂ := (Set.mem_prod.1 hq).1
        have hv : q.2.1 ∈ Metric.ball (0 : Fin 2 → ℂ) (ρ₂ / 2) := (Set.mem_prod.1 (Set.mem_prod.1 hq).2).1
        have hw : q.2.2 ∈ Metric.ball (0 : Fin 2 → ℂ) (ρ₂ / 2) := (Set.mem_prod.1 (Set.mem_prod.1 hq).2).2
        exact Set.mem_prod.2 ⟨Metric.ball_subset_ball hε₂₁ hz, Set.mem_prod.2 ⟨hshift _ hz _ hv, hshift _ hz _ hw⟩⟩
      have h1 := hM.comp hΨ hmaps
      have h2 : (fun q : ℂ × ((Fin 2 → ℂ) × (Fin 2 → ℂ)) => F q.1 q.2.1 q.2.2) =
          (fun p : ℂ × ((Fin 2 → ℂ) × (Fin 2 → ℂ)) => M p.1 p.2.1 p.2.2) ∘
            (fun q : ℂ × ((Fin 2 → ℂ) × (Fin 2 → ℂ)) => (q.1, (q.2.1 + o q.1, q.2.2 + o q.1))) -
          (fun q : ℂ × ((Fin 2 → ℂ) × (Fin 2 → ℂ)) => o q.1) := by
        funext q; simp [hFdef]
      rw [h2]
      exact h1.sub hofst
    have hF_left : ∀ z ∈ Metric.ball (σ₀ t) ε₂, ∀ w ∈ Metric.ball (0 : Fin 2 → ℂ) (ρ₂ / 2), F z 0 w = w := by
      intro z hz w hw
      obtain ⟨σ, hσ, rfl⟩ := hballε₂ hz |> hbij.surjOn
      have hz1 : σ t ∈ Metric.ball (σ₀ t) ε₁ := Metric.ball_subset_ball hε₂₁ hz
      have how : w + o (σ t) ∈ Metric.ball v₁ ρ₂ := hshift _ hz w hw
      have hoo : o (σ t) ∈ Metric.ball v₁ ρ₂ := by simpa using hshift _ hz 0 (Metric.mem_ball_self hρ₃)
      obtain ⟨hmem, hmul⟩ := hM₁ σ hσ hz1 (o (σ t)) hoo (w + o (σ t)) how
      rw [(ho₁ σ hσ hz1).2, 𝒜.L.one_mul] at hmul
      have := ψinj σ hσ hz1 _ _ hmem (hρ₂ρ' how) hmul
      simp only [hFdef, zero_add]
      rw [this, add_sub_cancel_right]
    have hF_right : ∀ z ∈ Metric.ball (σ₀ t) ε₂, ∀ v ∈ Metric.ball (0 : Fin 2 → ℂ) (ρ₂ / 2), F z v 0 = v := by
      intro z hz v hv
      obtain ⟨σ, hσ, rfl⟩ := hballε₂ hz |> hbij.surjOn
      have hz1 : σ t ∈ Metric.ball (σ₀ t) ε₁ := Metric.ball_subset_ball hε₂₁ hz
      have hov : v + o (σ t) ∈ Metric.ball v₁ ρ₂ := hshift _ hz v hv
      have hoo : o (σ t) ∈ Metric.ball v₁ ρ₂ := by simpa using hshift _ hz 0 (Metric.mem_ball_self hρ₃)
      obtain ⟨hmem, hmul⟩ := hM₁ σ hσ hz1 (v + o (σ t)) hov (o (σ t)) hoo
      rw [(ho₁ σ hσ hz1).2, 𝒜.L.mul_one] at hmul
      have := ψinj σ hσ hz1 _ _ hmem (hρ₂ρ' hov) hmul
      simp only [hFdef, zero_add]
      rw [this, add_sub_cancel_right]
    have hF_comm : ∀ z ∈ Metric.ball (σ₀ t) ε₂, ∀ v w : Fin 2 → ℂ, v ∈ Metric.ball (0 : Fin 2 → ℂ) (ρ₂ / 2) →
        w ∈ Metric.ball (0 : Fin 2 → ℂ) (ρ₂ / 2) → F z v w = F z w v := by
      intro z hz v w hv hw
      obtain ⟨σ, hσ, rfl⟩ := hballε₂ hz |> hbij.surjOn
      have hz1 : σ t ∈ Metric.ball (σ₀ t) ε₁ := Metric.ball_subset_ball hε₂₁ hz
      have hov : v + o (σ t) ∈ Metric.ball v₁ ρ₂ := hshift _ hz v hv
      have how : w + o (σ t) ∈ Metric.ball v₁ ρ₂ := hshift _ hz w hw
      obtain ⟨hmem₁, hmul₁⟩ := hM₁ σ hσ hz1 _ hov _ how
      obtain ⟨hmem₂, hmul₂⟩ := hM₁ σ hσ hz1 _ how _ hov
      rw [𝒜.comm _ _ _, ← hmul₂] at hmul₁
      have := ψinj σ hσ hz1 _ _ hmem₁ hmem₂ hmul₁
      simp only [hFdef]
      rw [this]
    have hF_assoc : ∀ z ∈ Metric.ball (σ₀ t) ε₂, ∀ u v w : Fin 2 → ℂ, u ∈ Metric.ball (0 : Fin 2 → ℂ) (ρ₂ / 2) →
        v ∈ Metric.ball (0 : Fin 2 → ℂ) (ρ₂ / 2) → w ∈ Metric.ball (0 : Fin 2 → ℂ) (ρ₂ / 2) →
        F z u v ∈ Metric.ball (0 : Fin 2 → ℂ) (ρ₂ / 2) → F z v w ∈ Metric.ball (0 : Fin 2 → ℂ) (ρ₂ / 2) →
        F z (F z u v) w = F z u (F z v w) := by
      intro z hz u v w hu hv hw huv hvw
      obtain ⟨σ, hσ, rfl⟩ := hballε₂ hz |> hbij.surjOn
      have hz1 : σ t ∈ Metric.ball (σ₀ t) ε₁ := Metric.ball_subset_ball hε₂₁ hz
      have hou := hshift _ hz u hu
      have hov := hshift _ hz v hv
      have how := hshift _ hz w hw
      have houv := hshift _ hz _ huv
      have hovw := hshift _ hz _ hvw
      simp only [hFdef, sub_add_cancel] at houv hovw ⊢
      obtain ⟨m₁, e₁⟩ := hM₁ σ hσ hz1 _ hou _ hov
      obtain ⟨m₂, e₂⟩ := hM₁ σ hσ hz1 _ houv _ how
      obtain ⟨m₃, e₃⟩ := hM₁ σ hσ hz1 _ hov _ how
      obtain ⟨m₄, e₄⟩ := hM₁ σ hσ hz1 _ hou _ hovw
      rw [e₁, 𝒜.L.mul_assoc, ← e₃, ← e₄] at e₂
      rw [ψinj σ hσ hz1 _ _ m₂ m₄ e₂]

    obtain ⟨ε₃, r₃, δ₃, ex, lg, hε₃, hε₃₂, hr₃, hδ₃, hexD, hlgD, hB1⟩ :=
      LocalGroupLaw.exists_localExp_family_of_differentiableOn_of_comm_of_assoc (σ₀ t) hε₂ hρ₃ F hF_diff
        hF_left hF_right hF_comm hF_assoc

    have hε₃₁ : ε₃ ≤ ε₁ := hε₃₂.trans hε₂₁
    have hball₃r : Metric.ball (σ₀ t) ε₃ ⊆ Metric.ball (σ₀ t) r := (Metric.ball_subset_ball hε₃₁).trans hball₁
    have hex_slice : ∀ z ∈ Metric.ball (σ₀ t) ε₃, DifferentiableOn ℂ (ex z) (Metric.ball (0 : Fin 2 → ℂ) r₃) := by
      intro z hz
      have hincl : DifferentiableOn ℂ (fun v : Fin 2 → ℂ => (z, v)) (Metric.ball (0 : Fin 2 → ℂ) r₃) :=
        (differentiableOn_const _).prodMk differentiableOn_id
      exact hexD.comp hincl (fun v hv => Set.mem_prod.2 ⟨hz, hv⟩)

    obtain ⟨fs₁, η₁, hη₁, hS₁⟩ := hSURJ₁
    have hη₁2 : 0 < η₁ / 2 := half_pos hη₁
    obtain ⟨ε₄, hε₄, hε₄₃, htest⟩ : ∃ ε₄ : ℝ, 0 < ε₄ ∧ ε₄ ≤ ε₃ ∧
        ∀ (σ : Sc →ₐ[ℂ] ℂ) (hσ : σ ∈ 𝒰) (hz : σ t ∈ Metric.ball (σ₀ t) ε₄), ∀ q ∈ fs₁,
          ∀ (h : ⊤ ≤ (ψ₁ σ (o (σ t))).1 ⁻¹ᵁ U₁),
          ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((ψ₁ σ (o (σ t))).1.appLE U₁ ⊤ h) q) -
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
                (((𝒜.L.one (Spec.map (CommRingCat.ofHom σ₀.toRingHom))).1.appLE U₁ ⊤ h1U₁) q)‖ < η₁ / 2 := by
      have hF1 := fun (q : Γ(𝒜.A, U₁)) => (hAN₁ U₁ q).2
      choose Fq hFqd hFqv using hF1
      have hmem₀ : ((σ₀ t, v₁) : ℂ × (Fin 2 → ℂ)) ∈ {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε₁ ∧ p.2 ∈ Metric.ball v₁ ρ' ∧
          ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (ψ₁ σ p.2).1 ⁻¹ᵁ U₁} :=
        ⟨Metric.mem_ball_self hε₁, Metric.mem_ball_self hρ', σ₀, hσ₀, rfl,
          hU₁ σ₀ hσ₀ (Metric.mem_ball_self hε₁) _ (Metric.mem_ball_self hρ')⟩
      have hpair : ContinuousAt (fun z : ℂ => ((z, o z) : ℂ × (Fin 2 → ℂ))) (σ₀ t) :=
        continuousAt_id.prodMk (ho.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε₁)))
      have hev : ∀ q ∈ fs₁, ∀ᶠ z in 𝓝 (σ₀ t), ‖Fq q (z, o z) - Fq q (σ₀ t, v₁)‖ < η₁ / 2 := by
        intro q hq
        have hc : ContinuousAt (Fq q) (σ₀ t, v₁) :=
          (hFqd q).continuousOn.continuousAt ((hAN₁ U₁ q).1.mem_nhds hmem₀)
        have hc' : ContinuousAt (fun z : ℂ => Fq q (z, o z)) (σ₀ t) := by
          have : ContinuousAt (Fq q) ((fun z : ℂ => ((z, o z) : ℂ × (Fin 2 → ℂ))) (σ₀ t)) := by
            simpa [ho₀] using hc
          exact ContinuousAt.comp this hpair
        have := (Metric.tendsto_nhds.1 hc') (η₁ / 2) hη₁2
        simpa [ho₀, dist_eq_norm] using this
      obtain ⟨ε', hε', hε'b⟩ := Metric.eventually_nhds_iff_ball.1 ((Filter.eventually_all_finset fs₁).2 hev)
      refine ⟨min ε' ε₃, lt_min hε' hε₃, min_le_right _ _, fun σ hσ hz q hq h => ?_⟩
      have hz' : σ t ∈ Metric.ball (σ₀ t) ε' := Metric.ball_subset_ball (min_le_left _ _) hz
      have hz1 : σ t ∈ Metric.ball (σ₀ t) ε₁ :=
        Metric.ball_subset_ball ((min_le_right _ _).trans (hε₃₂.trans hε₂₁)) hz
      have h1 := hε'b _ hz' q hq
      rw [hFqv q σ hσ hz1 (o (σ t)) (ho₁ σ hσ hz1).1 h,
        hFqv q σ₀ hσ₀ (Metric.mem_ball_self hε₁) v₁ (Metric.mem_ball_self hρ')
          (hU₁ σ₀ hσ₀ (Metric.mem_ball_self hε₁) _ (Metric.mem_ball_self hρ'))] at h1
      rwa [ev_congr _ _ _ h1U₁ (hU₁ σ₀ hσ₀ (Metric.mem_ball_self hε₁) _ (Metric.mem_ball_self hρ')) q
        (congrArg Subtype.val hCEN).symm]
    have hε₄₁ : ε₄ ≤ ε₁ := hε₄₃.trans hε₃₁
    have hball₄r : Metric.ball (σ₀ t) ε₄ ⊆ Metric.ball (σ₀ t) r := (Metric.ball_subset_ball hε₄₁).trans hball₁

    have hlatt_disc : ∀ E' : FakeEllipticCurve Λ N ℂ, ∃ τ : ℝ, 0 < τ ∧ ∀ x ∈ latt E', ‖x‖ < τ → x = 0 := by
      intro E'
      obtain ⟨⟨b₀, hb₀⟩, -⟩ := hL1 E'
      have hopen : IsOpen ({0} : Set (Submodule.span ℤ (Set.range b₀))) := isOpen_discrete _
      obtain ⟨τ, hτ, hτ'⟩ := Metric.isOpen_singleton_iff.1 hopen
      refine ⟨τ, hτ, fun x hx hxn => ?_⟩
      rw [hb₀] at hx
      have := hτ' ⟨x, hx⟩ (by rw [Subtype.dist_eq]; simpa using hxn)
      exact congrArg Subtype.val this

    have hact_one : ∀ (σ : Sc →ₐ[ℂ] ℂ) (x : ↥Λ),
        (𝒜.L.one (Spec.map (CommRingCat.ofHom σ.toRingHom))).1 ≫ 𝒜.act x =
          (𝒜.L.one (Spec.map (CommRingCat.ofHom σ.toRingHom))).1 := by
      intro σ x
      have h := 𝒜.act_hom x (Spec.map (CommRingCat.ofHom σ.toRingHom)) (𝒜.L.one _) (𝒜.L.one _)
      rw [𝒜.L.one_mul] at h
      have := eq_one_of_mul_self 𝒜.L _ _ h.symm
      exact congrArg Subtype.val this
    have hANact := fun (x : ↥Λ) (i : Fin 2) => (hAN₁ ((𝒜.act x) ⁻¹ᵁ U₁) ((𝒜.act x).app U₁ (s₁ i))).2
    choose FA hFAd hFAv using hANact
    have hFAopen := fun (x : ↥Λ) => (hAN₁ ((𝒜.act x) ⁻¹ᵁ U₁) ((𝒜.act x).app U₁ (s₁ 0))).1
    set Rx : ↥Λ → ℂ → (Fin 2 → ℂ) → (Fin 2 → ℂ) := fun x z u => (fun i => FA x i (z, u + o z)) - o z with hRxdef
    set ιC : ↥Λ → Matrix (Fin 2) (Fin 2) ℂ := fun x => (ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ) with hιC

    have perfibre : ∀ (σ : Sc →ₐ[ℂ] ℂ) (hσ : σ ∈ 𝒰) (hz : σ t ∈ Metric.ball (σ₀ t) ε₄),
        ∃ (A : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ)) (τ : ℝ), 0 < τ ∧
          (∀ v ∈ Metric.ball (0 : Fin 2 → ℂ) τ,
            (A : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) v ∈ Metric.ball (0 : Fin 2 → ℂ) r₃ ∧
            ex (σ t) ((A : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) v) + o (σ t) ∈ Metric.ball v₁ ρ₂ ∧
            ((e (E (σ t))).symm (v : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t) =
              (ψ₁ σ (ex (σ t) ((A : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) v) + o (σ t))).1) ∧
          (∀ x : ↥Λ, ∃ τₓ : ℝ, 0 < τₓ ∧ ∀ u ∈ Metric.ball (0 : Fin 2 → ℂ) τₓ,
            ex (σ t) ((A : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) ((ιC x).mulVec
              ((A.symm : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) u))) = Rx x (σ t) (ex (σ t) u)) := by
      intro σ hσ hz
      have hz3 : σ t ∈ Metric.ball (σ₀ t) ε₃ := Metric.ball_subset_ball hε₄₃ hz
      have hz2 : σ t ∈ Metric.ball (σ₀ t) ε₂ := Metric.ball_subset_ball hε₃₂ hz3
      have hz1 : σ t ∈ Metric.ball (σ₀ t) ε₁ := Metric.ball_subset_ball hε₂₁ hz2
      obtain ⟨hex0, hexd, hexinj, hexmaps, hexhom, hexsurj, hlgex, hexlg⟩ := hB1 _ hz3

      set φσ : (Fin 2 → ℂ) → (Spec (CommRingCat.of ℂ) ⟶ 𝒜.A) :=
        fun v => ((e (E (σ t))).symm (v : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t) with hφσ
      have hφs : ∀ v : Fin 2 → ℂ, φσ v ≫ 𝒜.f = Spec.map (CommRingCat.ofHom σ.toRingHom) := fun v => hover0 σ hσ _
      have hφan : ∀ (W : 𝒜.A.Opens) (q : Γ(𝒜.A, W)), IsOpen {v : Fin 2 → ℂ | ⊤ ≤ (φσ v) ⁻¹ᵁ W} ∧
          ∃ Fq : (Fin 2 → ℂ) → ℂ, DifferentiableOn ℂ Fq {v : Fin 2 → ℂ | ⊤ ≤ (φσ v) ⁻¹ᵁ W} ∧
            ∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ (φσ v) ⁻¹ᵁ W),
              Fq v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((φσ v).appLE W ⊤ h) q) := by
        intro W q
        obtain ⟨hopen, Fq, hFq, hFqv⟩ := hAN (E (σ t)) ((g (σ t)) ⁻¹ᵁ W) ((g (σ t)).app W q)
        have hset : {v : Fin 2 → ℂ | ⊤ ≤ (φσ v) ⁻¹ᵁ W} =
            {v : Fin 2 → ℂ | ⊤ ≤ ((e (E (σ t))).symm (v : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ⁻¹ᵁ
              ((g (σ t)) ⁻¹ᵁ W)} := by
          ext v; simp only [Set.mem_setOf_eq, hφσ, Scheme.Hom.comp_preimage]
        refine ⟨hset ▸ hopen, Fq, hset ▸ hFq, fun v h => ?_⟩
        have h' : ⊤ ≤ ((e (E (σ t))).symm (v : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ⁻¹ᵁ ((g (σ t)) ⁻¹ᵁ W) := by
          rw [← Scheme.Hom.comp_preimage]; exact h
        rw [hFqv v h']
        exact (eval_comp _ _ _ _ h' h).symm
      have hφmul : ∀ v w : Fin 2 → ℂ,
          (𝒜.L.mul (Spec.map (CommRingCat.ofHom σ.toRingHom)) ⟨φσ v, hφs v⟩ ⟨φσ w, hφs w⟩).1 = φσ (v + w) := by
        intro v w
        simp only [hφσ]
        rw [hpi_add, hgmul σ hσ]
      have hφone : φσ 0 = (𝒜.L.one (Spec.map (CommRingCat.ofHom σ.toRingHom))).1 := by
        simp only [hφσ]
        rw [hpi_zero, hgone σ hσ]
      have hφinj : ∃ τ : ℝ, 0 < τ ∧ ∀ v ∈ Metric.ball (0 : Fin 2 → ℂ) τ, ∀ v' ∈ Metric.ball (0 : Fin 2 → ℂ) τ,
          φσ v = φσ v' → v = v' := by
        obtain ⟨τ, hτ, hdisc⟩ := hlatt_disc (E (σ t))
        refine ⟨τ / 2, half_pos hτ, fun v hv v' hv' hvv' => ?_⟩
        have h1 := hinj0 σ hσ _ _ hvv'
        have h2 : ((v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup) = (v' : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup) :=
          (e (E (σ t))).symm.injective h1
        rw [QuotientAddGroup.eq_iff_sub_mem] at h2
        have h3 : ‖v - v'‖ < τ := by
          rw [Metric.mem_ball, dist_zero_right] at hv hv'
          calc ‖v - v'‖ ≤ ‖v‖ + ‖v'‖ := norm_sub_le _ _
            _ < τ / 2 + τ / 2 := add_lt_add hv hv'
            _ = τ := by ring
        exact sub_eq_zero.1 (hdisc _ h2 h3)
      have hsurjσ : ∀ (P : SchemeHomOver (Spec.map (CommRingCat.ofHom σ.toRingHom)) 𝒜.f) (hP : ⊤ ≤ P.1 ⁻¹ᵁ U₁),
          (∀ q ∈ fs₁, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE U₁ ⊤ hP) q) -
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
                (((ψ₁ σ (o (σ t))).1.appLE U₁ ⊤ (hU₁ σ hσ hz1 _ (ho₁ σ hσ hz1).1)) q)‖ < η₁ / 2) →
          ∃ v ∈ Metric.ball v₁ ρ', ψ₁ σ v = P := by
        intro P hP hclose
        apply hS₁ σ hσ hz1 P hP
        intro q hq
        have h1 := hclose q hq
        have h2 := htest σ hσ hz q hq (hU₁ σ hσ hz1 _ (ho₁ σ hσ hz1).1)
        calc _ ≤ _ + _ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ < η₁ / 2 + η₁ / 2 := add_lt_add h1 h2
          _ = η₁ := by ring
      obtain ⟨τ₁, hfun, hτ₁, hh0, hhD, hhinj, hhP, hhmul⟩ :=
        exists_localCoord_of_pointFamily 𝒜.L (Spec.map (CommRingCat.ofHom σ.toRingHom)) φσ hφs hφan hφmul hφone hφinj
          U₁ s₁ v₁ ρ' (ψ₁ σ) (hU₁ σ hσ hz1) (hCOORD σ hσ hz1) (o (σ t)) (ho₁ σ hσ hz1).1 (ho₁ σ hσ hz1).2
          fs₁ (η₁ / 2) hη₁2 hsurjσ ρ₂ hρ₂ hρ₂' (M (σ t)) (hM₁ σ hσ hz1) (ρ₂ / 4) hρ₂4 (by linarith) (ho₂ _ hz2)

      have hoz : o (σ t) ∈ Metric.ball v₁ (ρ₂ / 4) := ho₂ _ hz2
      have hhmaps : Set.MapsTo hfun (Metric.ball (0 : Fin 2 → ℂ) τ₁) (Metric.ball (0 : Fin 2 → ℂ) (ρ₂ / 2)) := by
        intro v hv
        have h1 := (hhP v hv).1
        rw [Metric.mem_ball] at h1 hoz ⊢
        rw [dist_zero_right]
        have : hfun v = (hfun v + o (σ t) - v₁) - (o (σ t) - v₁) := by abel
        rw [this]
        calc ‖(hfun v + o (σ t) - v₁) - (o (σ t) - v₁)‖ ≤ ‖hfun v + o (σ t) - v₁‖ + ‖o (σ t) - v₁‖ := norm_sub_le _ _
          _ = dist (hfun v + o (σ t)) v₁ + dist (o (σ t)) v₁ := by rw [dist_eq_norm, dist_eq_norm]
          _ < ρ₂ / 4 + ρ₂ / 4 := add_lt_add h1 hoz
          _ = ρ₂ / 2 := by ring
      have hhhom : ∀ v w : Fin 2 → ℂ, v ∈ Metric.ball (0 : Fin 2 → ℂ) τ₁ → w ∈ Metric.ball (0 : Fin 2 → ℂ) τ₁ →
          v + w ∈ Metric.ball (0 : Fin 2 → ℂ) τ₁ → hfun (v + w) = F (σ t) (hfun v) (hfun w) := by
        intro v w hv hw hvw
        have := hhmul v w hv hw hvw
        simp only [hFdef]
        rw [← this, add_sub_cancel_right]
      have hA : HasFDerivAt hfun (fderiv ℂ hfun 0) 0 :=
        (hhD.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hτ₁))).hasFDerivAt
      obtain ⟨s', hs', hs'τ, hB2⟩ :=
        LocalGroupLaw.exists_ball_eq_localExp_comp_fderiv_of_map_add hr₃ hρ₃ (F (σ t)) (ex (σ t)) hex0 (hex_slice _ hz3)
          hexd hexinj hexmaps hexhom hτ₁ hfun hh0 hhD hhmaps hhhom (fderiv ℂ hfun 0) hA
      set A : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) := fderiv ℂ hfun 0 with hAdef

      have hAinj : Function.Injective A := by
        intro v v' hvv'

        obtain ⟨c, hc0, hcv, hcv'⟩ : ∃ c : ℝ, 0 < c ∧ (c : ℂ) • v ∈ Metric.ball (0 : Fin 2 → ℂ) s' ∧
            (c : ℂ) • v' ∈ Metric.ball (0 : Fin 2 → ℂ) s' := by
          refine ⟨s' / (2 * (‖v‖ + ‖v'‖ + 1)), by positivity, ?_, ?_⟩ <;>
          · rw [Metric.mem_ball, dist_zero_right, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
            have h1 : 0 < ‖v‖ + ‖v'‖ + 1 := by positivity
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith [norm_nonneg v, norm_nonneg v']
        have e1 := (hB2 _ hcv).2
        have e2 := (hB2 _ hcv').2
        rw [map_smul, hvv', ← map_smul] at e1
        have : hfun ((c : ℂ) • v) = hfun ((c : ℂ) • v') := by rw [e1, e2]
        have := hhinj (Metric.ball_subset_ball hs'τ hcv) (Metric.ball_subset_ball hs'τ hcv') this
        exact smul_right_injective _ (by exact_mod_cast hc0.ne') this
      let Aeqv : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ) :=
        (LinearEquiv.ofInjectiveEndo A.toLinearMap hAinj).toContinuousLinearEquiv
      have hAeqv : ∀ v, (Aeqv : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) v = A v := fun v => rfl

      have hcrd : ∀ v (hv : v ∈ Metric.ball (0 : Fin 2 → ℂ) τ₁) (i : Fin 2) (h : ⊤ ≤ (φσ v) ⁻¹ᵁ U₁),
          (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((φσ v).appLE U₁ ⊤ h) (s₁ i)) = (hfun v + o (σ t)) i := by
        intro v hv i h
        have hmem : hfun v + o (σ t) ∈ Metric.ball v₁ ρ' :=
          hρ₂ρ' (Metric.ball_subset_ball (by linarith) (hhP v hv).1)
        rw [ev_congr _ _ _ h (hU₁ σ hσ hz1 _ hmem) (s₁ i) (hhP v hv).2]
        exact hCOORD σ hσ hz1 _ hmem i

      have hP2' : ∀ x : ↥Λ, ∃ τ₂ : ℝ, 0 < τ₂ ∧ τ₂ ≤ s' ∧ ∀ v ∈ Metric.ball (0 : Fin 2 → ℂ) τ₂,
          (ιC x).mulVec v ∈ Metric.ball (0 : Fin 2 → ℂ) s' ∧ hfun ((ιC x).mulVec v) = Rx x (σ t) (hfun v) := by
        intro x
        have hcont : ContinuousAt (fun v : Fin 2 → ℂ => (ιC x).mulVec v) 0 := by
          have : Continuous (fun v : Fin 2 → ℂ => (ιC x).mulVec v) :=
            (Matrix.toLin' (ιC x)).continuous_of_finiteDimensional
          exact this.continuousAt
        have hev : ∀ᶠ v in 𝓝 (0 : Fin 2 → ℂ), (ιC x).mulVec v ∈ Metric.ball (0 : Fin 2 → ℂ) s' := by
          apply hcont.preimage_mem_nhds
          apply Metric.isOpen_ball.mem_nhds
          show (ιC x).mulVec 0 ∈ Metric.ball (0 : Fin 2 → ℂ) s'
          rw [Matrix.mulVec_zero]; exact Metric.mem_ball_self hs'
        obtain ⟨τ₂, hτ₂, hτ₂'⟩ := Metric.eventually_nhds_iff_ball.1 hev
        refine ⟨min τ₂ s', lt_min hτ₂ hs', min_le_right _ _, fun v hv => ?_⟩
        have hv₂ : v ∈ Metric.ball (0 : Fin 2 → ℂ) τ₂ := Metric.ball_subset_ball (min_le_left _ _) hv
        have hvs : v ∈ Metric.ball (0 : Fin 2 → ℂ) s' := Metric.ball_subset_ball (min_le_right _ _) hv
        have hιv : (ιC x).mulVec v ∈ Metric.ball (0 : Fin 2 → ℂ) s' := hτ₂' v hv₂
        refine ⟨hιv, ?_⟩
        have hvτ : v ∈ Metric.ball (0 : Fin 2 → ℂ) τ₁ := Metric.ball_subset_ball hs'τ hvs
        have hιvτ : (ιC x).mulVec v ∈ Metric.ball (0 : Fin 2 → ℂ) τ₁ := Metric.ball_subset_ball hs'τ hιv
        have hpt : φσ ((ιC x).mulVec v) = φσ v ≫ 𝒜.act x := by
          simp only [hφσ, hιC, Category.assoc]
          exact (hgact σ hσ x v).symm
        have hPv := hhP v hvτ
        have hPιv := hhP _ hιvτ
        have hmem_v : hfun v + o (σ t) ∈ Metric.ball v₁ ρ' := hρ₂ρ' (Metric.ball_subset_ball (by linarith) hPv.1)
        have hmem_ιv : hfun ((ιC x).mulVec v) + o (σ t) ∈ Metric.ball v₁ ρ' :=
          hρ₂ρ' (Metric.ball_subset_ball (by linarith) hPιv.1)
        have hU_ιv : ⊤ ≤ (φσ ((ιC x).mulVec v)) ⁻¹ᵁ U₁ := by
          rw [hPιv.2]; exact hU₁ σ hσ hz1 _ hmem_ιv
        have hact_mem : ⊤ ≤ (ψ₁ σ (hfun v + o (σ t))).1 ⁻¹ᵁ ((𝒜.act x) ⁻¹ᵁ U₁) := by
          rw [← Scheme.Hom.comp_preimage, ← hPv.2, ← hpt]; exact hU_ιv
        have hact_mem' : ⊤ ≤ ((ψ₁ σ (hfun v + o (σ t))).1 ≫ 𝒜.act x) ⁻¹ᵁ U₁ := by
          rw [Scheme.Hom.comp_preimage]; exact hact_mem
        funext i
        simp only [hRxdef, Pi.sub_apply]
        rw [hFAv x i σ hσ hz1 _ hmem_v hact_mem, ← eval_comp _ _ _ _ hact_mem hact_mem',
          ev_congr _ _ _ hact_mem' hU_ιv (s₁ i) (by rw [← hPv.2, ← hpt]), hcrd _ hιvτ i hU_ιv]
        simp

      refine ⟨Aeqv, s', hs', fun v hv => ?_, fun x => ?_⟩
      · have hvτ : v ∈ Metric.ball (0 : Fin 2 → ℂ) τ₁ := Metric.ball_subset_ball hs'τ hv
        obtain ⟨hAv, hfv⟩ := hB2 v hv
        refine ⟨hAv, ?_, ?_⟩
        · rw [hAeqv, ← hfv]
          exact Metric.ball_subset_ball (by linarith) (hhP v hvτ).1
        · rw [hAeqv, ← hfv]
          exact (hhP v hvτ).2
      · obtain ⟨τ₂, hτ₂, hτ₂s, hP2v⟩ := hP2' x
        have hcont : ContinuousAt (fun u : Fin 2 → ℂ => (Aeqv.symm : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) u) 0 :=
          (Aeqv.symm : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)).continuous.continuousAt
        have hev : ∀ᶠ u in 𝓝 (0 : Fin 2 → ℂ),
            (Aeqv.symm : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) u ∈ Metric.ball (0 : Fin 2 → ℂ) τ₂ := by
          apply hcont.preimage_mem_nhds
          apply Metric.isOpen_ball.mem_nhds
          show (Aeqv.symm : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) 0 ∈ Metric.ball (0 : Fin 2 → ℂ) τ₂
          rw [map_zero]; exact Metric.mem_ball_self hτ₂
        obtain ⟨τₓ, hτₓ, hτₓ'⟩ := Metric.eventually_nhds_iff_ball.1 hev
        refine ⟨τₓ, hτₓ, fun u hu => ?_⟩
        set v := (Aeqv.symm : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) u with hvdef
        have hv2 : v ∈ Metric.ball (0 : Fin 2 → ℂ) τ₂ := hτₓ' u hu
        obtain ⟨hιs, hRv⟩ := hP2v v hv2
        have e1 := (hB2 _ hιs).2
        have e2 := (hB2 v (Metric.ball_subset_ball hτ₂s hv2)).2
        have hAv : A v = u := by
          rw [← hAeqv, hvdef]; exact ContinuousLinearEquiv.apply_symm_apply _ _
        rw [hAeqv, ← e1, hRv, e2, hAv]

    haveI : Nonempty (Sc →ₐ[ℂ] ℂ) := ⟨σ₀⟩
    set σz : ℂ → (Sc →ₐ[ℂ] ℂ) := fun z => Function.invFunOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 z with hσzdef
    have hσz_mem : ∀ z ∈ Metric.ball (σ₀ t) r, σz z ∈ 𝒰 := fun z hz => Function.invFunOn_mem (hbij.surjOn hz)
    have hσz_t : ∀ z ∈ Metric.ball (σ₀ t) r, σz z t = z := fun z hz => Function.invFunOn_eq (f := fun σ : Sc →ₐ[ℂ] ℂ => σ t) (hbij.surjOn hz)
    have hσz_σ : ∀ σ ∈ 𝒰, σz (σ t) = σ := fun σ hσ => hbij.injOn.leftInvOn_invFunOn hσ
    choose Af τf hτf hP1 hP2 using perfibre

    have hzmem4 : ∀ z ∈ Metric.ball (σ₀ t) ε₄, σz z t ∈ Metric.ball (σ₀ t) ε₄ := fun z hz => by
      rw [hσz_t z (hball₄r hz)]; exact hz
    let Aeq : ∀ z : ℂ, z ∈ Metric.ball (σ₀ t) ε₄ → ((Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ)) :=
      fun z hz => Af (σz z) (hσz_mem z (hball₄r hz)) (hzmem4 z hz)
    let Bm : ↥Λ → ℂ → Matrix (Fin 2) (Fin 2) ℂ := fun x z =>
      if hz : z ∈ Metric.ball (σ₀ t) ε₄ then
        LinearMap.toMatrix' (((Aeq z hz : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)).toLinearMap ∘ₗ Matrix.toLin' (ιC x)) ∘ₗ
          ((Aeq z hz).symm : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)).toLinearMap)
      else 0
    have hBdiff : ∀ (x : ↥Λ) (i j : Fin 2), DifferentiableOn ℂ (fun z : ℂ => Bm x z i j) (Metric.ball (σ₀ t) ε₄) := by
      intro x

      set Lx : Set (ℂ × (Fin 2 → ℂ)) := {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε₁ ∧ p.2 ∈ Metric.ball v₁ ρ' ∧
          ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (ψ₁ σ p.2).1 ⁻¹ᵁ ((𝒜.act x) ⁻¹ᵁ U₁)} with hLx
      have hLx_open : IsOpen Lx := hFAopen x
      set Ψ : ℂ × (Fin 2 → ℂ) → ℂ × (Fin 2 → ℂ) := fun p => (p.1, p.2 + o p.1) with hΨ
      have hΨcont : ContinuousOn Ψ (Metric.ball (σ₀ t) ε₄ ×ˢ Set.univ) := by
        refine continuousOn_fst.prodMk (continuousOn_snd.add ?_)
        exact (ho.continuousOn.mono (Metric.ball_subset_ball hε₄₁)).comp continuousOn_fst (fun p hp => hp.1)
      have hΨdiff : DifferentiableOn ℂ Ψ (Metric.ball (σ₀ t) ε₄ ×ˢ Set.univ) := by
        refine differentiableOn_fst.prodMk (differentiableOn_snd.add ?_)
        exact (ho.mono (Metric.ball_subset_ball hε₄₁)).comp differentiableOn_fst (fun p hp => hp.1)
      set Ox : Set (ℂ × (Fin 2 → ℂ)) := (Metric.ball (σ₀ t) ε₄ ×ˢ Set.univ) ∩ Ψ ⁻¹' Lx with hOx
      have hOx_open : IsOpen Ox := hΨcont.isOpen_inter_preimage (Metric.isOpen_ball.prod isOpen_univ) hLx_open

      have hone_mem : ∀ (σ : Sc →ₐ[ℂ] ℂ) (hσ : σ ∈ 𝒰) (hz1 : σ t ∈ Metric.ball (σ₀ t) ε₁),
          ⊤ ≤ (ψ₁ σ (o (σ t))).1 ⁻¹ᵁ ((𝒜.act x) ⁻¹ᵁ U₁) := by
        intro σ hσ hz1
        rw [← Scheme.Hom.comp_preimage, (ho₁ σ hσ hz1).2, hact_one σ x, ← (ho₁ σ hσ hz1).2]
        exact hU₁ σ hσ hz1 _ (ho₁ σ hσ hz1).1
      have hO0 : ∀ z ∈ Metric.ball (σ₀ t) ε₄, (z, (0 : Fin 2 → ℂ)) ∈ Ox := by
        intro z hz
        obtain ⟨σ, hσ, rfl⟩ := hbij.surjOn (hball₄r hz)
        have hz1 : σ t ∈ Metric.ball (σ₀ t) ε₁ := Metric.ball_subset_ball hε₄₁ hz
        refine ⟨Set.mem_prod.2 ⟨hz, Set.mem_univ _⟩, ?_⟩
        show (σ t, (0 : Fin 2 → ℂ) + o (σ t)) ∈ Lx
        rw [zero_add]
        exact ⟨hz1, (ho₁ σ hσ hz1).1, σ, hσ, rfl, hone_mem σ hσ hz1⟩
      have hRdiff : DifferentiableOn ℂ (fun q : ℂ × (Fin 2 → ℂ) => Rx x q.1 q.2) Ox := by
        have h1 : DifferentiableOn ℂ (fun q : ℂ × (Fin 2 → ℂ) => fun i => FA x i (Ψ q)) Ox := by
          refine differentiableOn_pi.2 fun i => ?_
          exact (hFAd x i).comp (hΨdiff.mono Set.inter_subset_left) (fun p hp => hp.2)
        have h2 : DifferentiableOn ℂ (fun q : ℂ × (Fin 2 → ℂ) => o q.1) Ox :=
          ((ho.mono (Metric.ball_subset_ball hε₄₁)).comp differentiableOn_fst (fun p hp => hp.1)).mono
            Set.inter_subset_left
        have : (fun q : ℂ × (Fin 2 → ℂ) => Rx x q.1 q.2) =
            (fun q : ℂ × (Fin 2 → ℂ) => fun i => FA x i (Ψ q)) - (fun q : ℂ × (Fin 2 → ℂ) => o q.1) := by
          funext q; simp [hRxdef, hΨ]
        rw [this]; exact h1.sub h2
      have hR0 : ∀ z ∈ Metric.ball (σ₀ t) ε₄, Rx x z 0 = 0 := by
        intro z hz
        obtain ⟨σ, hσ, rfl⟩ := hbij.surjOn (hball₄r hz)
        have hz1 : σ t ∈ Metric.ball (σ₀ t) ε₁ := Metric.ball_subset_ball hε₄₁ hz
        funext i
        simp only [hRxdef, Pi.sub_apply, Pi.zero_apply, zero_add]
        have hm := hone_mem σ hσ hz1
        have hm' : ⊤ ≤ ((ψ₁ σ (o (σ t))).1 ≫ 𝒜.act x) ⁻¹ᵁ U₁ := by rw [Scheme.Hom.comp_preimage]; exact hm
        rw [hFAv x i σ hσ hz1 _ (ho₁ σ hσ hz1).1 hm, ← eval_comp _ _ _ _ hm hm',
          ev_congr _ _ _ hm' (hU₁ σ hσ hz1 _ (ho₁ σ hσ hz1).1) (s₁ i)
            (by rw [(ho₁ σ hσ hz1).2, hact_one σ x]),
          hCOORD σ hσ hz1 _ (ho₁ σ hσ hz1).1 i, sub_self]
      have hBm : ∀ z ∈ Metric.ball (σ₀ t) ε₄, ∃ τ : ℝ, 0 < τ ∧
          ∀ u ∈ Metric.ball (0 : Fin 2 → ℂ) τ, ex z ((Bm x z).mulVec u) = Rx x z (ex z u) := by
        intro z hz
        obtain ⟨τₓ, hτₓ, h⟩ := hP2 (σz z) (hσz_mem z (hball₄r hz)) (hzmem4 z hz) x
        refine ⟨τₓ, hτₓ, fun u hu => ?_⟩
        have := h u hu
        rw [hσz_t z (hball₄r hz)] at this
        simp only [Bm, dif_pos hz, LinearMap.toMatrix'_mulVec, LinearMap.comp_apply, Matrix.toLin'_apply]
        exact this
      exact differentiableOn_matrix_of_localConj (σ₀ t) hε₄ hr₃ hδ₃ ex lg
        (hexD.mono (Set.prod_mono (Metric.ball_subset_ball hε₄₃) subset_rfl))
        (hlgD.mono (Set.prod_mono (Metric.ball_subset_ball hε₄₃) subset_rfl))
        (fun z hz => (hB1 z (Metric.ball_subset_ball hε₄₃ hz)).1)
        (fun z hz => (hB1 z (Metric.ball_subset_ball hε₄₃ hz)).2.2.2.2.2.2.1)
        (Rx x) Ox hOx_open hO0 hRdiff hR0 (Bm x) hBm

    have hspan : Submodule.span ℂ (Set.range ιC) = ⊤ :=
      QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.span_range_map_algebraMap_eq_top_of_isMaximalOrder hB Λ hΛ ι hι
    have hMA : ∀ z (hz : z ∈ Metric.ball (σ₀ t) ε₄), ∃ Mx : Matrix (Fin 2) (Fin 2) ℂ, Mx.det ≠ 0 ∧ ∀ x : ↥Λ, Mx * ιC x = Bm x z * Mx := by
      intro z hz
      refine ⟨LinearMap.toMatrix' ((Aeq z hz : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)).toLinearMap), ?_, ?_⟩
      · have h1 : LinearMap.toMatrix' ((Aeq z hz : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)).toLinearMap) *
            LinearMap.toMatrix' ((Aeq z hz).symm : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)).toLinearMap = 1 := by
          rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
          congr 1
          ext v
          simp
        have hu : IsUnit (LinearMap.toMatrix' ((Aeq z hz : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)).toLinearMap)) :=
          IsUnit.of_mul_eq_one _ h1
        exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero
      · intro x
        simp only [Bm, dif_pos hz]
        rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_toLin' (ιC x), ← LinearMap.toMatrix'_comp,
          LinearMap.toMatrix'_toLin']
        congr 1
        ext v
        simp
    obtain ⟨ε₅, Nm, hε₅, hε₅₄, hNd, hN⟩ :=
      Matrix.exists_differentiableOn_det_ne_zero_forall_intertwiner_eq_smul ιC hspan (σ₀ t) hε₄ (fun z x => Bm x z)
        (fun x i j => hBdiff x i j) (fun z hz => hMA z hz)

    have hAdet : ∀ z (hz : z ∈ Metric.ball (σ₀ t) ε₄),
        (LinearMap.toMatrix' ((Aeq z hz : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)).toLinearMap)).det ≠ 0 := by
      intro z hz
      have h1 : LinearMap.toMatrix' ((Aeq z hz : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)).toLinearMap) *
          LinearMap.toMatrix' ((Aeq z hz).symm : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)).toLinearMap = 1 := by
        rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
        congr 1
        ext v
        simp
      exact ((Matrix.isUnit_iff_isUnit_det _).1 (IsUnit.of_mul_eq_one _ h1)).ne_zero
    have hAint : ∀ z (hz : z ∈ Metric.ball (σ₀ t) ε₄) (x : ↥Λ),
        LinearMap.toMatrix' ((Aeq z hz : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)).toLinearMap) * ιC x =
          Bm x z * LinearMap.toMatrix' ((Aeq z hz : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)).toLinearMap) := by
      intro z hz x
      simp only [Bm, dif_pos hz]
      rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_toLin' (ιC x), ← LinearMap.toMatrix'_comp,
        LinearMap.toMatrix'_toLin']
      congr 1
      ext v
      simp
    have hcz : ∀ z (hz : z ∈ Metric.ball (σ₀ t) ε₅), ∃ c : ℂ, c ≠ 0 ∧
        LinearMap.toMatrix' ((Aeq z (Metric.ball_subset_ball hε₅₄ hz) : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)).toLinearMap) =
          c • Nm z := by
      intro z hz
      have hz4 : z ∈ Metric.ball (σ₀ t) ε₄ := Metric.ball_subset_ball hε₅₄ hz
      obtain ⟨c, hc⟩ := (hN z hz).2.2 _ (hAint z hz4)
      refine ⟨c, ?_, hc⟩
      rintro rfl
      apply hAdet z hz4
      rw [hc, zero_smul, Matrix.det_zero]
    choose cf hcf0 hcf using hcz
    let κ : ℂ → ℂ := fun z => if hz : z ∈ Metric.ball (σ₀ t) ε₅ then (cf z hz)⁻¹ else 1
    have hκne5 : ∀ z ∈ Metric.ball (σ₀ t) ε₅, κ z ≠ 0 := by
      intro z hz; simp only [κ, dif_pos hz]; exact inv_ne_zero (hcf0 z hz)
    have hκA : ∀ z (hz : z ∈ Metric.ball (σ₀ t) ε₅) (v : Fin 2 → ℂ),
        (Aeq z (Metric.ball_subset_ball hε₅₄ hz) : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) (κ z • v) = (Nm z).mulVec v := by
      intro z hz v
      simp only [κ, dif_pos hz]
      rw [map_smul]
      have : (Aeq z (Metric.ball_subset_ball hε₅₄ hz) : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) v =
          (LinearMap.toMatrix' ((Aeq z (Metric.ball_subset_ball hε₅₄ hz) : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)).toLinearMap)).mulVec v :=
        (LinearMap.toMatrix'_mulVec _ v).symm
      rw [this, hcf z hz, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (hcf0 z hz), one_smul]

    obtain ⟨ε₆, r', hε₆, hε₆₅, hr', hNr⟩ : ∃ ε₆ r' : ℝ, 0 < ε₆ ∧ ε₆ ≤ ε₅ ∧ 0 < r' ∧
        ∀ z ∈ Metric.ball (σ₀ t) ε₆, ∀ w ∈ Metric.ball (0 : Fin 2 → ℂ) r',
          (Nm z).mulVec w ∈ Metric.ball (0 : Fin 2 → ℂ) (r₃ / 2) := by
      exact exists_ball_mulVec_mem_ball (σ₀ t) hε₅ (half_pos hr₃) Nm hNd
    have hε₆₄ : ε₆ ≤ ε₄ := hε₆₅.trans hε₅₄
    have hε₆₁ : ε₆ ≤ ε₁ := hε₆₄.trans hε₄₁
    have hε₆r : ε₆ ≤ r := hε₆₁.trans (le_of_ball_subset_ball hε₁ hball₁)

    have hkey : ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₀ t) ε₆ → ∀ w ∈ Metric.ball (0 : Fin 2 → ℂ) r',
        ((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t) =
          (ψ₁ σ (ex (σ t) ((Nm (σ t)).mulVec w) + o (σ t))).1 := by
      intro σ hσ hz w hw
      have hz5 : σ t ∈ Metric.ball (σ₀ t) ε₅ := Metric.ball_subset_ball hε₆₅ hz
      have hz4 : σ t ∈ Metric.ball (σ₀ t) ε₄ := Metric.ball_subset_ball hε₅₄ hz5
      have hz3 : σ t ∈ Metric.ball (σ₀ t) ε₃ := Metric.ball_subset_ball hε₄₃ hz4
      have hz2 : σ t ∈ Metric.ball (σ₀ t) ε₂ := Metric.ball_subset_ball hε₃₂ hz3
      have hz1 : σ t ∈ Metric.ball (σ₀ t) ε₁ := Metric.ball_subset_ball hε₂₁ hz2
      obtain ⟨hex0, hexd, hexinj, hexmaps, hexhom, -, -, -⟩ := hB1 _ hz3

      have hAf_eq : ∀ (σ' : Sc →ₐ[ℂ] ℂ) (h1 : σ' ∈ 𝒰) (h2 : σ' t ∈ Metric.ball (σ₀ t) ε₄) (h : σ' = σ) (v : Fin 2 → ℂ),
          (Af σ' h1 h2 : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) v = (Af σ hσ hz4 : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) v := by
        rintro σ' h1 h2 rfl v; rfl
      have hzσ : σ t ∈ Metric.ball (σ₀ t) r := hball₄r hz4
      have hAN : ∀ v : Fin 2 → ℂ, (Af σ hσ hz4 : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) (κ (σ t) • v) = (Nm (σ t)).mulVec v := by
        intro v
        rw [← hAf_eq (σz (σ t)) (hσz_mem _ hzσ) (hzmem4 _ hz4) (hσz_σ σ hσ)]
        exact hκA (σ t) hz5 v

      let Xp := SchemeHomOver (Spec.map (CommRingCat.ofHom σ.toRingHom)) 𝒜.f
      let Lf : (Fin 2 → ℂ) → Xp := fun a =>
        ⟨((e (E (σ t))).symm ((κ (σ t) • a : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t),
          hover0 σ hσ _⟩
      let Rf : (Fin 2 → ℂ) → Xp := fun a => ψ₁ σ (ex (σ t) ((Nm (σ t)).mulVec a) + o (σ t))
      have hL : ∀ a b : Fin 2 → ℂ, Lf (a + b) = 𝒜.L.mul _ (Lf a) (Lf b) := by
        intro a b
        apply Subtype.ext
        show ((e (E (σ t))).symm ((κ (σ t) • (a + b) : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t) = _
        rw [smul_add, hpi_add, hgmul σ hσ]
      have hR : ∀ a b : Fin 2 → ℂ, a ∈ Metric.ball (0 : Fin 2 → ℂ) r' → b ∈ Metric.ball (0 : Fin 2 → ℂ) r' →
          a + b ∈ Metric.ball (0 : Fin 2 → ℂ) r' → Rf (a + b) = 𝒜.L.mul _ (Rf a) (Rf b) := by
        intro a b ha hb hab
        have hhalf : Metric.ball (0 : Fin 2 → ℂ) (r₃ / 2) ⊆ Metric.ball (0 : Fin 2 → ℂ) r₃ := Metric.ball_subset_ball (by linarith)
        have hNa := hNr _ hz a ha
        have hNb := hNr _ hz b hb
        have hNab := hNr _ hz (a + b) hab
        rw [Matrix.mulVec_add] at hNab
        have h1 := hexhom _ _ (hhalf hNa) (hhalf hNb) (hhalf hNab)
        have hpa : ex (σ t) ((Nm (σ t)).mulVec a) + o (σ t) ∈ Metric.ball v₁ ρ₂ := hshift _ hz2 _ (hexmaps (hhalf hNa))
        have hpb : ex (σ t) ((Nm (σ t)).mulVec b) + o (σ t) ∈ Metric.ball v₁ ρ₂ := hshift _ hz2 _ (hexmaps (hhalf hNb))
        obtain ⟨-, hmul⟩ := hM₁ σ hσ hz1 _ hpa _ hpb
        show ψ₁ σ (ex (σ t) ((Nm (σ t)).mulVec (a + b)) + o (σ t)) = _
        rw [← hmul, Matrix.mulVec_add, h1]
        congr 1
        simp only [hFdef, sub_add_cancel]

      have hκpos : 0 < ‖κ (σ t)‖ + 1 := by positivity
      have hs : 0 < τf σ hσ hz4 / (‖κ (σ t)‖ + 1) := div_pos (hτf σ hσ hz4) hκpos
      have hagree : ∀ a ∈ Metric.ball (0 : Fin 2 → ℂ) (τf σ hσ hz4 / (‖κ (σ t)‖ + 1)), Lf a = Rf a := by
        intro a ha
        have hκa : κ (σ t) • a ∈ Metric.ball (0 : Fin 2 → ℂ) (τf σ hσ hz4) := by
          rw [Metric.mem_ball, dist_zero_right] at ha ⊢
          rw [norm_smul]
          calc ‖κ (σ t)‖ * ‖a‖ ≤ (‖κ (σ t)‖ + 1) * ‖a‖ := by
                exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
            _ < (‖κ (σ t)‖ + 1) * (τf σ hσ hz4 / (‖κ (σ t)‖ + 1)) := mul_lt_mul_of_pos_left ha hκpos
            _ = τf σ hσ hz4 := by field_simp
        obtain ⟨-, -, hP⟩ := hP1 σ hσ hz4 _ hκa
        apply Subtype.ext
        show ((e (E (σ t))).symm ((κ (σ t) • a : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t) =
          (ψ₁ σ (ex (σ t) ((Nm (σ t)).mulVec a) + o (σ t))).1
        rw [hP, hAN]
      have := eqOn_ball_of_map_add (𝒜.L.mul _) Lf Rf hs hL hR hagree w hw
      exact congrArg Subtype.val this

    have hΘ : DifferentiableOn ℂ (fun p : ℂ × (Fin 2 → ℂ) => ex p.1 ((Nm p.1).mulVec p.2) + o p.1)
        (Metric.ball (σ₀ t) ε₆ ×ˢ Metric.ball (0 : Fin 2 → ℂ) r') := by
      exact differentiableOn_exp_mulVec_add (σ₀ t) (hε₆₄.trans hε₄₃) ex Nm o hexD
        (fun i j => (hNd i j).mono (Metric.ball_subset_ball hε₆₅)) (ho.mono (Metric.ball_subset_ball hε₆₁))
        (fun z hz w hw => Metric.ball_subset_ball (by linarith) (hNr z hz w hw))
    have hΘmem : ∀ z ∈ Metric.ball (σ₀ t) ε₆, ∀ w ∈ Metric.ball (0 : Fin 2 → ℂ) r',
        ex z ((Nm z).mulVec w) + o z ∈ Metric.ball v₁ ρ' := by
      intro z hz w hw
      have hz3 : z ∈ Metric.ball (σ₀ t) ε₃ := Metric.ball_subset_ball (hε₆₄.trans hε₄₃) hz
      have h1 := ((hB1 z hz3).2.2.2.1) (Metric.ball_subset_ball (by linarith) (hNr z hz w hw))
      exact hρ₂ρ' (hshift z (Metric.ball_subset_ball (hε₆₄.trans (hε₄₃.trans hε₃₂)) hz) _ h1)
    have hLOCAN := locAn_of_chart_reparam Sc t σ₀ 𝒰 ε₁ ρ' v₁ ψ₁ hAN₁
      (fun z w => ex z ((Nm z).mulVec w) + o z) ε₆ r' hε₆ hε₆₁ hr' hΘ hΘmem
      (fun σ w => ((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t))
      hkey
    exact ⟨ε₆, κ, r', hε₆, hε₆r, hr', fun z hz => hκne5 z (Metric.ball_subset_ball hε₆₅ hz), hLOCAN⟩
  obtain ⟨ε, κ, r', hε, hεr, hr', hκ, hLOCAN⟩ := analytic

  have fibcov :

        (∀ σ₁ ∈ 𝒰, σ₁ t ∈ Metric.ball (σ₀ t) ε → ∀ w₁ : Fin 2 → ℂ,
          ∃ (V : 𝒜.A.Opens) (f₂ f₃ : Γ(𝒜.A, V)) (δ : ℝ) (D : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ))
            (F : (Fin 2 → ℂ) → (Fin 2 → ℂ)),
            0 < δ ∧
            (∀ w ∈ Metric.ball w₁ δ, ⊤ ≤ (((e (E (σ₁ t))).symm ((κ (σ₁ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ₁ t))).toAddSubgroup)).1 ≫ g (σ₁ t)) ⁻¹ᵁ V) ∧
            (∀ (w : Fin 2 → ℂ) (hV : ⊤ ≤ (((e (E (σ₁ t))).symm ((κ (σ₁ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ₁ t))).toAddSubgroup)).1 ≫ g (σ₁ t)) ⁻¹ᵁ V), w ∈ Metric.ball w₁ δ →
              F w = ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((((e (E (σ₁ t))).symm ((κ (σ₁ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ₁ t))).toAddSubgroup)).1 ≫ g (σ₁ t))).appLE V ⊤ hV) f₂),
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((((e (E (σ₁ t))).symm ((κ (σ₁ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ₁ t))).toAddSubgroup)).1 ≫ g (σ₁ t))).appLE V ⊤ hV) f₃)]) ∧
            HasFDerivAt F (D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) w₁) := by
    intro σ₁ hσ₁ hz₁ w₁
    have hcne : κ (σ₁ t) ≠ 0 := hκ _ hz₁

    haveI hcl : IsClosedImmersion (g (σ₁ t)) :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) (hc σ₁ hσ₁).flip
        (IsClosedImmersion.spec_of_surjective _ (hsurjσ σ₁))

    obtain ⟨U, f₁, f₂, ε', D', F', hε', hU', hF', hD'⟩ := hCOV (E (σ₁ t)) (κ (σ₁ t) • w₁)

    obtain ⟨V, f₂', f₃', ε'', F'', hε'', hV, hF'', hD''⟩ :=
      AlgebraicGeometry.IsClosedImmersion.exists_hasFDerivAt_appLE_comp_of_hasFDerivAt_appLE (g (σ₁ t))
        (fun v : Fin 2 → ℂ => ((e (E (σ₁ t))).symm (v : (Fin 2 → ℂ) ⧸ (latt (E (σ₁ t))).toAddSubgroup)).1)
        (κ (σ₁ t) • w₁)
        (by
          intro W hW
          obtain ⟨hopen, -⟩ := hAN (E (σ₁ t)) W (0 : Γ((E (σ₁ t)).A, W))
          obtain ⟨ε₀, hε₀, hsub⟩ := Metric.isOpen_iff.1 hopen _ hW
          exact ⟨ε₀, hε₀, fun v hv => hsub hv⟩)
        U f₁ f₂ ε' D' F' hε' hU' hF' hD'

    set c : ℂ := κ (σ₁ t) with hcdef
    let Sc' : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ) := (LinearEquiv.smulOfNeZero ℂ (Fin 2 → ℂ) c hcne).toContinuousLinearEquiv
    have hSc' : ∀ w : Fin 2 → ℂ, Sc' w = c • w := fun w => by simp [Sc']
    have hball : ∀ w ∈ Metric.ball w₁ (ε'' / ‖c‖), c • w ∈ Metric.ball (c • w₁) ε'' := by
      intro w hw
      rw [Metric.mem_ball, dist_smul₀]
      rw [Metric.mem_ball] at hw
      have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hcne
      calc ‖c‖ * dist w w₁ < ‖c‖ * (ε'' / ‖c‖) := mul_lt_mul_of_pos_left hw hcpos
        _ = ε'' := by field_simp
    refine ⟨V, f₂', f₃', ε'' / ‖c‖, Sc'.trans D', fun w => F'' (c • w), div_pos hε'' (norm_pos_iff.mpr hcne), ?_, ?_, ?_⟩
    · intro w hw
      exact hV _ (hball w hw)
    · intro w hV' hw
      exact hF'' (c • w) hV' (hball w hw)
    · have h1 : HasFDerivAt (fun w : Fin 2 → ℂ => c • w) (Sc' : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) w₁ := by
        have := (hasFDerivAt_id (𝕜 := ℂ) w₁).const_smul c
        convert this using 1 <;> first | rfl | exact ContinuousLinearMap.ext fun w => by simp [hSc']
      have h2 := hD''.comp w₁ h1
      convert h2 using 1 <;> first | rfl | (ext1 w; simp)

  refine ⟨ε, κ, r', hε, hεr, hr', hκ, hinj0, ?_, ?_, ?_, hLOCAN, fibcov⟩
  ·
    intro σ hσ hz w
    rw [← hgone σ hσ]
    constructor
    · intro h
      exact (hpi_eq_one_iff _ _).1 (hinj0 σ hσ _ _ h)
    · intro h
      rw [(hpi_eq_one_iff _ _).2 h]
  ·
    intro σ hσ w
    exact hover0 σ hσ _
  ·
    intro σ hσ w w' hw hw'
    rw [smul_add, hpi_add, hgmul σ hσ]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isLocalHom_differentiableOn_uniformization_family_near_zero
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isLocalHom_differentiableOn_uniformization_family_near_zero (solution)
