-- Prove2me | solution 1 for CerednikDrinfeld.QM.exists_meromorphicRealization_of_periodMap_of_analyticAt_evalAt_of_two_mul_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/f9719d37-f687-525c-be42-c13332a23f1b

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_AlgebraicCurve_CurveModel_place_eq_of_pointEquivPlace_symm_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_exists_meromorphicRealization_of_periodMap_of_analyticAt_evalAt_of_two_mul_dvd

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology

open scoped Topology
open Filter UpperHalfPlane

namespace P6aAn

theorem coe_preimage_compl_singleton (τ₀ : UpperHalfPlane) :
    ((↑) : UpperHalfPlane → ℂ) ⁻¹' {(τ₀ : ℂ)}ᶜ = {τ₀}ᶜ := by
  ext τ
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, UpperHalfPlane.coe_inj]

theorem map_coe_nhdsNE (τ₀ : UpperHalfPlane) :
    map ((↑) : UpperHalfPlane → ℂ) (𝓝[≠] τ₀) = 𝓝[≠] (τ₀ : ℂ) := by
  rw [← coe_preimage_compl_singleton τ₀]
  exact UpperHalfPlane.isOpenEmbedding_coe.map_nhdsWithin_preimage_eq _ τ₀

private scoped instance _root_.P6aAn.nhdsNE_neBot (τ₀ : UpperHalfPlane) : (𝓝[≠] τ₀).NeBot := by
  refine Filter.NeBot.of_map (m := ((↑) : UpperHalfPlane → ℂ)) ?_
  rw [map_coe_nhdsNE]
  exact NormedField.nhdsNE_neBot _

p2m_export "P6aAn" "nhdsNE_neBot"
theorem eventually_nhds_ofComplex {τ₀ : UpperHalfPlane} {p : UpperHalfPlane → Prop} (h : ∀ᶠ τ in 𝓝 τ₀, p τ) :
    ∀ᶠ z in 𝓝 (τ₀ : ℂ), p (ofComplex z) ∧ ((ofComplex z : UpperHalfPlane) : ℂ) = z := by
  rw [← UpperHalfPlane.isOpenEmbedding_coe.map_nhds_eq, Filter.eventually_map]
  exact h.mono fun τ hτ => by rw [ofComplex_apply]; exact ⟨hτ, rfl⟩

theorem eventually_nhdsNE_ofComplex {τ₀ : UpperHalfPlane} {p : UpperHalfPlane → Prop} (h : ∀ᶠ τ in 𝓝[≠] τ₀, p τ) :
    ∀ᶠ z in 𝓝[≠] (τ₀ : ℂ), p (ofComplex z) ∧ ((ofComplex z : UpperHalfPlane) : ℂ) = z := by
  rw [← map_coe_nhdsNE, Filter.eventually_map]
  exact h.mono fun τ hτ => by rw [ofComplex_apply]; exact ⟨hτ, rfl⟩

theorem tendsto_coe (τ₀ : UpperHalfPlane) : Tendsto ((↑) : UpperHalfPlane → ℂ) (𝓝 τ₀) (𝓝 (τ₀ : ℂ)) :=
  UpperHalfPlane.continuous_coe.continuousAt

section eval

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F)

theorem evalAt_inv_of_mem (hv : v.IsRational) {x : F} (hx0 : x ≠ 0) (hx : x ∈ v.toValuationSubring)
    (hx' : x⁻¹ ∈ v.toValuationSubring) : v.evalAt x ≠ 0 ∧ v.evalAt x⁻¹ = (v.evalAt x)⁻¹ := by
  have h := v.evalAt_mul_of_mem hv hx hx'
  rw [mul_inv_cancel₀ hx0, v.evalAt_one] at h
  exact ⟨left_ne_zero_of_mul_eq_one h.symm, eq_inv_of_mul_eq_one_right h.symm⟩

theorem evalAt_eq_zero_of_inv_not_mem (hv : v.IsRational) {y : F} (hy : y ∈ v.toValuationSubring)
    (hy' : y⁻¹ ∉ v.toValuationSubring) : v.evalAt y = 0 := by
  have hnu : ¬ IsUnit (⟨y, hy⟩ : v.toValuationSubring) := by
    rintro ⟨u, hu⟩
    apply hy'
    have h1 : ((u⁻¹ : (v.toValuationSubring)ˣ) : v.toValuationSubring) * (u : v.toValuationSubring) = 1 := u.inv_mul
    have h2 : (((u⁻¹ : (v.toValuationSubring)ˣ) : v.toValuationSubring) : F) * y = 1 := by
      have := congrArg (fun a : v.toValuationSubring => (a : F)) h1
      simp only [hu, Subring.coe_mul, OneMemClass.coe_one] at this
      exact this
    rw [← eq_inv_of_mul_eq_one_left h2]
    exact ((u⁻¹ : (v.toValuationSubring)ˣ) : v.toValuationSubring).2
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv hy, map_zero, IsLocalRing.residue_eq_zero_iff]
  exact (IsLocalRing.mem_maximalIdeal _).2 hnu

end eval

section main

variable {Fc : Type} [Field Fc] [Algebra ℂ Fc] (plc : UpperHalfPlane → AlgebraicCurve.Place ℂ Fc)
  (hrat : ∀ τ : UpperHalfPlane, (plc τ).IsRational)
  (hF : ∀ (τ₀ : UpperHalfPlane) (x : Fc), x ∈ (plc τ₀).toValuationSubring →
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F (τ₀ : ℂ) ∧
      ∀ᶠ τ in 𝓝 τ₀, x ∈ (plc τ).toValuationSubring ∧ F (τ : ℂ) = (plc τ).evalAt x)
  (hreg : ∀ (τ₀ : UpperHalfPlane) (x : Fc), ∀ᶠ z in 𝓝[≠] τ₀, x ∈ (plc z).toValuationSubring)

include hrat hF hreg in

theorem exists_pole_fn {x : Fc} {τ : UpperHalfPlane} (hx : x ∉ (plc τ).toValuationSubring) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G (τ : ℂ) ∧ G (τ : ℂ) = 0 ∧
      ∀ᶠ z in 𝓝[≠] τ, G ((z : UpperHalfPlane) : ℂ) ≠ 0 ∧ (plc z).evalAt x = (G ((z : UpperHalfPlane) : ℂ))⁻¹ := by
  have hx0 : x ≠ 0 := by rintro rfl; exact hx (zero_mem _)
  have hy : x⁻¹ ∈ (plc τ).toValuationSubring := ((plc τ).toValuationSubring.mem_or_inv_mem x).resolve_left hx
  obtain ⟨G, hGa, hGe⟩ := hF τ x⁻¹ hy
  refine ⟨G, hGa, ?_, ?_⟩
  · obtain ⟨-, h⟩ := hGe.self_of_nhds
    rw [h]
    exact evalAt_eq_zero_of_inv_not_mem (plc τ) (hrat τ) hy (by rwa [inv_inv])
  · filter_upwards [hreg τ x, hGe.filter_mono nhdsWithin_le_nhds] with z hxz hyz
    obtain ⟨hne, hinv⟩ := evalAt_inv_of_mem (plc z) (hrat z) (inv_ne_zero hx0) hyz.1 (by rwa [inv_inv])
    rw [inv_inv] at hinv
    rw [← hyz.2] at hne hinv
    exact ⟨hne, hinv⟩

include hrat hF hreg in

theorem meromorphicAt_evalAt (x : Fc) (τ : UpperHalfPlane) :
    MeromorphicAt (fun z : ℂ => (plc (UpperHalfPlane.ofComplex z)).evalAt x) (τ : ℂ) := by
  by_cases hx : x ∈ (plc τ).toValuationSubring
  · obtain ⟨F, hFa, hFe⟩ := hF τ x hx
    refine hFa.meromorphicAt.congr ?_
    have h := eventually_nhds_ofComplex hFe
    refine (h.filter_mono nhdsWithin_le_nhds).mono fun z hz => ?_
    obtain ⟨⟨-, h2⟩, h3⟩ := hz
    rw [h3] at h2
    exact h2
  · obtain ⟨G, hGa, -, hGe⟩ := exists_pole_fn plc hrat hF hreg hx
    refine hGa.meromorphicAt.inv.congr ?_
    refine (eventually_nhdsNE_ofComplex hGe).mono fun z hz => ?_
    obtain ⟨⟨-, h2⟩, h3⟩ := hz
    rw [h3] at h2
    show (G z)⁻¹ = _
    exact h2.symm

include hrat hF hreg in

theorem mem_iff_isBoundedUnder (x : Fc) (τ : UpperHalfPlane) :
    x ∈ (plc τ).toValuationSubring ↔
      Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : UpperHalfPlane => ‖(plc z).evalAt x‖) := by
  constructor
  · intro hx
    obtain ⟨F, hFa, hFe⟩ := hF τ x hx
    have h1 : ∀ᶠ w in 𝓝 (τ : ℂ), ‖F w‖ < ‖F (τ : ℂ)‖ + 1 :=
      (hFa.continuousAt.norm.tendsto).eventually_lt_const (lt_add_one _)
    have h2 : ∀ᶠ t in 𝓝 τ, ‖F ((t : UpperHalfPlane) : ℂ)‖ < ‖F (τ : ℂ)‖ + 1 := (tendsto_coe τ).eventually h1
    refine ⟨‖F (τ : ℂ)‖ + 1, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [(h2.and hFe).filter_mono nhdsWithin_le_nhds] with t ht
    rw [← ht.2.2]
    exact ht.1.le
  · intro hb
    by_contra hx
    obtain ⟨G, hGa, hG0, hGe⟩ := exists_pole_fn plc hrat hF hreg hx
    obtain ⟨C, hC⟩ := hb
    rw [Filter.eventually_map] at hC
    have hCpos : 0 < |C| + 1 := by positivity
    have h1 : ∀ᶠ w in 𝓝 (τ : ℂ), ‖G w‖ < (|C| + 1)⁻¹ := by
      have ht : Tendsto (fun w => ‖G w‖) (𝓝 (τ : ℂ)) (𝓝 0) := by
        have := hGa.continuousAt.norm.tendsto
        rwa [hG0, norm_zero] at this
      exact ht.eventually_lt_const (inv_pos.2 hCpos)
    have h2 : ∀ᶠ t in 𝓝 τ, ‖G ((t : UpperHalfPlane) : ℂ)‖ < (|C| + 1)⁻¹ := (tendsto_coe τ).eventually h1
    have hfalse : ∀ᶠ t in 𝓝[≠] τ, False := by
      filter_upwards [h2.filter_mono nhdsWithin_le_nhds, hGe, hC] with t ht hte htC
      rw [hte.2, norm_inv] at htC
      have hlt : |C| + 1 < ‖G ((t : UpperHalfPlane) : ℂ)‖⁻¹ := (lt_inv_comm₀ (norm_pos_iff.2 hte.1) hCpos).1 ht
      linarith [le_abs_self C]
    exact hfalse.exists.elim fun _ h => h

end main

end P6aAn
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_meromorphicRealization_of_periodMap_of_analyticAt_evalAt_of_two_mul_dvd.P6aAn"

theorem solution
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) (hD : 2 * N * q * q' ∣ D)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)

    (X : Scheme.{0}) [hXint : IsIntegral X]
    (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (hsmooth : Smooth πX) (hproper : IsProper πX)
    (pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ _) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.Iso E E' → pt S s E = pt S s E')
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ _) (s' : Spec (CommRingCat.of S') ⟶ _),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    (pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _) (P : SchemeHomOver s πX),
      ∃ E : FakeEllipticCurve Λ N k, pt k s E = P)
    (pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _)
      (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E')
    (hsmooth1 : SmoothOfRelativeDimension 1 πX)
    (hgeom : ∀ (k : Type) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      IsIntegral (CategoryTheory.Limits.pullback πX s))

    (Fc₀ : Type) [Field Fc₀] [Algebra ℂ Fc₀] [AlgebraicCurve.IsCurveOver ℂ Fc₀] [Algebra.EssFiniteType ℂ Fc₀]
    (U₀ : ModularCurve.UniformizedHeckeCurve (fuchsianGroup R ι) Fc₀)
    (h₀ :
      Function.Surjective U₀.pt ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ∃ S : Finset ℍ[ℚ, a, b],
        (∀ x ∈ S, x ∈ R ∧ nrd x = ℓ ∧
          ∃ h ∈ (if ℓ ∣ N then levelHeckeUSet Λ R ℓ else primeHeckeSet R ℓ),
            (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = x ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) ∧
        (∀ y : ℍ[ℚ, a, b], y ∈ R → nrd y = ℓ →
          (∃ h ∈ (if ℓ ∣ N then levelHeckeUSet Λ R ℓ else primeHeckeSet R ℓ),
            (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = y ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) →
          ∃! x, x ∈ S ∧ ∃ u : ℍ[ℚ, a, b], IsUnitOf R u ∧ nrd u = 1 ∧ u * x = y) ∧
        (U₀.heckePoints ℓ hℓ).map (fun g => (g : Matrix (Fin 2) (Fin 2) ℝ)) = S.val.map ι) ∧
      (∀ (x : Fc₀) (τ : UpperHalfPlane), MeromorphicAt (fun z : ℂ => U₀.realize x (UpperHalfPlane.ofComplex z)) (τ : ℂ)) ∧
      (∀ (x y : Fc₀) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, U₀.realize (x + y) z = U₀.realize x z + U₀.realize y z) ∧
      (∀ (x y : Fc₀) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, U₀.realize (x * y) z = U₀.realize x z * U₀.realize y z) ∧
      (∀ (c : ℂ) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, U₀.realize (algebraMap ℂ Fc₀ c) z = c) ∧
      (∀ x y : Fc₀, (∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, U₀.realize x z = U₀.realize y z) → x = y) ∧
      (∀ x : Fc₀, ∀ γ ∈ fuchsianGroup R ι, ∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, U₀.realize x (γ • z) = U₀.realize x z) ∧
      (∀ f : UpperHalfPlane → ℂ, (∀ τ : UpperHalfPlane, MeromorphicAt (fun z : ℂ => f (UpperHalfPlane.ofComplex z)) (τ : ℂ)) →
        (∀ γ ∈ fuchsianGroup R ι, ∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, f (γ • z) = f z) →
        ∃ x : Fc₀, ∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, U₀.realize x z = f z))

    (sC : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (Fc : Type) [Field Fc] [Algebra ℂ Fc] [AlgebraicCurve.IsCurveOver ℂ Fc] [Algebra.EssFiniteType ℂ Fc]
    (𝔐c : AlgebraicCurve.CurveModel ℂ Fc)
    (e𝔐c : 𝔐c.C ⟶ CategoryTheory.Limits.pullback πX sC) (he𝔐c : IsIso e𝔐c)
    (he𝔐c_snd : e𝔐c ≫ CategoryTheory.Limits.pullback.snd πX sC = 𝔐c.toBase)

    (perE : FakeEllipticCurve Λ N ℂ → UpperHalfPlane)
    (hper :

      (∀ E E' : FakeEllipticCurve Λ N ℂ,
        FakeEllipticCurve.Iso E E' ↔ U₀.pt (perE E) = U₀.pt (perE E')) ∧

      (∀ τ : UpperHalfPlane, ∃ E : FakeEllipticCurve Λ N ℂ, U₀.pt (perE E) = U₀.pt τ))

    (hhol : ∀ (τ₀ : UpperHalfPlane) (E₀ : FakeEllipticCurve Λ N ℂ) (𝔓₀ : Place ℂ Fc),
      (pt _ sC E₀).1 = (𝔐c.pointEquivPlace.symm 𝔓₀).1 ≫ e𝔐c ≫ CategoryTheory.Limits.pullback.fst πX sC →
      U₀.pt τ₀ = U₀.pt (perE E₀) →
      ∀ x : Fc, x ∈ 𝔓₀.toValuationSubring →
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (τ₀ : ℂ) ∧
          ∀ᶠ τ in 𝓝 τ₀, ∀ (E : FakeEllipticCurve Λ N ℂ) (𝔓 : Place ℂ Fc),
            (pt _ sC E).1 = (𝔐c.pointEquivPlace.symm 𝔓).1 ≫ e𝔐c ≫ CategoryTheory.Limits.pullback.fst πX sC →
            U₀.pt τ = U₀.pt (perE E) → x ∈ 𝔓.toValuationSubring ∧ F (τ : ℂ) = 𝔓.evalAt x)

    (hdisc : ∀ τ τ' : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, ¬ ∃ γ ∈ fuchsianGroup R ι, γ • τ' = z) :
    ∃ V : Fc → UpperHalfPlane → ℂ,

      (∀ (x : Fc) (𝔓 : Place ℂ Fc) (E : FakeEllipticCurve Λ N ℂ),
        (pt _ sC E).1 = (𝔐c.pointEquivPlace.symm 𝔓).1 ≫ e𝔐c ≫ CategoryTheory.Limits.pullback.fst πX sC →
        x ∈ 𝔓.toValuationSubring → ∀ τ : UpperHalfPlane, U₀.pt τ = U₀.pt (perE E) → V x τ = 𝔓.evalAt x) ∧

      (∀ (x : Fc) (𝔓 : Place ℂ Fc) (E : FakeEllipticCurve Λ N ℂ),
      (pt _ sC E).1 = (𝔐c.pointEquivPlace.symm 𝔓).1 ≫ e𝔐c ≫ CategoryTheory.Limits.pullback.fst πX sC →
      ∀ τ : UpperHalfPlane, U₀.pt τ = U₀.pt (perE E) →
        (x ∈ 𝔓.toValuationSubring ↔
          Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : UpperHalfPlane => ‖V x z‖))) ∧

      ((∀ (x : Fc) (τ : UpperHalfPlane), MeromorphicAt (fun z : ℂ => V x (UpperHalfPlane.ofComplex z)) (τ : ℂ)) ∧
      (∀ (x y : Fc) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, V (x + y) z = V x z + V y z) ∧
      (∀ (x y : Fc) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, V (x * y) z = V x z * V y z) ∧
      (∀ (c : ℂ) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, V (algebraMap ℂ Fc c) z = c) ∧
      (∀ x : Fc, ∀ γ ∈ fuchsianGroup R ι, ∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, V x (γ • z) = V x z)) := by
  classical
  obtain ⟨hcls, horb⟩ := hper
  haveI := he𝔐c

  have hrat_all : ∀ v : Place ℂ Fc, v.IsRational := by
    intro v w
    have hdeg : Module.finrank ℂ v.ResidueField = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed v
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : v.ResidueField) one_ne_zero).1 hdeg w
    exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩

  have G4 : ∀ E : FakeEllipticCurve Λ N ℂ, ∃ 𝔓 : Place ℂ Fc, (pt _ sC E).1 = (𝔐c.pointEquivPlace.symm 𝔓).1 ≫ e𝔐c ≫ CategoryTheory.Limits.pullback.fst πX sC := by
    intro E
    let z : Spec (CommRingCat.of ℂ) ⟶ CategoryTheory.Limits.pullback πX sC :=
      CategoryTheory.Limits.pullback.lift (pt _ sC E).1 (𝟙 _) (by rw [Category.id_comp]; exact (pt _ sC E).2)
    let p : {p : Spec (CommRingCat.of ℂ) ⟶ 𝔐c.C // p ≫ 𝔐c.toBase = 𝟙 _} :=
      ⟨z ≫ inv e𝔐c, by rw [Category.assoc, ← he𝔐c_snd, IsIso.inv_hom_id_assoc, CategoryTheory.Limits.pullback.lift_snd]⟩
    refine ⟨𝔐c.pointEquivPlace p, ?_⟩
    rw [Equiv.symm_apply_apply]
    show (pt _ sC E).1 = (z ≫ inv e𝔐c) ≫ e𝔐c ≫ CategoryTheory.Limits.pullback.fst πX sC
    rw [Category.assoc, IsIso.inv_hom_id_assoc, CategoryTheory.Limits.pullback.lift_fst]
  choose plE hplE using G4
  choose Eof hEof using horb

  have hcanon : ∀ (τ : UpperHalfPlane) (E : FakeEllipticCurve Λ N ℂ) (𝔓 : Place ℂ Fc), (pt _ sC E).1 = (𝔐c.pointEquivPlace.symm 𝔓).1 ≫ e𝔐c ≫ CategoryTheory.Limits.pullback.fst πX sC →
      U₀.pt τ = U₀.pt (perE E) → plE (Eof τ) = 𝔓 := by
    intro τ E 𝔓 hl hτ
    have hiso : FakeEllipticCurve.Iso (Eof τ) E := (hcls _ _).2 ((hEof τ).trans hτ)
    have hpt : pt ℂ sC (Eof τ) = pt ℂ sC E := pt_iso ℂ sC _ _ hiso
    have h1 := hplE (Eof τ)
    rw [hpt, hl] at h1
    exact (AlgebraicCurve.CurveModel.place_eq_of_pointEquivPlace_symm_comp_eq 𝔐c πX sC e𝔐c he𝔐c he𝔐c_snd
      _ _ h1).symm
  have hinvar : ∀ τ τ' : UpperHalfPlane, U₀.pt τ = U₀.pt τ' → plE (Eof τ) = plE (Eof τ') :=
    fun τ τ' h => hcanon τ (Eof τ') _ (hplE _) (h.trans (hEof τ').symm)
  have hfib : ∀ z τ' : UpperHalfPlane, plE (Eof z) = plE (Eof τ') → ∃ γ ∈ fuchsianGroup R ι, γ • τ' = z := by
    intro z τ' h
    have h1 := hplE (Eof z)
    have h2 := hplE (Eof τ')
    rw [h] at h1
    have hpt : pt ℂ sC (Eof z) = pt ℂ sC (Eof τ') := Subtype.ext (h1.trans h2.symm)
    have h3 := (hcls _ _).1 (pt_injective ℂ sC _ _ hpt)
    rw [hEof, hEof] at h3
    obtain ⟨γ, hγ, hγz⟩ := (U₀.pt_eq_pt_iff z τ').1 h3
    exact ⟨γ⁻¹, inv_mem hγ, by rw [← hγz, inv_smul_smul]⟩

  have hreg : ∀ (τ₀ : UpperHalfPlane) (x : Fc), ∀ᶠ z in 𝓝[≠] τ₀, x ∈ (plE (Eof z)).toValuationSubring := by
    intro τ₀ x
    rcases eq_or_ne x 0 with rfl | hx
    · exact Filter.Eventually.of_forall fun z => zero_mem _
    obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := ℂ) x hx
    have hfin : ∀ v ∈ D.support, ∀ᶠ z in 𝓝[≠] τ₀, plE (Eof z) ≠ v := by
      intro v hv
      by_cases hvim : ∃ τ' : UpperHalfPlane, plE (Eof τ') = v
      · obtain ⟨τ', rfl⟩ := hvim
        filter_upwards [hdisc τ₀ τ'] with z hz heq
        exact hz (hfib z τ' heq)
      · push Not at hvim
        exact Filter.Eventually.of_forall fun z => hvim z
    have hall : ∀ᶠ z in 𝓝[≠] τ₀, ∀ v ∈ D.support, plE (Eof z) ≠ v :=
      (Filter.eventually_all_finset D.support).2 hfin
    filter_upwards [hall] with z hz
    by_contra hxm
    have hord : (plE (Eof z)).ord x ≠ 0 := fun h0 =>
      hxm ((plE (Eof z)).mem_toValuationSubring_of_ord_nonneg_alt hx h0.ge)
    exact hz (plE (Eof z)) (Finsupp.mem_support_iff.2 (by rw [hD]; exact hord)) rfl

  have hF : ∀ (τ₀ : UpperHalfPlane) (x : Fc), x ∈ (plE (Eof τ₀)).toValuationSubring →
      ∃ F : ℂ → ℂ, AnalyticAt ℂ F (τ₀ : ℂ) ∧
        ∀ᶠ τ in 𝓝 τ₀, x ∈ (plE (Eof τ)).toValuationSubring ∧ F (τ : ℂ) = (plE (Eof τ)).evalAt x := by
    intro τ₀ x hx
    obtain ⟨F, hFa, hev⟩ := hhol τ₀ (Eof τ₀) (plE (Eof τ₀)) (hplE _) (hEof τ₀).symm x hx
    exact ⟨F, hFa, hev.mono fun τ hτ => hτ (Eof τ) (plE (Eof τ)) (hplE _) (hEof τ).symm⟩
  have hrat : ∀ τ : UpperHalfPlane, (plE (Eof τ)).IsRational := fun τ => hrat_all _

  have evalAt_add : ∀ (v : Place ℂ Fc) {f g : Fc}, f ∈ v.toValuationSubring → g ∈ v.toValuationSubring →
      v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
    intro v f g hf hg
    apply v.algebraMap_residueField_injective
    rw [map_add, v.algebraMap_evalAt (hrat_all v) (add_mem hf hg), v.algebraMap_evalAt (hrat_all v) hf,
      v.algebraMap_evalAt (hrat_all v) hg, ← map_add]
    rfl

  refine ⟨fun x τ => (plE (Eof τ)).evalAt x, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x 𝔓 E hl hx τ hτ
    show (plE (Eof τ)).evalAt x = 𝔓.evalAt x
    rw [hcanon τ E 𝔓 hl hτ]
  · intro x 𝔓 E hl τ hτ
    rw [← hcanon τ E 𝔓 hl hτ]
    exact P6aAn.mem_iff_isBoundedUnder (fun τ => plE (Eof τ)) hrat hF hreg x τ
  · exact fun x τ => P6aAn.meromorphicAt_evalAt (fun τ => plE (Eof τ)) hrat hF hreg x τ
  · intro x y τ
    filter_upwards [hreg τ x, hreg τ y] with z hx hy
    exact evalAt_add _ hx hy
  · intro x y τ
    filter_upwards [hreg τ x, hreg τ y] with z hx hy
    exact (plE (Eof z)).evalAt_mul_of_mem (hrat _) hx hy
  · intro c τ
    exact Filter.Eventually.of_forall fun z => (plE (Eof z)).evalAt_algebraMap_eq c
  · intro x γ hγ τ
    refine Filter.Eventually.of_forall fun z => ?_
    show (plE (Eof (γ • z))).evalAt x = (plE (Eof z)).evalAt x
    rw [hinvar (γ • z) z ((U₀.pt_eq_pt_iff _ _).2 ⟨γ⁻¹, inv_mem hγ, inv_smul_smul γ z⟩)]

end S_CerednikDrinfeld_QM_exists_meromorphicRealization_of_periodMap_of_analyticAt_evalAt_of_two_mul_dvd
end P2MW
export P2MW.S_CerednikDrinfeld_QM_exists_meromorphicRealization_of_periodMap_of_analyticAt_evalAt_of_two_mul_dvd (solution)
