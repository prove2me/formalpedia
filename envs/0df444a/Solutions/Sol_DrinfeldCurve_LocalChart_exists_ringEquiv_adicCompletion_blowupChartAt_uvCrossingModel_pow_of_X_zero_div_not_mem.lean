-- Prove2me | solution 1 for DrinfeldCurve.LocalChart.exists_ringEquiv_adicCompletion_blowupChartAt_uvCrossingModel_pow_of_X_zero_div_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/a76ef472-e973-5563-9dd4-293f107e0979

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_AdicCompletion_exists_ringEquiv_of_isLocalization_of_comap_eq_of_comap_eq
import Theorems.Thm_DrinfeldCurve_LocalChart_exists_isMaximal_ringEquiv_adicCompletion_atPrime_uvCrossingModel_pow_of_mem_maximalIdeal
import Theorems.Thm_AdicCompletion_exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal
import Theorems.Thm_DrinfeldCurve_LocalChart_ChartPresentation_mem_nonZeroDivisors_and_flat_of_mem_maximalIdeal
import Definitions.Def_AdicCompletionLocalRing
import Theorems.Thm_ModularCurve_UVCrossingModel_isLocalRing_of_not_isUnit
import Theorems.Thm_ModularCurve_UVCrossingModel_nontrivial_of_not_isUnit
import Theorems.Thm_ModularCurve_UVCrossingModel_V_mem_nonZeroDivisors
import Theorems.Thm_ModularCurve_UVCrossingModel_U_mul_V
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_LocalChart_exists_ringEquiv_adicCompletion_blowupChartAt_uvCrossingModel_pow_of_X_zero_div_not_mem
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply"

set_option autoImplicit false
set_option maxHeartbeats 32000000

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem ChartLocate.isLocalization_away_closure_range_insert_inv
    {A K : Type} [CommRing A] [CommRing K] (φ : A →+* K) (hφ : Function.Injective φ)
    (f : A) (g : K) (hfg : φ f * g = 1)
    (Q : Subring K) (hQ : Q = Subring.closure (Set.range φ ∪ {g}))
    (hφQ : ∀ a : A, φ a ∈ Q) :
    letI : Algebra A ↥Q := (φ.codRestrict Q hφQ).toAlgebra
    IsLocalization (Submonoid.powers f) ↥Q := by
  letI inst : Algebra A ↥Q := (φ.codRestrict Q hφQ).toAlgebra
  show IsLocalization (Submonoid.powers f) ↥Q
  have halg : ∀ a : A, ((algebraMap A ↥Q a : ↥Q) : K) = φ a := fun a => rfl
  have hgQ : g ∈ Q := by rw [hQ]; exact Subring.subset_closure (Or.inr rfl)

  have key : ∀ x : K, x ∈ Q → ∃ (a : A) (k : ℕ), x * (φ f) ^ k = φ a := by
    intro x hx
    rw [hQ] at hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨a, rfl⟩ | hx
      · exact ⟨a, 0, by simp⟩
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨1, 1, by rw [pow_one, mul_comm, hfg, map_one]⟩
    | zero => exact ⟨0, 0, by simp⟩
    | one => exact ⟨1, 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, k, ha⟩ := hx
      obtain ⟨b, l, hb⟩ := hy
      refine ⟨a * f ^ l + b * f ^ k, k + l, ?_⟩
      rw [add_mul, map_add, map_mul, map_mul, map_pow, map_pow, ← ha, ← hb]
      ring
    | neg x _ hx =>
      obtain ⟨a, k, ha⟩ := hx
      exact ⟨-a, k, by rw [neg_mul, ha, map_neg]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, k, ha⟩ := hx
      obtain ⟨b, l, hb⟩ := hy
      refine ⟨a * b, k + l, ?_⟩
      rw [map_mul, ← ha, ← hb]
      ring
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  ·
    rintro ⟨y, hy⟩
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hy
    have hu : IsUnit (algebraMap A ↥Q f) := by
      refine IsUnit.of_mul_eq_one ⟨g, hgQ⟩ ?_
      apply Subtype.ext
      show φ f * g = 1
      exact hfg
    show IsUnit (algebraMap A ↥Q (f ^ k))
    rw [map_pow]
    exact hu.pow k
  ·
    intro z
    obtain ⟨a, k, hak⟩ := key (z : K) z.2
    refine ⟨(a, ⟨f ^ k, (Submonoid.mem_powers_iff _ _).mpr ⟨k, rfl⟩⟩), ?_⟩
    apply Subtype.ext
    show (z : K) * φ (f ^ k) = φ a
    rw [map_pow]
    exact hak
  ·
    intro x y hxy
    refine ⟨1, ?_⟩
    have hφxy : φ x = φ y := by
      have := congrArg (fun t : ↥Q => (t : K)) hxy
      exact this
    simp only [OneMemClass.coe_one, one_mul]
    exact hφ hφxy

theorem ChartLocate.injective_of_isLocalization_away_of_injective
    {R S T : Type} [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    (x : R) [IsLocalization.Away x S] (j : S →+* T) (g : R →+* T)
    (hj : ∀ r : R, j (algebraMap R S r) = g r) (hg : Function.Injective g) (hx : IsUnit (g x)) :
    Function.Injective j := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro z hz
  obtain ⟨⟨r, ⟨y, hy⟩⟩, hzr⟩ := IsLocalization.surj (Submonoid.powers x) z
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hy

  have hr : g r = 0 := by
    have := congrArg j hzr
    rw [map_mul, hz, zero_mul, hj] at this
    exact this.symm
  have hr0 : r = 0 := hg (by rw [hr, map_zero])

  have hzu : z * algebraMap R S (x ^ k) = 0 := by
    have : ((⟨x ^ k, hy⟩ : Submonoid.powers x) : R) = x ^ k := rfl
    rw [this] at hzr
    rw [hzr, hr0, map_zero]
  have hu : IsUnit (algebraMap R S (x ^ k)) :=
    IsLocalization.map_units S (⟨x ^ k, (Submonoid.mem_powers_iff _ _).mpr ⟨k, rfl⟩⟩ : Submonoid.powers x)
  exact (hu.mul_left_eq_zero).mp hzu

theorem ChartLocate.exists_units_eq_mul_U_of_mul_V_eq_const
    {W : Type} [CommRing W] (πe : W) (hπe : πe ∈ nonZeroDivisors W) (ε : Wˣ)
    (z : ModularCurve.UVCrossingModel W πe) (γV : (ModularCurve.UVCrossingModel W πe)ˣ)
    (h : z * ((γV : ModularCurve.UVCrossingModel W πe) * ModularCurve.UVCrossingModel.V πe) =
      ModularCurve.UVCrossingModel.const πe (πe * (ε : W))) :
    ∃ γU : (ModularCurve.UVCrossingModel W πe)ˣ, z = (γU : ModularCurve.UVCrossingModel W πe) * ModularCurve.UVCrossingModel.U πe := by

  have hconst : ∀ a b : W, ModularCurve.UVCrossingModel.const πe (a * b) = ModularCurve.UVCrossingModel.const πe a * ModularCurve.UVCrossingModel.const πe b := by
    intro a b
    rw [← ModularCurve.UVCrossingModel.constHom_apply, ← ModularCurve.UVCrossingModel.constHom_apply, ← ModularCurve.UVCrossingModel.constHom_apply, map_mul]
  have hc : ModularCurve.UVCrossingModel.const πe (πe * (ε : W)) =
      ModularCurve.UVCrossingModel.U πe * ModularCurve.UVCrossingModel.const πe (ε : W) * ModularCurve.UVCrossingModel.V πe := by
    rw [hconst, ← ModularCurve.UVCrossingModel.U_mul_V]; ring

  have hεu : IsUnit (ModularCurve.UVCrossingModel.const πe (ε : W)) := by
    rw [← ModularCurve.UVCrossingModel.constHom_apply]; exact (Units.isUnit ε).map _

  have hV := ModularCurve.UVCrossingModel.V_mem_nonZeroDivisors (W := W) hπe
  have hzγ : z * (γV : ModularCurve.UVCrossingModel W πe) = ModularCurve.UVCrossingModel.U πe * ModularCurve.UVCrossingModel.const πe (ε : W) := by
    have h0 : (z * (γV : ModularCurve.UVCrossingModel W πe) - ModularCurve.UVCrossingModel.U πe * ModularCurve.UVCrossingModel.const πe (ε : W)) * ModularCurve.UVCrossingModel.V πe = 0 := by
      rw [sub_mul, mul_assoc, h, hc, sub_self]
    exact sub_eq_zero.mp ((mul_right_mem_nonZeroDivisors_eq_zero_iff hV).mp h0)

  refine ⟨hεu.unit * γV⁻¹, ?_⟩
  have : z = (z * (γV : ModularCurve.UVCrossingModel W πe)) * ((γV⁻¹ : (ModularCurve.UVCrossingModel W πe)ˣ) : ModularCurve.UVCrossingModel W πe) := by
    rw [mul_assoc, Units.mul_inv, mul_one]
  rw [this, hzγ, Units.val_mul, IsUnit.unit_spec]
  ring

theorem ChartLocate.not_isUnit_ringEquiv_adicCompletion_algebraMap_of_mem_maximalIdeal
    {T M : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [CommRing M] [IsLocalRing M]
    (e : AdicCompletion (IsLocalRing.maximalIdeal T) T ≃+* M) (x : T) (hx : x ∈ IsLocalRing.maximalIdeal T) :
    ¬ IsUnit (e (algebraMap T (AdicCompletion (IsLocalRing.maximalIdeal T) T) x)) := by
  intro hu

  have hu' : IsUnit (algebraMap T (AdicCompletion (IsLocalRing.maximalIdeal T) T) x) := by
    have := hu.map e.symm
    rwa [RingEquiv.symm_apply_apply] at this

  have hmem : algebraMap T (AdicCompletion (IsLocalRing.maximalIdeal T) T) x ∈
      IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal T) T) :=
    AdicCompletion.maximalIdeal_eq_map.ge (Ideal.mem_map_of_mem _ hx)
  exact (IsLocalRing.mem_maximalIdeal _).mp hmem hu'

theorem solution
    (q : ℕ) [Fact q.Prime]
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    (π : O) (hπ : maximalIdeal O = Ideal.span {π})
    (ϖ : O) (hϖ : ϖ ∈ maximalIdeal O) (hϖ0 : ϖ ≠ 0)
    (m : ℕ) (hm : 1 ≤ m) (ε : Oˣ) (hϖπ : ϖ = π ^ m * (ε : O))
    (ϖq : O) (hϖq : ϖq = ϖ ^ (q + 1))
    (f u v : MvPowerSeries (Fin 2) O) (hu : IsUnit u) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q O ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) O), MvPowerSeries.X 1}) ^ (q + 2))
    (hqO : (q : O) ∈ maximalIdeal O)
    (s : MvPowerSeries (Fin 2) O ⧸ Ideal.span {MvPowerSeries.C ϖq * v - f * u})
    (hsnz : s ∈ nonZeroDivisors (MvPowerSeries (Fin 2) O ⧸ Ideal.span {MvPowerSeries.C ϖq * v - f * u}))
    (hs : s ∈ Ideal.span {Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C ϖq * v - f * u}) (MvPowerSeries.C ϖ),
      Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C ϖq * v - f * u}) (MvPowerSeries.X 0),
      Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C ϖq * v - f * u}) (MvPowerSeries.X 1)}) :
    let S := (MvPowerSeries (Fin 2) O ⧸ Ideal.span {MvPowerSeries.C ϖq * v - f * u})
    let mkS : MvPowerSeries (Fin 2) O →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C ϖq * v - f * u})
    let 𝔐 : Ideal S := Ideal.span {mkS (MvPowerSeries.C ϖ), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}
    let Ls := Localization.Away s
    let Rs : Subring Ls := Subring.closure
      (Set.range (algebraMap S Ls) ∪ {x : Ls | ∃ i ∈ 𝔐, x * algebraMap S Ls s = algebraMap S Ls i})
    ∀ (P' : Ideal ↥Rs) (hP' : P'.IsMaximal)

      (hover : ∀ (i : S) (hi : algebraMap S Ls i ∈ Rs),
        i ∈ Ideal.span {mkS (MvPowerSeries.C π), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} → (⟨_, hi⟩ : ↥Rs) ∈ P')

      (hoff : ∀ (x : Ls) (hx : x ∈ Rs), x * algebraMap S Ls s = algebraMap S Ls (mkS (MvPowerSeries.C ϖ)) → (⟨x, hx⟩ : ↥Rs) ∈ P'),
      ∀ (n : ℕ)
        (hchart : ∀ (t : Ls) (ht : t ∈ Rs), t * algebraMap S Ls s = algebraMap S Ls (mkS (MvPowerSeries.X 0)) → (⟨t, ht⟩ : ↥Rs) ∉ P')
        (hslope : ∀ (t t' : Ls) (ht : t ∈ Rs) (ht' : t' ∈ Rs),
          t * algebraMap S Ls s = algebraMap S Ls (mkS (MvPowerSeries.X 0)) →
          t' * algebraMap S Ls s = algebraMap S Ls (mkS (MvPowerSeries.X 1)) →
          (⟨t', ht'⟩ : ↥Rs) - ((n : ℕ) : ↥Rs) * ⟨t, ht⟩ ∈ P'),
    ∃ (hSR : ∀ i : S, algebraMap S Ls i ∈ Rs)
      (ι : AdicCompletion P' ↥Rs ≃+* UVCrossingModel O (π ^ m)),

      (∀ o : O, ι (algebraMap ↥Rs (AdicCompletion P' ↥Rs) ⟨_, hSR (mkS (MvPowerSeries.C o))⟩) = const (π ^ m) o) ∧

      (∃ (p₀ p₁ : O) (α β : UVCrossingModel O (π ^ m)),
        (p₀ ∉ maximalIdeal O ∨ p₁ ∉ maximalIdeal O) ∧ (p₀ ^ q * p₁ - p₀ * p₁ ^ q ∈ maximalIdeal O) ∧
        ¬ IsUnit (α - const (π ^ m) p₀) ∧ ¬ IsUnit (β - const (π ^ m) p₁) ∧
        ι (algebraMap ↥Rs (AdicCompletion P' ↥Rs) ⟨_, hSR (mkS (MvPowerSeries.X 0))⟩) = V (π ^ m) * α ∧
        ι (algebraMap ↥Rs (AdicCompletion P' ↥Rs) ⟨_, hSR (mkS (MvPowerSeries.X 1))⟩) = V (π ^ m) * β) ∧

      (∃ γV : (UVCrossingModel O (π ^ m))ˣ,
        ι (algebraMap ↥Rs (AdicCompletion P' ↥Rs) ⟨_, hSR s⟩) = (γV : UVCrossingModel O (π ^ m)) * V (π ^ m)) ∧
      (∀ (x : Ls) (hx : x ∈ Rs), x * algebraMap S Ls s = algebraMap S Ls (mkS (MvPowerSeries.C ϖ)) →
        ∃ γU : (UVCrossingModel O (π ^ m))ˣ,
          ι (algebraMap ↥Rs (AdicCompletion P' ↥Rs) ⟨x, hx⟩) = (γU : UVCrossingModel O (π ^ m)) * U (π ^ m))  := by
  intro S mkS 𝔐 Ls Rs P' hP' hover hoff n hchart hslope
  subst hϖq
  classical
  haveI := hP'

  let pr : DrinfeldCurve.LocalChart.ChartPresentation q O ϖ := ⟨f, u, v, hu, hv, hf⟩
  have hSpr : pr.Ring = S := rfl
  obtain ⟨hCnzd, -, hX0nzd, hX1nzd⟩ :=
    DrinfeldCurve.LocalChart.ChartPresentation.mem_nonZeroDivisors_and_flat_of_mem_maximalIdeal q O ϖ hϖ hϖ0 pr
  have hX0nzd' : mkS (MvPowerSeries.X 0) ∈ nonZeroDivisors S := hX0nzd

  have ha : ((n : ℕ) : O) ^ q - (n : O) ∈ maximalIdeal O := by
    have hdvd : (q : ℤ) ∣ (n : ℤ) ^ q - n := by
      haveI := Fact.out (p := q.Prime)
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.pow_card, sub_self]
    obtain ⟨t, ht⟩ := hdvd
    have : ((n : ℕ) : O) ^ q - (n : O) = (q : O) * (t : O) := by
      have := congrArg (Int.cast : ℤ → O) ht
      push_cast at this
      exact this
    rw [this]; exact Ideal.mul_mem_right _ _ hqO

  obtain ⟨hι₀, hx, hy, hw, 𝔪a, h𝔪amax, h𝔪aspan, hxy, hnoeth, hmaxloc, hwn, hres, ι5, hι5c, ⟨γ, hγ, hι5x⟩, hι5y⟩ :=
    DrinfeldCurve.LocalChart.exists_isMaximal_ringEquiv_adicCompletion_atPrime_uvCrossingModel_pow_of_mem_maximalIdeal
      q O π hπ ϖ hϖ hϖ0 m hm ε hϖπ pr hX0nzd hqO (n : O) ha

  have hSR : ∀ i : S, algebraMap S Ls i ∈ Rs := fun i => Subring.subset_closure (Or.inl ⟨i, rfl⟩)
  have hts : ∀ i : S, (algebraMap S Ls i * IsLocalization.Away.invSelf s) * algebraMap S Ls s = algebraMap S Ls i := by
    intro i; rw [mul_assoc, mul_comm (IsLocalization.Away.invSelf s), IsLocalization.Away.mul_invSelf, mul_one]
  have h𝔐s : ∀ i : S, i ∈ 𝔐 → algebraMap S Ls i * IsLocalization.Away.invSelf s ∈ Rs :=
    fun i hi => Subring.subset_closure (Or.inr ⟨i, hi, hts i⟩)
  have hX0𝔐 : mkS (MvPowerSeries.X 0) ∈ 𝔐 := Ideal.subset_span (by simp)
  have hX1𝔐 : mkS (MvPowerSeries.X 1) ∈ 𝔐 := Ideal.subset_span (by simp)
  have hϖ𝔐 : mkS (MvPowerSeries.C ϖ) ∈ 𝔐 := Ideal.subset_span (by simp)
  have ht₀R : (algebraMap S Ls (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf s) ∈ Rs := h𝔐s _ hX0𝔐
  have ht₁R : (algebraMap S Ls (mkS (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf s) ∈ Rs := h𝔐s _ hX1𝔐
  have htϖR : (algebraMap S Ls (mkS (MvPowerSeries.C ϖ)) * IsLocalization.Away.invSelf s) ∈ Rs := h𝔐s _ hϖ𝔐
  have ht₀P : (⟨(algebraMap S Ls (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf s), ht₀R⟩ : ↥Rs) ∉ P' := hchart _ ht₀R (hts _)
  have ht₁P : (⟨(algebraMap S Ls (mkS (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf s), ht₁R⟩ : ↥Rs) - ((n : ℕ) : ↥Rs) * ⟨(algebraMap S Ls (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf s), ht₀R⟩ ∈ P' := hslope _ _ ht₀R ht₁R (hts _) (hts _)
  have htϖP : (⟨(algebraMap S Ls (mkS (MvPowerSeries.C ϖ)) * IsLocalization.Away.invSelf s), htϖR⟩ : ↥Rs) ∈ P' := hoff _ htϖR (hts _)

  let L2 : Type := Localization.Away (algebraMap S Ls (mkS (MvPowerSeries.X 0)))
  have hX0nzdLs : algebraMap S Ls (mkS (MvPowerSeries.X 0)) ∈ nonZeroDivisors Ls :=
    IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers s) Ls hX0nzd'
  have hinj2 : Function.Injective (algebraMap Ls L2) :=
    IsLocalization.injective (M := Submonoid.powers (algebraMap S Ls (mkS (MvPowerSeries.X 0)))) (S := L2)
      (Submonoid.powers_le.mpr hX0nzdLs)
  have halg2 : ∀ i : S, algebraMap Ls L2 (algebraMap S Ls i) = algebraMap S L2 i :=
    fun i => (IsScalarTower.algebraMap_apply S Ls L2 i).symm
  have hsX0unit : IsUnit (algebraMap S L2 (s * mkS (MvPowerSeries.X 0))) :=
    IsLocalization.Away.algebraMap_isUnit (s * mkS (MvPowerSeries.X 0))
  have hX0unit2 : IsUnit (algebraMap S L2 (mkS (MvPowerSeries.X 0))) := by
    have := hsX0unit; rw [map_mul] at this; exact isUnit_of_mul_isUnit_right this
  have hsunit2 : IsUnit (algebraMap S L2 s) := by
    have := hsX0unit; rw [map_mul] at this; exact isUnit_of_mul_isUnit_left this
  obtain ⟨jL0, hjL0⟩ : ∃ j : (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) →+* L2, ∀ i : S, j ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) i) = algebraMap S L2 i :=
    by
      let g2 : pr.Ring →+* L2 := algebraMap S L2
      have hg2 : IsUnit (g2 ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) := hX0unit2
      exact ⟨IsLocalization.Away.lift ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)) hg2,
        fun i => IsLocalization.Away.lift_eq ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)) hg2 i⟩

  obtain ⟨a, z, hz, hsz⟩ := Ideal.mem_span_insert.mp hs
  obtain ⟨b, z', hz', hzz⟩ := Ideal.mem_span_insert.mp hz
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hz'
  have hsabc : s = a * mkS (MvPowerSeries.C ϖ) + b * mkS (MvPowerSeries.X 0) + c * mkS (MvPowerSeries.X 1) := by
    rw [hsz, hzz, ← hc]; ring
  have hι₀R : ∀ i : S, (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) i ∈ (Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))})) := fun i => Subring.subset_closure (Or.inl ⟨i, rfl⟩)
  have hσR : (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) ∈ (Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))})) :=
    add_mem (add_mem (mul_mem (hι₀R a) hx) (hι₀R b)) (mul_mem (hι₀R c) hw)
  have hxy' : (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) = (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) (mkS (MvPowerSeries.C ϖ)) := hxy
  have hmkp : ∀ F : MvPowerSeries (Fin 2) O, (Ideal.Quotient.mk (Ideal.span {pr.rel})) F = mkS F := fun _ => rfl
  have hy0S : ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) = (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) (mkS (MvPowerSeries.X 0)) := rfl
  have hwy' : ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) = (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) (mkS (MvPowerSeries.X 1)) := by
    rw [mul_assoc, mul_comm (IsLocalization.Away.invSelf _), IsLocalization.Away.mul_invSelf, mul_one]
    rfl
  have hdecomp : ∀ (a' b' c' : pr.Ring),
      (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) (a' * (Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.C ϖ) + b' * (Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0) + c' * (Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) =
        ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a' * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b' + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c' * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) := by
    intro a' b' c'
    have : ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a' * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b' + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c' * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) =
        (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a' * ((((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b' * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c' * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) := by ring
    rw [this, hxy', hwy', map_add, map_add, map_mul, map_mul, map_mul]
    rfl
  have hsσ : (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) s = ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) := by
    rw [hsabc]; exact hdecomp a b c

  have hX0_2 : jL0 ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) = algebraMap S L2 (mkS (MvPowerSeries.X 0)) := hjL0 _
  have hu_s : algebraMap Ls L2 (algebraMap S Ls (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf s) * algebraMap S L2 s = algebraMap S L2 (mkS (MvPowerSeries.X 0)) := by
    rw [← halg2 s, ← map_mul, hts, halg2]
  have hv_X0 : jL0 ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) * algebraMap S L2 (mkS (MvPowerSeries.X 0)) =
      algebraMap S L2 s := by
    rw [← hX0_2, ← map_mul, ← hsσ, hjL0]
  have huv : algebraMap Ls L2 (algebraMap S Ls (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf s) * jL0 ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) = 1 := by
    apply (hsunit2.mul hX0unit2).mul_right_cancel
    rw [one_mul]
    calc algebraMap Ls L2 (algebraMap S Ls (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf s) * jL0 ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) *
          (algebraMap S L2 s * algebraMap S L2 (mkS (MvPowerSeries.X 0)))
        = (algebraMap Ls L2 (algebraMap S Ls (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf s) * algebraMap S L2 s) *
          (jL0 ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) * algebraMap S L2 (mkS (MvPowerSeries.X 0))) := by ring
      _ = algebraMap S L2 (mkS (MvPowerSeries.X 0)) * algebraMap S L2 s := by rw [hu_s, hv_X0]
      _ = algebraMap S L2 s * algebraMap S L2 (mkS (MvPowerSeries.X 0)) := mul_comm _ _

  have hchartId : ∀ (t : Ls) (a' b' c' : S),
      t * algebraMap S Ls s = algebraMap S Ls (a' * mkS (MvPowerSeries.C ϖ) + b' * mkS (MvPowerSeries.X 0) + c' * mkS (MvPowerSeries.X 1)) →
      algebraMap Ls L2 t * jL0 ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) =
        jL0 ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a' * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b' + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c' * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) := by
    intro t a' b' c' ht
    apply hX0unit2.mul_right_cancel
    rw [mul_assoc, hv_X0, ← halg2 s, ← map_mul, ht, halg2, ← hjL0,
      show (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) (a' * mkS (MvPowerSeries.C ϖ) + b' * mkS (MvPowerSeries.X 0) + c' * mkS (MvPowerSeries.X 1)) = _ from hdecomp a' b' c',
      map_mul, hX0_2]
  have hx0_2 : jL0 (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) = algebraMap Ls L2 (algebraMap S Ls (mkS (MvPowerSeries.C ϖ)) * IsLocalization.Away.invSelf s) * jL0 ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) := by
    have h1 := hchartId (algebraMap S Ls (mkS (MvPowerSeries.C ϖ)) * IsLocalization.Away.invSelf s) 1 0 0 (by rw [hts]; congr 1; ring)
    rw [h1, show (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) (1 : S) = 1 from map_one _, show (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) (0 : S) = 0 from map_zero _]
    congr 1; ring
  have hw0_2 : jL0 ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) = algebraMap Ls L2 (algebraMap S Ls (mkS (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf s) * jL0 ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) := by
    have h1 := hchartId (algebraMap S Ls (mkS (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf s) 0 0 1 (by rw [hts]; congr 1; ring)
    rw [h1, show (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) (1 : S) = 1 from map_one _, show (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) (0 : S) = 0 from map_zero _]
    congr 1; ring

  have hinjS : Function.Injective (algebraMap S Ls) :=
    IsLocalization.injective (M := Submonoid.powers s) (S := Ls) (Submonoid.powers_le.mpr hsnz)
  have hinjS2 : Function.Injective (algebraMap S L2) := by
    intro i i' h; apply hinjS; apply hinj2; rw [halg2, halg2]; exact h
  have hinjL0 : Function.Injective jL0 := by
    let g2 : pr.Ring →+* L2 := algebraMap S L2
    exact ChartLocate.injective_of_isLocalization_away_of_injective ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)) jL0 g2 hjL0 hinjS2 hX0unit2

  let φA : ↥Rs →+* L2 := (algebraMap Ls L2).comp Rs.subtype
  let φB : ↥(Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))})) →+* L2 := jL0.comp ((Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))}))).subtype
  have hφA : Function.Injective φA := hinj2.comp Subtype.val_injective
  have hφB : Function.Injective φB := hinjL0.comp Subtype.val_injective
  let Q : Subring L2 := Subring.closure (Set.range φA ∪ {(jL0 ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))))})
  have hφAQ : ∀ r : ↥Rs, φA r ∈ Q := fun r => Subring.subset_closure (Or.inl ⟨r, rfl⟩)
  have hvQ : (jL0 ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))))) ∈ Q := Subring.subset_closure (Or.inr rfl)
  have huQ : (algebraMap Ls L2 (algebraMap S Ls (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf s)) ∈ Q := hφAQ ⟨(algebraMap S Ls (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf s), ht₀R⟩

  have hR0Q : ∀ r : ↥(Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))})), φB r ∈ Q := by
    intro r
    have : (Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))})) ≤ Q.comap jL0 := by
      refine Subring.closure_le.mpr ?_
      rintro z hz
      rcases hz with ⟨i, rfl⟩ | hz
      · show jL0 ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) i) ∈ Q
        rw [hjL0, ← halg2]; exact hφAQ ⟨_, hSR i⟩
      · rcases hz with rfl | rfl
        · show jL0 (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) ∈ Q
          rw [hx0_2]; exact mul_mem (hφAQ ⟨_, htϖR⟩) hvQ
        · show jL0 ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) ∈ Q
          rw [hw0_2]; exact mul_mem (hφAQ ⟨_, ht₁R⟩) hvQ
    exact this r.2

  have hRsQ' : ∀ r : ↥Rs, φA r ∈ Subring.closure (Set.range φB ∪ {(algebraMap Ls L2 (algebraMap S Ls (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf s))}) := by
    intro r
    have : Rs ≤ (Subring.closure (Set.range φB ∪ {(algebraMap Ls L2 (algebraMap S Ls (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf s))})).comap (algebraMap Ls L2) := by
      refine Subring.closure_le.mpr ?_
      rintro t ht
      rcases ht with ⟨i, rfl⟩ | ⟨i, hi, hti⟩
      · show algebraMap Ls L2 (algebraMap S Ls i) ∈ Subring.closure (Set.range φB ∪ {(algebraMap Ls L2 (algebraMap S Ls (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf s))})
        rw [halg2, ← hjL0]; exact Subring.subset_closure (Or.inl ⟨⟨_, hι₀R i⟩, rfl⟩)
      · show algebraMap Ls L2 t ∈ Subring.closure (Set.range φB ∪ {(algebraMap Ls L2 (algebraMap S Ls (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf s))})
        obtain ⟨a', z1, hz1, hiz⟩ := Ideal.mem_span_insert.mp hi
        obtain ⟨b', z2, hz2, hzz2⟩ := Ideal.mem_span_insert.mp hz1
        obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp hz2
        have hi' : i = a' * mkS (MvPowerSeries.C ϖ) + b' * mkS (MvPowerSeries.X 0) + c' * mkS (MvPowerSeries.X 1) := by
          rw [hiz, hzz2, ← hc']; ring
        have h1 := hchartId t a' b' c' (by rw [hti, hi'])
        have h2 : algebraMap Ls L2 t = jL0 ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a' * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b' + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c' * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) * (algebraMap Ls L2 (algebraMap S Ls (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf s)) := by
          rw [← h1, mul_assoc, mul_comm (jL0 _), huv, mul_one]
        rw [h2]
        refine mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, ?_⟩, rfl⟩)) (Subring.subset_closure (Or.inr rfl))
        exact add_mem (add_mem (mul_mem (hι₀R a') hx) (hι₀R b')) (mul_mem (hι₀R c') hw)
    exact this r.2
  have hQeq : Q = Subring.closure (Set.range φB ∪ {(algebraMap Ls L2 (algebraMap S Ls (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf s))}) := by
    apply le_antisymm
    · refine Subring.closure_le.mpr ?_
      rintro z hz
      rcases hz with ⟨r, rfl⟩ | rfl
      · exact hRsQ' r
      · exact Subring.subset_closure (Or.inl ⟨⟨_, hσR⟩, rfl⟩)
    · refine Subring.closure_le.mpr ?_
      rintro z hz
      rcases hz with ⟨r, rfl⟩ | rfl
      · exact hR0Q r
      · exact huQ
  have hφBQ : ∀ r : ↥(Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))})), φB r ∈ Q := hR0Q
  letI algA : Algebra ↥Rs ↥Q := (φA.codRestrict Q hφAQ).toAlgebra
  letI algB : Algebra ↥(Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))})) ↥Q := (φB.codRestrict Q hφBQ).toAlgebra
  haveI locA : IsLocalization (Submonoid.powers (⟨(algebraMap S Ls (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf s), ht₀R⟩ : ↥Rs)) ↥Q :=
    ChartLocate.isLocalization_away_closure_range_insert_inv φA hφA ⟨(algebraMap S Ls (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf s), ht₀R⟩ (jL0 ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))))) huv Q rfl hφAQ
  haveI locB : IsLocalization (Submonoid.powers (⟨((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))), hσR⟩ : ↥(Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))})))) ↥Q :=
    ChartLocate.isLocalization_away_closure_range_insert_inv φB hφB ⟨((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))), hσR⟩ (algebraMap Ls L2 (algebraMap S Ls (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf s))
      (by rw [mul_comm]; exact huv) Q hQeq hφBQ

  have hdisj : Disjoint (↑(Submonoid.powers (⟨(algebraMap S Ls (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf s), ht₀R⟩ : ↥Rs)) : Set ↥Rs) ↑P' :=
    (Ideal.disjoint_powers_iff_notMem (⟨(algebraMap S Ls (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf s), ht₀R⟩ : ↥Rs) hP'.isPrime.isRadical).mpr ht₀P
  let 𝔔 : Ideal ↥Q := Ideal.map (algebraMap ↥Rs ↥Q) P'
  haveI h𝔔p : 𝔔.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (⟨(algebraMap S Ls (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf s), ht₀R⟩ : ↥Rs)) ↥Q P' hP'.isPrime hdisj
  have h𝔔A : 𝔔.comap (algebraMap ↥Rs ↥Q) = P' :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers (⟨(algebraMap S Ls (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf s), ht₀R⟩ : ↥Rs)) ↥Q hP'.isPrime hdisj

  have hgenQ : ∀ (g : ↥(Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))}))) (p : ↥Rs), φB g = φA p * (jL0 ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))))) → p ∈ P' → algebraMap ↥(Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))})) ↥Q g ∈ 𝔔 := by
    intro g p hgp hp
    have : algebraMap ↥(Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))})) ↥Q g = algebraMap ↥Rs ↥Q p * ⟨(jL0 ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))))), hvQ⟩ := Subtype.ext hgp
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hp)
  have hgenQ' : ∀ (g : ↥(Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))}))) (p : ↥Rs), φB g = φA p → p ∈ P' → algebraMap ↥(Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))})) ↥Q g ∈ 𝔔 := by
    intro g p hgp hp
    have : algebraMap ↥(Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))})) ↥Q g = algebraMap ↥Rs ↥Q p := Subtype.ext hgp
    rw [this]
    exact Ideal.mem_map_of_mem _ hp
  have hoverS : ∀ F : MvPowerSeries (Fin 2) O,
      mkS F ∈ Ideal.span {mkS (MvPowerSeries.C π), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} →
      (⟨algebraMap S Ls (mkS F), hSR _⟩ : ↥Rs) ∈ P' := fun F hF => hover _ (hSR _) hF
  have hπP : (⟨algebraMap S Ls (mkS (MvPowerSeries.C π)), hSR _⟩ : ↥Rs) ∈ P' := hoverS _ (Ideal.subset_span (by simp))
  have hX0P : (⟨algebraMap S Ls (mkS (MvPowerSeries.X 0)), hSR _⟩ : ↥Rs) ∈ P' := hoverS _ (Ideal.subset_span (by simp))
  have hφAB : ∀ i : S, φB ⟨(algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) i, hι₀R i⟩ = φA ⟨algebraMap S Ls i, hSR i⟩ := by
    intro i; show jL0 ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) i) = algebraMap Ls L2 (algebraMap S Ls i); rw [hjL0, halg2]
  have hnat2 : φA ((n : ℕ) : ↥Rs) = ((n : ℕ) : L2) := map_natCast φA n
  have hnatB : φB ⟨((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) (n : O), hι₀ (n : O)⟩ = ((n : ℕ) : L2) := by
    have := hφAB (mkS (MvPowerSeries.C ((n : ℕ) : O)))
    rw [show (⟨algebraMap S Ls (mkS (MvPowerSeries.C ((n : ℕ) : O))), hSR _⟩ : ↥Rs) = ((n : ℕ) : ↥Rs) from
      Subtype.ext (by simp only [map_natCast]; rfl)] at this
    rw [hnat2] at this
    exact this
  have hle𝔪a : 𝔪a ≤ 𝔔.comap (algebraMap ↥(Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))})) ↥Q) := by
    rw [h𝔪aspan]
    refine Ideal.span_le.mpr ?_
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rw [SetLike.mem_coe, Ideal.mem_comap]
    rcases hg with rfl | rfl | rfl | rfl
    · exact hgenQ' _ _ (hφAB _) hπP
    · exact hgenQ' _ _ (hφAB _) hX0P
    · exact hgenQ _ ⟨(algebraMap S Ls (mkS (MvPowerSeries.C ϖ)) * IsLocalization.Away.invSelf s), htϖR⟩ hx0_2 htϖP
    · refine hgenQ _ _ ?_ ht₁P
      show jL0 (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) - ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) (n : O)) = φA (⟨(algebraMap S Ls (mkS (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf s), ht₁R⟩ - ((n : ℕ) : ↥Rs) * ⟨(algebraMap S Ls (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf s), ht₀R⟩) * (jL0 ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))))
      rw [map_sub jL0, hw0_2, map_sub φA, map_mul φA, hnat2, sub_mul,
        show jL0 (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) (n : O)) = ((n : ℕ) : L2) from hnatB]
      congr 1
      show ((n : ℕ) : L2) = (n : L2) * (algebraMap Ls L2 (algebraMap S Ls (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf s)) * (jL0 ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))))
      rw [mul_assoc, huv, mul_one]
  have h𝔔B : 𝔔.comap (algebraMap ↥(Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))})) ↥Q) = 𝔪a :=
    (h𝔪amax.eq_of_le (Ideal.comap_ne_top _ h𝔔p.ne_top) hle𝔪a).symm

  haveI := h𝔪amax
  obtain ⟨T1, hT1⟩ := AdicCompletion.exists_ringEquiv_of_isLocalization_of_comap_eq_of_comap_eq
    (Submonoid.powers (⟨(algebraMap S Ls (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf s), ht₀R⟩ : ↥Rs)) (Submonoid.powers (⟨((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))), hσR⟩ : ↥(Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))})))) P' 𝔪a 𝔔 h𝔔A h𝔔B
  obtain ⟨T2, hT2⟩ := AdicCompletion.exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal (S := (Localization.AtPrime 𝔪a)) 𝔪a
  haveI : IsNoetherianRing (Localization.AtPrime 𝔪a) := hnoeth
  have hπm0 : π ≠ 0 := by
    intro h0; apply hϖ0
    have : ϖ ∈ Ideal.span {π} := hπ ▸ hϖ
    rw [h0, Ideal.span_singleton_eq_bot.mpr rfl] at this
    exact this
  have hπmnu : ¬ IsUnit (π ^ m) := by
    intro hu
    have hπu : IsUnit π := (isUnit_pow_iff (by omega)).mp hu
    have : π ∈ maximalIdeal O := hπ ▸ Ideal.mem_span_singleton_self π
    exact (IsLocalRing.mem_maximalIdeal _).mp this hπu
  haveI : IsLocalRing (UVCrossingModel O (π ^ m)) := ModularCurve.UVCrossingModel.isLocalRing_of_not_isUnit hπmnu
  haveI : Nontrivial (UVCrossingModel O (π ^ m)) := ModularCurve.UVCrossingModel.nontrivial_of_not_isUnit hπmnu
  let ι : AdicCompletion P' ↥Rs ≃+* (UVCrossingModel O (π ^ m)) := T1.trans (T2.trans ι5)
  have hιval : ∀ (r : ↥Rs) (g : ↥(Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))}))), φA r = φB g →
      ι (algebraMap ↥Rs (AdicCompletion P' ↥Rs) r) = ι5 (algebraMap (Localization.AtPrime 𝔪a) (AdicCompletion (maximalIdeal (Localization.AtPrime 𝔪a)) (Localization.AtPrime 𝔪a)) (algebraMap ↥(Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))})) (Localization.AtPrime 𝔪a) g)) := by
    intro r g h
    have hq : algebraMap ↥Rs ↥Q r = algebraMap ↥(Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))})) ↥Q g := Subtype.ext h
    have e1 := hT1 r g hq
    have e2 := hT2 g
    exact (congrArg (fun z => ι5 (T2 z)) e1).trans (congrArg ι5 e2)
  have hπmnzd : π ^ m ∈ nonZeroDivisors O := pow_mem (mem_nonZeroDivisors_of_ne_zero hπm0) m

  let G : ↥(Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))})) →+* (UVCrossingModel O (π ^ m)) := ι5.toRingHom.comp ((algebraMap (Localization.AtPrime 𝔪a) (AdicCompletion (maximalIdeal (Localization.AtPrime 𝔪a)) (Localization.AtPrime 𝔪a))).comp (algebraMap ↥(Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))})) (Localization.AtPrime 𝔪a)))
  let ιR : ↥Rs →+* (UVCrossingModel O (π ^ m)) := ι.toRingHom.comp (algebraMap ↥Rs (AdicCompletion P' ↥Rs))
  have hιG : ∀ (r : ↥Rs) (g : ↥(Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))}))), φA r = φB g → ιR r = G g := fun r g h => hιval r g h
  have hGy : G ⟨((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), hy⟩ = V (π ^ m) := hι5y
  have hGc : ∀ o : O, G ⟨((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) o, hι₀ o⟩ = const (π ^ m) o := fun o => hι5c o

  have hconst : ∀ o : O, ιR ⟨algebraMap S Ls (mkS (MvPowerSeries.C o)), hSR _⟩ = const (π ^ m) o :=
    fun o => (hιG ⟨algebraMap S Ls (mkS (MvPowerSeries.C o)), hSR _⟩ ⟨((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) o, hι₀ o⟩ (hφAB (mkS (MvPowerSeries.C o))).symm).trans (hGc o)

  have hp0 : (1 : O) ∉ maximalIdeal O ∨ ((n : ℕ) : O) ∉ maximalIdeal O :=
    Or.inl (fun h => (maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h))
  have harith : (1 : O) ^ q * ((n : ℕ) : O) - 1 * ((n : ℕ) : O) ^ q ∈ maximalIdeal O := by
    have e : (1 : O) ^ q * ((n : ℕ) : O) - 1 * ((n : ℕ) : O) ^ q = -(((n : ℕ) : O) ^ q - (n : O)) := by ring
    rw [e]; exact neg_mem ha
  have h11 : ¬ IsUnit ((1 : (UVCrossingModel O (π ^ m))) - const (π ^ m) (1 : O)) := by
    have h0 : (1 : (UVCrossingModel O (π ^ m))) - const (π ^ m) (1 : O) = 0 := by
      rw [show const (π ^ m) (1 : O) = 1 from map_one (constHom (π ^ m))]; exact sub_self _
    exact fun hu => not_isUnit_zero (h0 ▸ hu)
  have hβ : ¬ IsUnit (G ⟨((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), hw⟩ - const (π ^ m) ((n : ℕ) : O)) := by
    have e : G (⟨((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), hw⟩ - ⟨((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ((n : ℕ) : O), hι₀ ((n : ℕ) : O)⟩) = G ⟨((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), hw⟩ - const (π ^ m) ((n : ℕ) : O) :=
      (map_sub G _ _).trans (congrArg (fun z => G ⟨((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), hw⟩ - z) (hGc ((n : ℕ) : O)))
    intro hu
    exact ChartLocate.not_isUnit_ringEquiv_adicCompletion_algebraMap_of_mem_maximalIdeal ι5 _ hwn (e ▸ hu)
  have hX0 : ιR ⟨algebraMap S Ls (mkS (MvPowerSeries.X 0)), hSR _⟩ = V (π ^ m) * 1 :=
    ((hιG ⟨algebraMap S Ls (mkS (MvPowerSeries.X 0)), hSR _⟩ ⟨((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), hy⟩ (hφAB (mkS (MvPowerSeries.X 0))).symm).trans hGy).trans (mul_one _).symm
  have hbX1 : (⟨(algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) (mkS (MvPowerSeries.X 1)), hι₀R _⟩ : ↥(Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))}))) = ⟨((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), hw⟩ * ⟨((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), hy⟩ := Subtype.ext hwy'.symm
  have hX1 : ιR ⟨algebraMap S Ls (mkS (MvPowerSeries.X 1)), hSR _⟩ = V (π ^ m) * G ⟨((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), hw⟩ :=
    (hιG ⟨algebraMap S Ls (mkS (MvPowerSeries.X 1)), hSR _⟩ ⟨(algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) (mkS (MvPowerSeries.X 1)), hι₀R _⟩ (hφAB (mkS (MvPowerSeries.X 1))).symm).trans
      (((congrArg G hbX1).trans (map_mul G _ _)).trans ((congrArg (fun z => G ⟨((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), hw⟩ * z) hGy).trans (mul_comm _ _)))

  have hσP : (⟨((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))), hσR⟩ : ↥(Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))}))) ∉ 𝔪a := by
    intro hmem
    have h1 : algebraMap ↥(Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))})) ↥Q ⟨((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))), hσR⟩ ∈ 𝔔 := by rw [← h𝔔B] at hmem; exact hmem
    have h2 : algebraMap ↥Rs ↥Q ⟨(algebraMap S Ls (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf s), ht₀R⟩ * algebraMap ↥(Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))})) ↥Q ⟨((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))), hσR⟩ = 1 := Subtype.ext huv
    exact h𝔔p.ne_top ((Ideal.eq_top_iff_one _).mpr (h2 ▸ Ideal.mul_mem_left _ _ h1))
  have hσu : IsUnit (algebraMap ↥(Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))})) (Localization.AtPrime 𝔪a) ⟨((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))), hσR⟩) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime 𝔪a) 𝔪a _).mpr hσP
  have hσu' : IsUnit (G ⟨((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))), hσR⟩) := (hσu.map (algebraMap (Localization.AtPrime 𝔪a) (AdicCompletion (maximalIdeal (Localization.AtPrime 𝔪a)) (Localization.AtPrime 𝔪a)))).map ι5.toRingHom
  have hbs : (⟨(algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) s, hι₀R s⟩ : ↥(Subring.closure (Set.range (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ∪ {(((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))}))) = ⟨((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))), hσR⟩ * ⟨((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), hy⟩ := Subtype.ext hsσ
  have hsclause : ιR ⟨algebraMap S Ls s, hSR s⟩ = (hσu'.unit : (UVCrossingModel O (π ^ m))) * V (π ^ m) :=
    (hιG ⟨algebraMap S Ls s, hSR s⟩ ⟨(algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) s, hι₀R s⟩ (hφAB s).symm).trans
      (((congrArg G hbs).trans (map_mul G _ _)).trans
        ((congrArg (fun z => G ⟨((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) a * (((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))).comp ((Ideal.Quotient.mk (Ideal.span {pr.rel})).comp MvPowerSeries.C)) ϖ * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))) + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) b + (algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) c * ((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))), hσR⟩ * z) hGy).trans (congrArg (fun z => z * V (π ^ m)) hσu'.unit_spec.symm)))

  have hconstϖ : ιR ⟨algebraMap S Ls (mkS (MvPowerSeries.C ϖ)), hSR _⟩ = const (π ^ m) (π ^ m * (ε : O)) :=
    (hconst ϖ).trans (congrArg (const (π ^ m)) hϖπ)
  have hlast : ∀ (x : Ls) (hx : x ∈ Rs), x * algebraMap S Ls s = algebraMap S Ls (mkS (MvPowerSeries.C ϖ)) →
      ∃ γU : ((UVCrossingModel O (π ^ m)))ˣ, ιR ⟨x, hx⟩ = (γU : (UVCrossingModel O (π ^ m))) * U (π ^ m) := by
    intro x' hx' hxs
    have e1 : (⟨x', hx'⟩ : ↥Rs) * ⟨algebraMap S Ls s, hSR s⟩ = ⟨algebraMap S Ls (mkS (MvPowerSeries.C ϖ)), hSR _⟩ :=
      Subtype.ext hxs
    have h3 : ιR ⟨x', hx'⟩ * ((hσu'.unit : (UVCrossingModel O (π ^ m))) * V (π ^ m)) = const (π ^ m) (π ^ m * (ε : O)) :=
      (congrArg (fun z => ιR ⟨x', hx'⟩ * z) hsclause).symm.trans
        ((map_mul ιR _ _).symm.trans ((congrArg ιR e1).trans hconstϖ))
    exact ChartLocate.exists_units_eq_mul_U_of_mul_V_eq_const (π ^ m) hπmnzd ε _ hσu'.unit h3
  exact ⟨hSR, ι, hconst, ⟨1, (n : O), 1, G ⟨((algebraMap pr.Ring (Localization.Away ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0)))) ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf ((Ideal.Quotient.mk (Ideal.span {pr.rel})) (MvPowerSeries.X 0))), hw⟩, hp0, harith, h11, hβ, hX0, hX1⟩, ⟨hσu'.unit, hsclause⟩, hlast⟩

end S_DrinfeldCurve_LocalChart_exists_ringEquiv_adicCompletion_blowupChartAt_uvCrossingModel_pow_of_X_zero_div_not_mem
end P2MW
export P2MW.S_DrinfeldCurve_LocalChart_exists_ringEquiv_adicCompletion_blowupChartAt_uvCrossingModel_pow_of_X_zero_div_not_mem (solution)
