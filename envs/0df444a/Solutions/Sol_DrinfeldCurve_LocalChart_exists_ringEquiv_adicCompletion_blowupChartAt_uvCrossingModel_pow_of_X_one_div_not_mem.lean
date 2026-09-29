-- Prove2me | solution 1 for DrinfeldCurve.LocalChart.exists_ringEquiv_adicCompletion_blowupChartAt_uvCrossingModel_pow_of_X_one_div_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/8b814faa-e6a2-5a1f-b520-a51c277c3a10

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_DrinfeldCurve_LocalChart_exists_ringEquiv_adicCompletion_blowupChartAt_uvCrossingModel_pow_of_X_zero_div_not_mem
import Theorems.Thm_DrinfeldCurve_LocalChart_ChartPresentation_exists_swap_ringEquiv
import Theorems.Thm_AdicCompletion_exists_ringEquiv_map_of_ringEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_LocalChart_exists_ringEquiv_adicCompletion_blowupChartAt_uvCrossingModel_pow_of_X_one_div_not_mem
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

namespace ChartSwapSol

theorem transport {S S' : Type} [CommRing S] [CommRing S'] (e : S ≃+* S') (s : S) (𝔐 : Ideal S) (𝔐' : Ideal S')
    (h𝔐 : ∀ x : S', x ∈ 𝔐' ↔ e.symm x ∈ 𝔐) :
    ∃ E : Localization.Away s ≃+* Localization.Away (e s),
      (∀ x : S, E (algebraMap S (Localization.Away s) x) = algebraMap S' (Localization.Away (e s)) (e x)) ∧
      (Subring.closure (Set.range (algebraMap S (Localization.Away s)) ∪
          {x | ∃ i ∈ 𝔐, x * algebraMap S (Localization.Away s) s = algebraMap S (Localization.Away s) i})).map
          E.toRingHom =
        Subring.closure (Set.range (algebraMap S' (Localization.Away (e s))) ∪
          {x | ∃ i ∈ 𝔐', x * algebraMap S' (Localization.Away (e s)) (e s) =
            algebraMap S' (Localization.Away (e s)) i}) := by
  obtain ⟨E, hE⟩ : ∃ E : Localization.Away s ≃+* Localization.Away (e s),
      ∀ x : S, E (algebraMap S (Localization.Away s) x) = algebraMap S' (Localization.Away (e s)) (e x) :=
    ⟨IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers s) (T := Submonoid.powers (e s))
        (Localization.Away s) (Localization.Away (e s)) e (Submonoid.map_powers e.toMonoidHom s),
      fun x => IsLocalization.ringEquivOfRingEquiv_eq _ x⟩
  refine ⟨E, hE, ?_⟩
  rw [RingHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨i, rfl⟩ | ⟨i, hi, hx⟩
    · exact Or.inl ⟨e i, show algebraMap S' _ (e i) = E (algebraMap S _ i) by rw [hE]⟩
    · refine Or.inr ⟨e i, (h𝔐 _).mpr (by rw [e.symm_apply_apply]; exact hi), ?_⟩
      show E x * algebraMap S' _ (e s) = algebraMap S' _ (e i)
      rw [← hE, ← hE, ← map_mul, hx]
  · rintro (⟨i', hy⟩ | ⟨i', hi', hy⟩)
    · refine ⟨algebraMap S _ (e.symm i'), Or.inl ⟨e.symm i', rfl⟩, ?_⟩
      show E (algebraMap S _ (e.symm i')) = y
      rw [hE, e.apply_symm_apply]; exact hy
    · refine ⟨E.symm y, Or.inr ⟨e.symm i', (h𝔐 _).mp hi', ?_⟩, ?_⟩
      · apply E.injective
        rw [map_mul, E.apply_symm_apply, hE, hE, e.apply_symm_apply]; exact hy
      · show E (E.symm y) = y
        rw [E.apply_symm_apply]

theorem subEquiv {L L' : Type} [CommRing L] [CommRing L'] (E : L ≃+* L') (A : Subring L) (A' : Subring L')
    (h : A.map E.toRingHom = A') :
    ∃ ER : ↥A ≃+* ↥A', (∀ x : ↥A, ((ER x : ↥A') : L') = E x) ∧ (∀ y : ↥A', ((ER.symm y : ↥A) : L) = E.symm y) := by
  subst h
  refine ⟨(RingEquiv.subringMap E : ↥A ≃+* ↥(A.map E.toRingHom)), fun x => rfl, fun y => ?_⟩
  have h1 : E (((RingEquiv.subringMap E : ↥A ≃+* ↥(A.map E.toRingHom)).symm y : ↥A) : L) = (y : L') :=
    congrArg (fun z : ↥(A.map E.toRingHom) => (z : L'))
      ((RingEquiv.subringMap E : ↥A ≃+* ↥(A.map E.toRingHom)).apply_symm_apply y)
  calc (((RingEquiv.subringMap E : ↥A ≃+* ↥(A.map E.toRingHom)).symm y : ↥A) : L) =
      E.symm (E (((RingEquiv.subringMap E : ↥A ≃+* ↥(A.map E.toRingHom)).symm y : ↥A) : L)) :=
        (E.symm_apply_apply _).symm
    _ = E.symm y := by rw [h1]

theorem mem_nonZeroDivisors_map {S S' : Type} [CommRing S] [CommRing S'] (e : S ≃+* S') {s : S}
    (hs : s ∈ nonZeroDivisors S) : e s ∈ nonZeroDivisors S' := by
  rw [mem_nonZeroDivisors_iff] at hs ⊢
  obtain ⟨hs1, hs2⟩ := hs
  constructor
  · intro y hy
    have h1 : s * e.symm y = 0 := by
      apply e.injective
      rw [map_mul, e.apply_symm_apply, map_zero]; exact hy
    have h2 := congrArg e (hs1 _ h1)
    rwa [e.apply_symm_apply, map_zero] at h2
  · intro y hy
    have h1 : e.symm y * s = 0 := by
      apply e.injective
      rw [map_mul, e.apply_symm_apply, map_zero]; exact hy
    have h2 := congrArg e (hs2 _ h1)
    rwa [e.apply_symm_apply, map_zero] at h2

theorem mem_span_triple_iff_of_ringEquiv {S S' : Type} [CommRing S] [CommRing S'] (e : S ≃+* S')
    (a b c : S) (a' b' c' : S') (ha : e a = a') (hb : e b = c') (hc : e c = b') (x : S') :
    x ∈ Ideal.span {a', b', c'} ↔ e.symm x ∈ Ideal.span {a, b, c} := by
  have hmap : Ideal.map e (Ideal.span {a, b, c}) = Ideal.span {a', b', c'} := by
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, ha, hb, hc,
      Set.pair_comm c' b']
  rw [← hmap, Ideal.symm_apply_mem_of_equiv_iff]

end ChartSwapSol

end

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

open ChartSwapSol in
set_option maxHeartbeats 160000000 in
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
        (hchart : ∀ (t : Ls) (ht : t ∈ Rs), t * algebraMap S Ls s = algebraMap S Ls (mkS (MvPowerSeries.X 1)) → (⟨t, ht⟩ : ↥Rs) ∉ P')
        (hslope : ∀ (t t' : Ls) (ht : t ∈ Rs) (ht' : t' ∈ Rs),
          t * algebraMap S Ls s = algebraMap S Ls (mkS (MvPowerSeries.X 1)) →
          t' * algebraMap S Ls s = algebraMap S Ls (mkS (MvPowerSeries.X 0)) →
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

  obtain ⟨pr', e₀, heC₀, heX0₀, heX1₀, -, -, -⟩ :=
    DrinfeldCurve.LocalChart.ChartPresentation.exists_swap_ringEquiv q O ϖ ⟨f, u, v, hu, hv, hf⟩

  set S' : Type := (MvPowerSeries (Fin 2) O ⧸
      Ideal.span {MvPowerSeries.C (ϖ ^ (q + 1)) * pr'.v - pr'.f * pr'.u}) with hS'def
  let mk' : MvPowerSeries (Fin 2) O →+* S' :=
    Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (ϖ ^ (q + 1)) * pr'.v - pr'.f * pr'.u})
  obtain ⟨e, heC, heX0, heX1⟩ : ∃ e : S ≃+* S',
      (∀ o : O, e (mkS (MvPowerSeries.C o)) = mk' (MvPowerSeries.C o)) ∧
      e (mkS (MvPowerSeries.X 0)) = mk' (MvPowerSeries.X 1) ∧
      e (mkS (MvPowerSeries.X 1)) = mk' (MvPowerSeries.X 0) :=
    ⟨e₀, heC₀, heX0₀, heX1₀⟩
  clear heC₀ heX0₀ heX1₀

  have hsnz' := mem_nonZeroDivisors_map e hsnz
  have h𝔐 : ∀ x, x ∈ Ideal.span {mk' (MvPowerSeries.C ϖ), mk' (MvPowerSeries.X 0), mk' (MvPowerSeries.X 1)} ↔
      e.symm x ∈ 𝔐 :=
    mem_span_triple_iff_of_ringEquiv e _ _ _ _ _ _ (heC ϖ) heX0 heX1
  have hs' : e s ∈ Ideal.span {mk' (MvPowerSeries.C ϖ), mk' (MvPowerSeries.X 0), mk' (MvPowerSeries.X 1)} :=
    (h𝔐 _).mpr (by rw [e.symm_apply_apply]; exact hs)
  obtain ⟨E, hE, hRs⟩ := transport e s 𝔐
    (Ideal.span {mk' (MvPowerSeries.C ϖ), mk' (MvPowerSeries.X 0), mk' (MvPowerSeries.X 1)}) h𝔐

  set Rs' : Subring (Localization.Away (e s)) := Subring.closure
      (Set.range (algebraMap S' (Localization.Away (e s))) ∪
        {x | ∃ i ∈ Ideal.span {mk' (MvPowerSeries.C ϖ), mk' (MvPowerSeries.X 0), mk' (MvPowerSeries.X 1)},
          x * algebraMap S' (Localization.Away (e s)) (e s) = algebraMap S' (Localization.Away (e s)) i})
    with hRs'def
  obtain ⟨ER, hER, hERs⟩ := subEquiv E Rs Rs' hRs
  have hSR : ∀ i : S, algebraMap S Ls i ∈ Rs := fun i => Subring.subset_closure (Or.inl ⟨i, rfl⟩)
  have hmemMap : ∀ y, y ∈ Rs.map E.toRingHom ↔ E.symm y ∈ Rs := by
    intro y
    constructor
    · rintro ⟨x, hx, hxy⟩
      rw [← hxy]
      show E.symm (E x) ∈ Rs
      rw [E.symm_apply_apply]; exact hx
    · intro h; exact ⟨E.symm y, h, show E (E.symm y) = y from E.apply_symm_apply y⟩
  have hmemRs' : ∀ y, y ∈ Rs' ↔ E.symm y ∈ Rs := fun y => hRs ▸ hmemMap y

  have hC := DrinfeldCurve.LocalChart.exists_ringEquiv_adicCompletion_blowupChartAt_uvCrossingModel_pow_of_X_zero_div_not_mem
    q O π hπ ϖ hϖ hϖ0 m hm ε hϖπ (ϖ ^ (q + 1)) rfl pr'.f pr'.u pr'.v pr'.isUnit_u pr'.isUnit_v pr'.f_sub_mem hqO
    (e s) hsnz' hs'

  have hP'' : (Ideal.map ER P').IsMaximal := by haveI := hP'; infer_instance
  have hover' : ∀ (i : S') (hi : algebraMap S' (Localization.Away (e s)) i ∈ Rs'),
      i ∈ Ideal.span {mk' (MvPowerSeries.C π), mk' (MvPowerSeries.X 0), mk' (MvPowerSeries.X 1)} →
      (⟨_, hi⟩ : ↥Rs') ∈ Ideal.map ER P' := by
    intro i hi hmem
    have hπ3 : ∀ x, x ∈ Ideal.span {mk' (MvPowerSeries.C π), mk' (MvPowerSeries.X 0), mk' (MvPowerSeries.X 1)} ↔
        e.symm x ∈ Ideal.span {mkS (MvPowerSeries.C π), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} :=
      mem_span_triple_iff_of_ringEquiv e _ _ _ _ _ _ (heC π) heX0 heX1
    have h1 := hover (e.symm i) (hSR _) ((hπ3 i).mp hmem)
    have h2 : ER ⟨_, hSR (e.symm i)⟩ = ⟨_, hi⟩ :=
      Subtype.ext ((hER _).trans ((hE _).trans (congrArg (algebraMap S' (Localization.Away (e s))) (e.apply_symm_apply i))))
    exact h2 ▸ Ideal.mem_map_of_mem ER h1
  have hoff' : ∀ (x : Localization.Away (e s)) (hx : x ∈ Rs'),
      x * algebraMap S' (Localization.Away (e s)) (e s) = algebraMap S' (Localization.Away (e s)) (mk' (MvPowerSeries.C ϖ)) →
      (⟨x, hx⟩ : ↥Rs') ∈ Ideal.map ER P' := by
    intro x hx hrel
    have hx0 : E.symm x ∈ Rs := (hmemRs' x).mp hx
    have hrel0 : E.symm x * algebraMap S Ls s = algebraMap S Ls (mkS (MvPowerSeries.C ϖ)) := by
      apply E.injective
      rw [map_mul, E.apply_symm_apply, hE, hE]
      exact hrel.trans (congrArg (algebraMap S' (Localization.Away (e s))) (heC ϖ)).symm
    have h1 := hoff (E.symm x) hx0 hrel0
    have h2 : ER ⟨E.symm x, hx0⟩ = ⟨x, hx⟩ := Subtype.ext ((hER _).trans (E.apply_symm_apply x))
    exact h2 ▸ Ideal.mem_map_of_mem ER h1
  have hchart' : ∀ (t : Localization.Away (e s)) (ht : t ∈ Rs'),
      t * algebraMap S' (Localization.Away (e s)) (e s) = algebraMap S' (Localization.Away (e s)) (mk' (MvPowerSeries.X 0)) →
      (⟨t, ht⟩ : ↥Rs') ∉ Ideal.map ER P' := by
    intro t ht hrel hmem
    have ht0 : E.symm t ∈ Rs := (hmemRs' t).mp ht
    have hrel0 : E.symm t * algebraMap S Ls s = algebraMap S Ls (mkS (MvPowerSeries.X 1)) := by
      apply E.injective
      rw [map_mul, E.apply_symm_apply, hE, hE]
      exact hrel.trans (congrArg (algebraMap S' (Localization.Away (e s))) heX1).symm
    apply hchart (E.symm t) ht0 hrel0
    have h2 : ER.symm ⟨t, ht⟩ = ⟨E.symm t, ht0⟩ := Subtype.ext (hERs _)
    exact h2 ▸ (Ideal.symm_apply_mem_of_equiv_iff.mpr hmem)
  have hslope' : ∀ (t t' : Localization.Away (e s)) (ht : t ∈ Rs') (ht' : t' ∈ Rs'),
      t * algebraMap S' (Localization.Away (e s)) (e s) = algebraMap S' (Localization.Away (e s)) (mk' (MvPowerSeries.X 0)) →
      t' * algebraMap S' (Localization.Away (e s)) (e s) = algebraMap S' (Localization.Away (e s)) (mk' (MvPowerSeries.X 1)) →
      (⟨t', ht'⟩ : ↥Rs') - ((n : ℕ) : ↥Rs') * ⟨t, ht⟩ ∈ Ideal.map ER P' := by
    intro t t' ht ht' hrel hrel'
    have ht0 : E.symm t ∈ Rs := (hmemRs' t).mp ht
    have ht'0 : E.symm t' ∈ Rs := (hmemRs' t').mp ht'
    have hrel0 : E.symm t * algebraMap S Ls s = algebraMap S Ls (mkS (MvPowerSeries.X 1)) := by
      apply E.injective
      rw [map_mul, E.apply_symm_apply, hE, hE]
      exact hrel.trans (congrArg (algebraMap S' (Localization.Away (e s))) heX1).symm
    have hrel'0 : E.symm t' * algebraMap S Ls s = algebraMap S Ls (mkS (MvPowerSeries.X 0)) := by
      apply E.injective
      rw [map_mul, E.apply_symm_apply, hE, hE]
      exact hrel'.trans (congrArg (algebraMap S' (Localization.Away (e s))) heX0).symm
    have h1 := hslope (E.symm t) (E.symm t') ht0 ht'0 hrel0 hrel'0
    have h2 : ER (⟨E.symm t', ht'0⟩ - ((n : ℕ) : ↥Rs) * ⟨E.symm t, ht0⟩) =
        (⟨t', ht'⟩ : ↥Rs') - ((n : ℕ) : ↥Rs') * ⟨t, ht⟩ := by
      rw [map_sub, map_mul, map_natCast]
      congr 1
      · exact Subtype.ext ((hER _).trans (E.apply_symm_apply t'))
      · congr 1; exact Subtype.ext ((hER _).trans (E.apply_symm_apply t))
    exact h2 ▸ Ideal.mem_map_of_mem ER h1
  obtain ⟨hSR', ι', hconst', ⟨p₀', p₁', α', β', hdir', hform', hα', hβ', hX0', hX1'⟩, ⟨γV', hγV'⟩, hoffU'⟩ :=
    hC (Ideal.map ER P') hP'' hover' hoff' n hchart' hslope'

  obtain ⟨ê, hê⟩ := AdicCompletion.exists_ringEquiv_map_of_ringEquiv P' ER

  have hERC : ∀ o : O, ER ⟨_, hSR (mkS (MvPowerSeries.C o))⟩ = ⟨_, hSR' (mk' (MvPowerSeries.C o))⟩ := fun o =>
    Subtype.ext ((hER _).trans ((hE _).trans (congrArg (algebraMap S' (Localization.Away (e s))) (heC o))))
  have hER0 : ER ⟨_, hSR (mkS (MvPowerSeries.X 0))⟩ = ⟨_, hSR' (mk' (MvPowerSeries.X 1))⟩ :=
    Subtype.ext ((hER _).trans ((hE _).trans (congrArg (algebraMap S' (Localization.Away (e s))) heX0)))
  have hER1 : ER ⟨_, hSR (mkS (MvPowerSeries.X 1))⟩ = ⟨_, hSR' (mk' (MvPowerSeries.X 0))⟩ :=
    Subtype.ext ((hER _).trans ((hE _).trans (congrArg (algebraMap S' (Localization.Away (e s))) heX1)))
  have hERs : ER ⟨_, hSR s⟩ = ⟨_, hSR' (e s)⟩ := Subtype.ext ((hER _).trans (hE s))
  have key : ∀ (x : ↥Rs), (ê.trans ι') (algebraMap ↥Rs (AdicCompletion P' ↥Rs) x) =
      ι' (algebraMap ↥Rs' (AdicCompletion (Ideal.map ER P') ↥Rs') (ER x)) :=
    fun x => (RingEquiv.trans_apply ê ι' _).trans (congrArg ι' (hê x))
  refine ⟨hSR, ê.trans ι', ?_, ⟨p₁', p₀', β', α', hdir'.symm, ?_, hβ', hα', ?_, ?_⟩, ⟨γV', ?_⟩, ?_⟩
  ·
    intro o
    exact (key _).trans ((congrArg (fun z : ↥Rs' => ι' (algebraMap ↥Rs' (AdicCompletion (Ideal.map ER P') ↥Rs') z))
      (hERC o)).trans (hconst' o))
  ·
    have : p₁' ^ q * p₀' - p₁' * p₀' ^ q = -(p₀' ^ q * p₁' - p₀' * p₁' ^ q) := by ring
    rw [this]; exact Submodule.neg_mem _ hform'
  ·
    exact (key _).trans ((congrArg (fun z : ↥Rs' => ι' (algebraMap ↥Rs' (AdicCompletion (Ideal.map ER P') ↥Rs') z))
      hER0).trans hX1')
  ·
    exact (key _).trans ((congrArg (fun z : ↥Rs' => ι' (algebraMap ↥Rs' (AdicCompletion (Ideal.map ER P') ↥Rs') z))
      hER1).trans hX0')
  ·
    exact (key _).trans ((congrArg (fun z : ↥Rs' => ι' (algebraMap ↥Rs' (AdicCompletion (Ideal.map ER P') ↥Rs') z))
      hERs).trans hγV')
  ·
    intro x hx hrel
    have hx' : E x ∈ Rs' := (hmemRs' _).mpr ((E.symm_apply_apply x).symm ▸ hx)
    have hrel' : E x * algebraMap S' (Localization.Away (e s)) (e s) =
        algebraMap S' (Localization.Away (e s)) (mk' (MvPowerSeries.C ϖ)) := by
      have h1 : E (x * algebraMap S Ls s) = E (algebraMap S Ls (mkS (MvPowerSeries.C ϖ))) := congrArg E hrel
      rw [map_mul, hE, hE] at h1
      exact h1.trans (congrArg (algebraMap S' (Localization.Away (e s))) (heC ϖ))
    obtain ⟨γU, hγU⟩ := hoffU' (E x) hx' hrel'
    have h3 : ER ⟨x, hx⟩ = ⟨E x, hx'⟩ := Subtype.ext (hER _)
    exact ⟨γU, (key _).trans ((congrArg (fun z : ↥Rs' => ι' (algebraMap ↥Rs' (AdicCompletion (Ideal.map ER P') ↥Rs') z))
      h3).trans hγU)⟩

end S_DrinfeldCurve_LocalChart_exists_ringEquiv_adicCompletion_blowupChartAt_uvCrossingModel_pow_of_X_one_div_not_mem
end P2MW
export P2MW.S_DrinfeldCurve_LocalChart_exists_ringEquiv_adicCompletion_blowupChartAt_uvCrossingModel_pow_of_X_one_div_not_mem (solution)
