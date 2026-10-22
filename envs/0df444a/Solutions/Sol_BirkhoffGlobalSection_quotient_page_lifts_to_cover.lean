-- Prove2me | solution 1 for BirkhoffGlobalSection.quotient_page_lifts_to_cover
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-26T20:52:10.230981+00:00
-- url     : https://prove2.me/submissions/78f5ae63-2c83-40de-94ba-5530325021f4

import Definitions.Def_BirkhoffGlobalSection_LiftedRationalPage

open BirkhoffGlobalSection

set_option autoImplicit false

theorem solution {μ c : ℝ} (φ : Flow ℝ (LeftEnergyState μ c))
    (hanti : IsAntipodallyEquivariantFlow μ c φ)
    (hinv : IsAntipodallyInvariantComponent μ c)
    (hfree : IsAntipodallyFreeComponent μ c)
    (hcont : IsContinuousQuotientDynamics φ hanti)
    (γ : PeriodicOrbit φ) (hdouble : IsAntipodalDoubleCover φ γ)
    (Q : RationalDiskLikeGlobalSurfaceOfSection φ hanti γ) :
    Nonempty (LiftedRationalPage φ γ) := by
  obtain ⟨-, -, -, -, page, hpage, hsmooth, hinj, himm, htrans, hbound,
    -, -, hfib, -, hret⟩ := Q
  have qeq : ∀ x y : LeftEnergyState μ c,
      toAntipodalQuotient x = toAntipodalQuotient y ↔
        (x : Phase) = (y : Phase) ∨ (x : Phase) = -(y : Phase) :=
    fun x y => Quotient.eq
  have qtm : ∀ (t : ℝ) (s : LeftEnergyState μ c),
      quotientTimeMap φ hanti t (toAntipodalQuotient s) =
        toAntipodalQuotient (φ t s) := fun t s => rfl
  have hhalf : ((φ (γ.period / 2) γ.point : LeftEnergyState μ c) : Phase) =
      -(γ.point : Phase) := hdouble.2
  have hsym : ∀ s : Phase, s ∈ orbitSet γ → -s ∈ orbitSet γ := by
    rintro s ⟨t, ht⟩
    have ht' : ((φ t γ.point : LeftEnergyState μ c) : Phase) = s := ht
    refine ⟨t + γ.period / 2, ?_⟩
    have hmap : φ (t + γ.period / 2) γ.point =
        φ t (φ (γ.period / 2) γ.point) :=
      φ.map_add t (γ.period / 2) γ.point
    calc ((φ (t + γ.period / 2) γ.point : LeftEnergyState μ c) : Phase)
        = ((φ t (φ (γ.period / 2) γ.point) :
            LeftEnergyState μ c) : Phase) := by rw [hmap]
      _ = -((φ t γ.point : LeftEnergyState μ c) : Phase) :=
          hanti t _ _ hhalf
      _ = -s := by rw [ht']
  have hne : ∀ u : Plane, u ∈ unitCircle → u ≠ -u := by
    intro u hu hcon
    have h0 : u 0 = -(u 0) := congrFun hcon 0
    have h1 : u 1 = -(u 1) := congrFun hcon 1
    have e0 : u 0 = 0 := by linarith
    have e1 : u 1 = 0 := by linarith
    have h01 : planeNormSq u = 0 := by
      unfold planeNormSq
      rw [e0, e1]
      norm_num
    have hu1 : planeNormSq u = 1 := hu
    rw [hu1] at h01
    norm_num at h01
  have hmem_closed : ∀ u : Plane, u ∈ unitCircle → u ∈ closedUnitDisk := by
    intro u hu
    exact le_of_eq hu
  refine ⟨⟨page, hpage, hsmooth, hinj, himm, htrans, hbound, ?_, ?_⟩⟩
  · intro u hu v hv
    constructor
    · intro h
      have hq : quotientDiskPage page hpage ⟨u, hu⟩ =
          quotientDiskPage page hpage ⟨v, hv⟩ :=
        (qeq _ _).mpr (Or.inr h)
      rcases (hfib ⟨u, hu⟩ ⟨v, hv⟩).mp hq with hEq | hB
      · exfalso
        have huv : u = v := hEq
        subst huv
        exact hfree ⟨page u, hpage u hu⟩ h
      · exact hB
    · rintro ⟨huc, hvc, huv⟩
      have hq : quotientDiskPage page hpage ⟨u, hu⟩ =
          quotientDiskPage page hpage ⟨v, hv⟩ :=
        (hfib ⟨u, hu⟩ ⟨v, hv⟩).mpr (Or.inr ⟨huc, hvc, huv⟩)
      rcases (qeq _ _).mp hq with hEq | hMinus
      · exfalso
        have hne' : u ≠ v := by
          rw [huv]
          exact hne u huc
        exact hne' (hinj hu hv hEq)
      · exact hMinus
  · intro s hs
    have hsQ : toAntipodalQuotient s ∉ quotientOrbitSet hanti γ := by
      rintro ⟨t, ht⟩
      apply hs
      have h1 := qtm t γ.point
      have ht' : quotientTimeMap φ hanti t (toAntipodalQuotient γ.point) =
          toAntipodalQuotient s := ht
      rw [h1] at ht'
      rcases (qeq _ _).mp ht' with hEq | hMinus
      · exact ⟨t, hEq⟩
      · have hmem : -((φ t γ.point : LeftEnergyState μ c) : Phase) ∈
            orbitSet γ :=
          hsym _ ⟨t, rfl⟩
        rw [hMinus] at hmem
        simpa using hmem
    obtain ⟨hpos, hneg⟩ := hret _ hsQ
    constructor
    · intro R
      obtain ⟨t, ht, w, hw, hweq⟩ := hpos R
      refine ⟨t, ht, (w : Plane), hw, ?_⟩
      have hu_disk : (w : Plane) ∈ closedUnitDisk := w.property
      have hte : toAntipodalQuotient (φ t s) =
          toAntipodalQuotient ⟨page (w : Plane), hpage _ hu_disk⟩ := by
        have h2 := qtm t s
        rw [h2] at hweq
        exact hweq.symm
      rcases (qeq _ _).mp hte with hEq | hMinus
      · exact Or.inl hEq
      · exact Or.inr hMinus
    · intro R
      obtain ⟨t, ht, w, hw, hweq⟩ := hneg R
      refine ⟨t, ht, (w : Plane), hw, ?_⟩
      have hu_disk : (w : Plane) ∈ closedUnitDisk := w.property
      have hte : toAntipodalQuotient (φ t s) =
          toAntipodalQuotient ⟨page (w : Plane), hpage _ hu_disk⟩ := by
        have h2 := qtm t s
        rw [h2] at hweq
        exact hweq.symm
      rcases (qeq _ _).mp hte with hEq | hMinus
      · exact Or.inl hEq
      · exact Or.inr hMinus
