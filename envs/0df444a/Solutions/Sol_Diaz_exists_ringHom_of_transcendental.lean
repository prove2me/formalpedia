-- Prove2me | solution 1 for Diaz.exists_ringHom_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T09:36:16.563386+00:00
-- url     : https://prove2.me/submissions/67175e78-ad05-4f58-8bad-ccd9bda8cf32

import Mathlib

open scoped Cardinal

noncomputable section

theorem solution {K : Subfield ℂ} {u t : ℂ}
    (hu : Transcendental (↥K) u) (ht : Transcendental (↥K) t) :
    ∃ Φ : ℂ →+* ℂ, (∀ a ∈ K, Φ a = a) ∧ Φ u = t := by
  -- Step 1: extend `{u}` and `{t}` to transcendence bases of `ℂ` over `K`.
  have hu' : AlgebraicIndepOn (↥K) id ({u} : Set ℂ) := by
    exact (algebraicIndependent_singleton_iff (R := ↥K)
      (x := fun x : ({u} : Set ℂ) => id (x : ℂ)) ⟨u, rfl⟩).2 hu
  have ht' : AlgebraicIndepOn (↥K) id ({t} : Set ℂ) := by
    exact (algebraicIndependent_singleton_iff (R := ↥K)
      (x := fun x : ({t} : Set ℂ) => id (x : ℂ)) ⟨t, rfl⟩).2 ht
  obtain ⟨B, huB, hB⟩ := exists_isTranscendenceBasis_superset hu'
  obtain ⟨C, htC, hC⟩ := exists_isTranscendenceBasis_superset ht'
  -- Step 2: the two bases are equipotent, and can be matched sending `u` to `t`.
  have hcard : #(↥B) = #(↥C) := hB.cardinalMk_eq hC
  obtain ⟨f⟩ := Cardinal.eq.mp hcard
  set iu : ↥B := ⟨u, huB rfl⟩ with hiu
  set it : ↥C := ⟨t, htC rfl⟩ with hit
  set e : ↥B ≃ ↥C := f.trans (Equiv.swap (f iu) it) with he
  have hei : e iu = it := by simp [he]
  -- Step 3: transport the polynomial presentations of the two bases into each other.
  set v : ↥B → ℂ := ((↑) : ↥B → ℂ) with hvdef
  set w : ↥C → ℂ := ((↑) : ↥C → ℂ) with hwdef
  have i1 : IsAlgClosure (Algebra.adjoin (↥K) (Set.range v)) ℂ :=
    IsAlgClosed.isAlgClosure_of_transcendence_basis v hB
  have i2 : IsAlgClosure (Algebra.adjoin (↥K) (Set.range w)) ℂ :=
    IsAlgClosed.isAlgClosure_of_transcendence_basis w hC
  set ε : Algebra.adjoin (↥K) (Set.range v) ≃ₐ[↥K] Algebra.adjoin (↥K) (Set.range w) :=
    hB.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv (↥K) e).trans hC.1.aevalEquiv) with hε
  set Phi : ℂ ≃+* ℂ := IsAlgClosure.equivOfEquiv ℂ ℂ ε.toRingEquiv with hPhi
  refine ⟨Phi.toRingHom, ?_, ?_⟩
  · intro a ha
    have h1 : (a : ℂ) = algebraMap (Algebra.adjoin (↥K) (Set.range v)) ℂ
        (algebraMap (↥K) (Algebra.adjoin (↥K) (Set.range v)) ⟨a, ha⟩) := by
      rw [← IsScalarTower.algebraMap_apply]
      rfl
    rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    conv_lhs => rw [h1]
    rw [hPhi, IsAlgClosure.equivOfEquiv_algebraMap]
    show algebraMap (Algebra.adjoin (↥K) (Set.range w)) ℂ
      (ε (algebraMap (↥K) (Algebra.adjoin (↥K) (Set.range v)) ⟨a, ha⟩)) = a
    rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
    rfl
  · have h2 : u = algebraMap (Algebra.adjoin (↥K) (Set.range v)) ℂ
        (hB.1.aevalEquiv (MvPolynomial.X iu)) := by
      rw [AlgebraicIndependent.algebraMap_aevalEquiv]
      simp [hvdef, hiu]
    rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    conv_lhs => rw [h2]
    rw [hPhi, IsAlgClosure.equivOfEquiv_algebraMap]
    show algebraMap (Algebra.adjoin (↥K) (Set.range w)) ℂ
      (ε (hB.1.aevalEquiv (MvPolynomial.X iu))) = t
    rw [hε]
    simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply,
      MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, hei]
    rw [AlgebraicIndependent.algebraMap_aevalEquiv]
    simp [hwdef, hit]
