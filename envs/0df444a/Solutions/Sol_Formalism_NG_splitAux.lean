-- Prove2me | solution 1 for Formalism.NG.splitAux
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:09:39.290801+00:00
-- url     : https://prove2.me/submissions/061934ac-a79b-49b2-8235-d8f2e81ec2f4

import Definitions.Def_Formalism_CharacterColumnKernels_StatOntoLattice
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SplitFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial
noncomputable section
namespace Formalism.NG
universe u
private theorem exists_universal_splitting_algebra (n : ℕ) : ∀ (T : Type u) [CommRing T] (P : T[X]), P.Monic → P.natDegree = n →
    ∃ (T' : Type u) (_ : CommRing T') (_ : Algebra T T') (rr : Fin n → T'),
      Module.Free T T' ∧ Module.Finite T T' ∧ Module.finrank T T' = n.factorial ∧
      P.map (algebraMap T T') = ∏ i, (X - C (rr i)) ∧
      Algebra.adjoin T (Set.range rr) = ⊤ ∧
      ∀ (B : Type*) [CommRing B] [Algebra T B] (a : Fin n → B),
        P.map (algebraMap T B) = ∏ i, (X - C (a i)) →
        ∃ φ : T' →ₐ[T] B, ∀ i, φ (rr i) = a i := by
  induction n with
  | zero =>
    intro T _ P hP hdeg
    have hP1 : P = 1 := hP.natDegree_eq_zero.mp hdeg
    refine ⟨T, inferInstance, Algebra.id T, Fin.elim0, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
    · rcases subsingleton_or_nontrivial T with h | h
      · simp
      · rw [Module.finrank_self]
        rfl
    · simp [hP1]
    · rw [eq_top_iff]
      intro t _
      exact Subalgebra.algebraMap_mem _ t
    · intro B _ _ a _
      exact ⟨Algebra.ofId T B, fun i => i.elim0⟩
  | succ n ih =>
    intro T _ P hP hdeg
    have hnt : Nontrivial T := by
      rcases subsingleton_or_nontrivial T with h | h
      · exfalso
        have h0 : P = 0 := Subsingleton.elim _ _
        rw [h0, natDegree_zero] at hdeg
        omega
      · exact h
    let r : AdjoinRoot P := AdjoinRoot.root P
    let pb := AdjoinRoot.powerBasis' hP
    have hfree1 : Module.Free T (AdjoinRoot P) := Module.Free.of_basis pb.basis
    have hfin1 : Module.Finite T (AdjoinRoot P) := Module.Finite.of_basis pb.basis
    have hrank1 : Module.finrank T (AdjoinRoot P) = n + 1 := by
      rw [Module.finrank_eq_card_basis pb.basis, Fintype.card_fin]
      simp [pb, hdeg]
    have hroot : (P.map (algebraMap T (AdjoinRoot P))).IsRoot r := by
      rw [AdjoinRoot.algebraMap_eq]
      exact AdjoinRoot.isRoot_root P
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = P.map (algebraMap T (AdjoinRoot P)) /ₘ (X - C r) := ⟨_, rfl⟩
    have hfac1 : (X - C r) * Q = P.map (algebraMap T (AdjoinRoot P)) := by
      rw [hQ]
      exact mul_divByMonic_eq_iff_isRoot.mpr hroot
    have hPm : (P.map (algebraMap T (AdjoinRoot P))).Monic := hP.map _
    have hQm : Q.Monic := (monic_X_sub_C r).of_mul_monic_left (hfac1 ▸ hPm)
    have : Nontrivial (AdjoinRoot P) := Module.nontrivial_of_finrank_pos (by rw [hrank1]; omega)
    have hQdeg : Q.natDegree = n := by
      have h1 := (monic_X_sub_C r).natDegree_mul hQm
      rw [hfac1, hP.natDegree_map, hdeg, natDegree_X_sub_C] at h1
      omega
    obtain ⟨T₂, i₂, a₂, rr₂, hfree2, hfin2, hrank2, hfac2, hadj2, huniv2⟩ := ih (AdjoinRoot P) Q hQm hQdeg
    let _ : Algebra T T₂ := ((algebraMap (AdjoinRoot P) T₂).comp (algebraMap T (AdjoinRoot P))).toAlgebra
    have : IsScalarTower T (AdjoinRoot P) T₂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let rr : Fin (n + 1) → T₂ := Fin.cons (algebraMap (AdjoinRoot P) T₂ r) rr₂
    refine ⟨T₂, i₂, inferInstance, rr, Module.Free.trans (R := T) (S := AdjoinRoot P) (M := T₂),
      Module.Finite.trans (AdjoinRoot P) T₂,
      ?_, ?_, ?_, ?_⟩
    · rw [← Module.finrank_mul_finrank T (AdjoinRoot P) T₂, hrank1, hrank2, Nat.factorial_succ]
    · have hmap : P.map (algebraMap T T₂) =
          (P.map (algebraMap T (AdjoinRoot P))).map (algebraMap (AdjoinRoot P) T₂) := by
        rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
      rw [hmap, ← hfac1, Polynomial.map_mul, hfac2, Fin.prod_univ_succ]
      simp [rr]
    · have hsub : ∀ t : AdjoinRoot P,
          algebraMap (AdjoinRoot P) T₂ t ∈ Algebra.adjoin T (Set.range rr) := by
        intro t
        have ht : t ∈ Algebra.adjoin T ({r} : Set (AdjoinRoot P)) := by
          rw [AdjoinRoot.adjoinRoot_eq_top]
          trivial
        have hm : (IsScalarTower.toAlgHom T (AdjoinRoot P) T₂) t ∈
            (Algebra.adjoin T ({r} : Set (AdjoinRoot P))).map
              (IsScalarTower.toAlgHom T (AdjoinRoot P) T₂) := Subalgebra.mem_map.mpr ⟨t, ht, rfl⟩
        rw [AlgHom.map_adjoin, Set.image_singleton] at hm
        exact Algebra.adjoin_mono (by rintro _ rfl; exact ⟨0, rfl⟩) hm
      rw [eq_top_iff]
      rintro z -
      have hz : z ∈ Algebra.adjoin (AdjoinRoot P) (Set.range rr₂) := by
        rw [hadj2]
        trivial
      induction hz using Algebra.adjoin_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact Algebra.subset_adjoin ⟨i.succ, by simp [rr]⟩
      | algebraMap t => exact hsub t
      | add y w _ _ hy hw => exact add_mem hy hw
      | mul y w _ _ hy hw => exact mul_mem hy hw
    · intro B _ _ a ha
      have hroot0 : P.eval₂ (Algebra.ofId T B : T →+* B) (a 0) = 0 := by
        show P.eval₂ (algebraMap T B) (a 0) = 0
        rw [← Polynomial.eval_map, ha, Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ 0) (by simp)
      let ψ : AdjoinRoot P →ₐ[T] B := AdjoinRoot.liftAlgHom P (Algebra.ofId T B) (a 0) hroot0
      let _ : Algebra (AdjoinRoot P) B := ψ.toRingHom.toAlgebra
      have : IsScalarTower T (AdjoinRoot P) B :=
        IsScalarTower.of_algebraMap_eq fun t => (ψ.commutes t).symm
      have hψr : algebraMap (AdjoinRoot P) B r = a 0 := AdjoinRoot.liftAlgHom_root _ _ _ _
      have hQB : Q.map (algebraMap (AdjoinRoot P) B) = ∏ i : Fin n, (X - C (a i.succ)) := by
        have h1 : P.map (algebraMap T B) = (X - C (a 0)) * Q.map (algebraMap (AdjoinRoot P) B) := by
          rw [IsScalarTower.algebraMap_eq T (AdjoinRoot P) B, ← Polynomial.map_map, ← hfac1,
            Polynomial.map_mul]
          simp [hψr]
        rw [ha, Fin.prod_univ_succ] at h1
        have h3 := sub_eq_zero.mpr h1
        rw [← mul_sub, (monic_X_sub_C (a 0)).mul_right_eq_zero_iff, sub_eq_zero] at h3
        exact h3.symm
      obtain ⟨φ₂, hφ₂⟩ := huniv2 B (fun i => a i.succ) hQB
      refine ⟨φ₂.restrictScalars T, fun i => ?_⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [rr, Fin.cons_zero, AlgHom.restrictScalars_apply]
        rw [AlgHom.commutes, hψr]
      · simp only [rr, Fin.cons_succ, AlgHom.restrictScalars_apply]
        exact hφ₂ j
end Formalism.NG
end
end

set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.NG
universe u
namespace Formalism.NG
theorem _root_.solution (n : ℕ) : ∀ (T : Type u) [CommRing T] (P : T[X]), P.Monic → P.natDegree = n →
    ∃ (T' : Type u) (_ : CommRing T') (_ : Algebra T T') (rr : Fin n → T'),
      Module.Free T T' ∧ Module.Finite T T' ∧ Module.finrank T T' = n.factorial ∧
      P.map (algebraMap T T') = ∏ i, (X - C (rr i)) ∧
      Algebra.adjoin T (Set.range rr) = ⊤ ∧
      ∀ (B : Type u) [CommRing B] [Algebra T B] (a : Fin n → B),
        P.map (algebraMap T B) = ∏ i, (X - C (a i)) →
        ∃ φ : T' →ₐ[T] B, ∀ i, φ (rr i) = a i := by
  intro T _ P hP hdeg
  obtain ⟨T', i', a', rr, h1, h2, h3, h4, h5, h6⟩ := exists_universal_splitting_algebra n T P hP hdeg
  exact ⟨T', i', a', rr, h1, h2, h3, h4, h5, fun B _ _ a ha => h6 B a ha⟩
end Formalism.NG
