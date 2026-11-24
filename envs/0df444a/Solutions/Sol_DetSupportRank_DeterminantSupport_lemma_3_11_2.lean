-- Prove2me | solution 2 for DetSupportRank.DeterminantSupport.lemma_3_11
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T23:08:04.475088+00:00
-- url     : https://prove2.me/submissions/96bf39ad-fc13-40ea-b5d7-c321081bffff

import Definitions.Def_DetSupportRank_DeterminantSupport_DegreeRelations

set_option autoImplicit false
open scoped BigOperators
open DetSupportRank.DeterminantSupport

/-- `∑_{I ⊆ univ} (-1)^|I| [S ⊆ I] = [S = univ] (-1)^r`, via `∏ (-1 + [i ∉ S])`. -/
private lemma dsr311_inner_sum {R : Type*} [CommRing R] (r : ℕ) (S : Finset (Fin r)) :
    (∑ I ∈ (Finset.univ : Finset (Fin r)).powerset,
      (-1 : R) ^ I.card * (if S ⊆ I then 1 else 0)) =
    if S = Finset.univ then (-1 : R) ^ r else 0 := by
  have h := Finset.prod_add (fun _ : Fin r => (-1 : R))
    (fun i => if i ∈ S then (0 : R) else 1) Finset.univ
  have lhs : ∏ i : Fin r, ((-1 : R) + if i ∈ S then 0 else 1) =
      if S = Finset.univ then (-1 : R) ^ r else 0 := by
    split_ifs with hS
    · subst hS; simp
    · obtain ⟨i, hi⟩ : ∃ i, i ∉ S := by
        by_contra hc
        push Not at hc
        exact hS (Finset.eq_univ_of_forall hc)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  rw [← lhs, h]
  refine Finset.sum_congr rfl (fun I _ => ?_)
  rw [Finset.prod_const (s := I) (-1 : R)]
  congr 1
  symm
  split_ifs with hSI
  · refine Finset.prod_eq_one (fun i hi => ?_)
    have : i ∉ I := (Finset.mem_sdiff.mp hi).2
    have : i ∉ S := fun h' => this (hSI h')
    simp [this]
  · obtain ⟨i, hiS, hiI⟩ := Finset.not_subset.mp hSI
    exact Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiI⟩) (by simp [hiS])

theorem solution {R : Type*} [CommRing R] (r : ℕ) (t : Fin r → R) :
    (∑ I ∈ (Finset.univ : Finset (Fin r)).powerset,
      (-1 : R) ^ I.card * (∑ i ∈ I, t i) ^ r) =
    (-1 : R) ^ r * (Nat.factorial r : R) * ∏ i, t i := by
  have expand : ∀ I : Finset (Fin r), (∑ i ∈ I, t i) ^ r =
      ∑ f : Fin r → Fin r,
        (∏ j, t (f j)) * (if Finset.univ.image f ⊆ I then (1 : R) else 0) := by
    intro I
    have : (∑ i ∈ I, t i) = ∑ i, (if i ∈ I then t i else 0) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [this, ← Fin.prod_const, Fintype.prod_sum]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    rw [Finset.prod_ite_zero]
    by_cases h1 : ∀ j ∈ (Finset.univ : Finset (Fin r)), f j ∈ I
    · have h2 : Finset.univ.image f ⊆ I := by
        intro x hx
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
        exact h1 j (Finset.mem_univ j)
      simp [h1, h2]
    · have h2 : ¬ Finset.univ.image f ⊆ I := by
        intro h
        exact h1 (fun j _ => h (Finset.mem_image_of_mem f (Finset.mem_univ j)))
      rw [if_neg h1, if_neg h2, mul_zero]
  simp_rw [expand, Finset.mul_sum]
  rw [Finset.sum_comm]
  have step : ∀ f : Fin r → Fin r,
      ∑ I ∈ (Finset.univ : Finset (Fin r)).powerset, (-1 : R) ^ I.card *
        ((∏ j, t (f j)) * (if Finset.univ.image f ⊆ I then (1 : R) else 0)) =
      (∏ j, t (f j)) *
        (if Finset.univ.image f = Finset.univ then (-1 : R) ^ r else 0) := by
    intro f
    rw [← dsr311_inner_sum r (Finset.univ.image f), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun I _ => ?_)
    ring
  simp_rw [step, mul_ite, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_mul]
  have perm : ∑ f ∈ Finset.univ.filter
      (fun f : Fin r → Fin r => Finset.univ.image f = Finset.univ), ∏ j, t (f j) =
      ∑ σ : Equiv.Perm (Fin r), ∏ j, t (σ j) := by
    symm
    apply Finset.sum_bij (fun (σ : Equiv.Perm (Fin r)) _ => (σ : Fin r → Fin r))
    · intro σ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Finset.image_univ_of_surjective σ.surjective
    · intro a _ b _ h
      exact Equiv.ext (congrFun h)
    · intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      have hs : Function.Surjective f := by
        intro y
        have : y ∈ Finset.univ.image f := by rw [hf]; exact Finset.mem_univ y
        obtain ⟨x, -, hx⟩ := Finset.mem_image.mp this
        exact ⟨x, hx⟩
      have hb : Function.Bijective f := Finite.surjective_iff_bijective.mp hs
      exact ⟨Equiv.ofBijective f hb, Finset.mem_univ _, rfl⟩
    · intro σ _
      rfl
  rw [perm]
  simp_rw [Equiv.prod_comp]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  ring
