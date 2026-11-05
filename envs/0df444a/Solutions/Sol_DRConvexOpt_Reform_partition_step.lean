-- Prove2me | solution 1 for DRConvexOpt.Reform.partition_step
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T12:04:14.957136+00:00
-- url     : https://prove2.me/submissions/7273ca4e-0b27-445d-9d0f-8d99142cd679

import Mathlib
import Definitions.Def_DRConvexOpt_Reform_Setting

open MeasureTheory Matrix DRConvexOpt.Reform

namespace DRCOPartAux

lemma tdot {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (y : Fin m → ℝ) (z : Fin n → ℝ) :
    (Mᵀ *ᵥ y) ⬝ᵥ z = (M *ᵥ z) ⬝ᵥ y := by
  rw [mulVec_transpose, dotProduct_comm (M *ᵥ z), dotProduct_mulVec]

lemma sinc_trans {α : Type*} [TopologicalSpace α] {A B C : Set α} (h1 : SInc A B)
    (h2 : SInc B C) : SInc A C :=
  h1.trans (interior_subset.trans h2)

lemma conf_closed {nP nQ nK nI : ℕ} (d : AmbData nP nQ nK nI)
    (hK : ∀ i, IsProperCone (d.K i)) (i : Fin (nI + 1)) : IsClosed (d.conf i) := by
  have hc : Continuous fun ω : (Fin nP → ℝ) × (Fin nQ → ℝ) =>
      d.c i - (d.C i *ᵥ ω.1 + d.D i *ᵥ ω.2) :=
    continuous_const.sub ((continuous_const.matrix_mulVec continuous_fst).add
      (continuous_const.matrix_mulVec continuous_snd))
  exact (hK i).1.preimage hc

open Classical in
/-- Under (N), every point lying in some confidence set has an index `i` whose antecedent set
is exactly the set of confidence sets containing the point. -/
lemma exists_anc_eq {nP nQ nK nI : ℕ} (d : AmbData nP nQ nK nI) (hN : Nesting d)
    (ω : (Fin nP → ℝ) × (Fin nQ → ℝ)) (j0 : Fin (nI + 1)) (hj0 : ω ∈ d.conf j0) :
    ∃ i, ω ∈ d.conf i ∧ anc d i = Finset.univ.filter (fun j => ω ∈ d.conf j) := by
  set S := Finset.univ.filter (fun j => ω ∈ d.conf j) with hS
  let down : Fin (nI + 1) → Finset (Fin (nI + 1)) := fun i =>
    S.filter (fun m => SInc (d.conf m) (d.conf i) ∧ ¬ SInc (d.conf i) (d.conf m))
  obtain ⟨i, hiS, hmin⟩ := S.exists_min_image (fun i => (down i).card)
    ⟨j0, by simp [hS, hj0]⟩
  have hωi : ω ∈ d.conf i := by simpa [hS] using hiS
  have key : ∀ k ∈ S, SInc (d.conf k) (d.conf i) → SInc (d.conf i) (d.conf k) := by
    intro k hk hki
    by_contra hik
    have hsub : down k ⊆ down i := by
      intro m hm
      simp only [down, Finset.mem_filter] at hm ⊢
      exact ⟨hm.1, sinc_trans hm.2.1 hki, fun h => hik (sinc_trans h hm.2.1)⟩
    have hlt : (down k).card < (down i).card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset hsub]
      refine ⟨k, ?_, ?_⟩
      · simp only [down, Finset.mem_filter]; exact ⟨hk, hki, hik⟩
      · simp only [down, Finset.mem_filter]; exact fun h => h.2.2 h.2.1
    exact absurd (hmin k hk) (not_le.mpr hlt)
  refine ⟨i, hωi, ?_⟩
  ext j
  simp only [anc, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, hS]
  constructor
  · rintro (rfl | hj)
    · exact hωi
    · exact interior_subset (hj hωi)
  · intro hj
    by_cases hji : j = i
    · exact Or.inl hji
    right
    rcases hN i j (Ne.symm hji) with h | h | h
    · exact h
    · exact key j (by simp [hS, hj]) h
    · exact absurd (Set.disjoint_left.mp h hωi) (not_not.mpr hj)

lemma nontriv {nP nQ : ℕ} (hdim : 0 < nP + nQ) : Nontrivial ((Fin nP → ℝ) × (Fin nQ → ℝ)) := by
  rcases Nat.eq_zero_or_pos nP with hP | hP
  · have hQ : 0 < nQ := by omega
    refine nontrivial_of_ne (0, 0) (0, fun _ => 1) fun h => ?_
    have := congrFun (congrArg Prod.snd h) ⟨0, hQ⟩
    simp at this
  · refine nontrivial_of_ne (0, 0) (fun _ => 1, 0) fun h => ?_
    have := congrFun (congrArg Prod.fst h) ⟨0, hP⟩
    simp at this

/-- A nonempty confidence set inside the bounded `C_I` is not strictly included in itself. -/
lemma not_sinc_self {nP nQ nK nI : ℕ} (d : AmbData nP nQ nK nI)
    (hK : ∀ i, IsProperCone (d.K i)) (hbdd : Bornology.IsBounded (d.conf (Fin.last nI)))
    (hsub : ∀ i, d.conf i ⊆ d.conf (Fin.last nI)) (hdim : 0 < nP + nQ) (i : Fin (nI + 1))
    (ω : (Fin nP → ℝ) × (Fin nQ → ℝ)) (hω : ω ∈ d.conf i) : ¬ SInc (d.conf i) (d.conf i) := by
  intro h
  haveI := nontriv hdim
  have hopen : IsOpen (d.conf i) := by
    have : interior (d.conf i) = d.conf i := interior_subset.antisymm h
    rw [← this]; exact isOpen_interior
  have hcl : IsClopen (d.conf i) := ⟨conf_closed d hK i, hopen⟩
  rcases isClopen_iff.mp hcl with h0 | h0
  · rw [h0] at hω; exact hω
  · have : Bornology.IsBounded (Set.univ : Set ((Fin nP → ℝ) × (Fin nQ → ℝ))) :=
      hbdd.subset (h0 ▸ hsub i)
    exact NormedSpace.unbounded_univ ℝ _ this

end DRCOPartAux

open DRCOPartAux in
theorem solution {nP nQ nK nI nN nL : ℕ} [NeZero nL]
    (d : AmbData nP nQ nK nI) (v : PWAff nN nP nL)
    (hK : ∀ i, IsProperCone (d.K i))
    (hbdd : Bornology.IsBounded (d.conf (Fin.last nI)))
    (hN : Nesting d) (hsub : ∀ i, d.conf i ⊆ d.conf (Fin.last nI)) (hdim : 0 < nP + nQ)
    (x : Fin nN → ℝ) (β : Fin nK → ℝ) (κ lam : Fin (nI + 1) → ℝ) :
    (∀ ω ∈ d.conf (Fin.last nI),
        v.eval x ω.1 ≤ (d.A *ᵥ ω.1 + d.B *ᵥ ω.2) ⬝ᵥ β +
          ∑ i, (d.conf i).indicator (fun _ => (1 : ℝ)) ω * (κ i - lam i)) ↔
    ∀ i, ∀ ω ∈ cbar d i,
      v.eval x ω.1 ≤ (d.A *ᵥ ω.1 + d.B *ᵥ ω.2) ⬝ᵥ β + ∑ i' ∈ anc d i, (κ i' - lam i') := by
  classical
  have hsum : ∀ (i : Fin (nI + 1)) (ω : (Fin nP → ℝ) × (Fin nQ → ℝ)),
      anc d i = Finset.univ.filter (fun j => ω ∈ d.conf j) →
      ∑ j, (d.conf j).indicator (fun _ => (1 : ℝ)) ω * (κ j - lam j) =
        ∑ i' ∈ anc d i, (κ i' - lam i') := by
    intro i ω hanc
    rw [hanc, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : ω ∈ d.conf j <;> simp [hj]
  constructor
  · intro h i ω hω
    obtain ⟨hωi, hωd⟩ := hω
    simp only [Set.mem_iUnion, not_exists] at hωd
    have hanc : anc d i = Finset.univ.filter (fun j => ω ∈ d.conf j) := by
      ext j
      simp only [anc, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (rfl | hj)
        · exact hωi
        · exact interior_subset (hj hωi)
      · intro hj
        by_cases hji : j = i
        · exact Or.inl hji
        right
        rcases hN i j (Ne.symm hji) with h' | h' | h'
        · exact h'
        · exact absurd hj (hωd j (by simp [desc, h']))
        · exact absurd (Set.disjoint_left.mp h' hωi) (not_not.mpr hj)
    rw [← hsum i ω hanc]
    exact h ω (hsub i hωi)
  · intro h ω hω
    obtain ⟨i, hωi, hanc⟩ := exists_anc_eq d hN ω _ hω
    rw [hsum i ω hanc]
    refine h i ω ⟨hωi, ?_⟩
    simp only [Set.mem_iUnion, not_exists]
    intro k hk hωk
    have hki : SInc (d.conf k) (d.conf i) := by simpa [desc] using hk
    have hk' : k ∈ anc d i := by rw [hanc]; simp [hωk]
    simp only [anc, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hk'
    apply not_sinc_self d hK hbdd hsub hdim i ω hωi
    rcases hk' with rfl | hik
    · exact hki
    · exact sinc_trans hik hki
