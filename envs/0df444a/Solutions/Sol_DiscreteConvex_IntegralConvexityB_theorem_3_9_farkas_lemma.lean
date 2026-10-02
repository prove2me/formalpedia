-- Prove2me | solution 1 for DiscreteConvex.IntegralConvexityB.theorem_3_9_farkas_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T01:54:48.927227+00:00
-- url     : https://prove2.me/submissions/82ba06a7-8297-4008-835c-f6922b6ba8d5

import Mathlib

open Matrix

/-- The finitely generated cone spanned by the columns of `A`. -/
private def fkCone {V W : Type*} [Fintype V] [Fintype W] (A : Matrix W V ℝ) : Set (W → ℝ) :=
  {z | ∃ x : V → ℝ, (∀ j, 0 ≤ x j) ∧ A *ᵥ x = z}

private theorem fkCone_convex {V W : Type*} [Fintype V] [Fintype W] (A : Matrix W V ℝ) :
    Convex ℝ (fkCone A) := by
  rintro z1 ⟨x1, hx1, rfl⟩ z2 ⟨x2, hx2, rfl⟩ a b ha hb hab
  refine ⟨a • x1 + b • x2, fun j => ?_, ?_⟩
  · have h1 := hx1 j
    have h2 := hx2 j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha h1) (mul_nonneg hb h2)
  · rw [mulVec_add, mulVec_smul, mulVec_smul]

private theorem fkCone_smul {V W : Type*} [Fintype V] [Fintype W] (A : Matrix W V ℝ)
    {t : ℝ} (ht : 0 ≤ t) {z : W → ℝ} (hz : z ∈ fkCone A) : t • z ∈ fkCone A := by
  obtain ⟨x, hx, rfl⟩ := hz
  refine ⟨t • x, fun j => ?_, ?_⟩
  · simpa using mul_nonneg ht (hx j)
  · rw [mulVec_smul]

private theorem fkCone_zero {V W : Type*} [Fintype V] [Fintype W] (A : Matrix W V ℝ) :
    (0 : W → ℝ) ∈ fkCone A := ⟨0, fun _ => le_rfl, by simp⟩

private theorem fkCone_col {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    (A : Matrix W V ℝ) (j : V) : Aᵀ j ∈ fkCone A := by
  refine ⟨Pi.single j 1, fun k => ?_, ?_⟩
  · rcases eq_or_ne k j with rfl | hk
    · simp
    · simp [Pi.single_apply, hk]
  · ext w
    simp [mulVec, dotProduct, Pi.single_apply, Matrix.transpose_apply]

/-- Support reduction (conic Carathéodory): a nonnegative representation can be thinned out
until the columns in its support are linearly independent. -/
private theorem fk_reduce {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    (A : Matrix W V ℝ) (z : W → ℝ) :
    ∀ k : ℕ, ∀ x : V → ℝ, (∀ j, 0 ≤ x j) → A *ᵥ x = z →
      (Finset.univ.filter fun j => x j ≠ 0).card ≤ k →
      ∃ x' : V → ℝ, (∀ j, 0 ≤ x' j) ∧ A *ᵥ x' = z ∧
        LinearIndependent ℝ fun j : ↥(Finset.univ.filter fun j => x' j ≠ 0) => Aᵀ (j : V) := by
  intro k
  induction k with
  | zero =>
    intro x hx hAx hcard
    have hemp : (Finset.univ.filter fun j => x j ≠ 0) = ∅ := by
      rw [← Finset.card_eq_zero]; omega
    haveI : IsEmpty ↥(Finset.univ.filter fun j => x j ≠ 0) :=
      Finset.isEmpty_coe_sort.mpr hemp
    exact ⟨x, hx, hAx, linearIndependent_empty_type⟩
  | succ k ih =>
    intro x hx hAx hcard
    by_cases hli :
        LinearIndependent ℝ fun j : ↥(Finset.univ.filter fun j => x j ≠ 0) => Aᵀ (j : V)
    · exact ⟨x, hx, hAx, hli⟩
    obtain ⟨gg, hsum, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hli
    -- extend `gg` by zero
    set lamr : V → ℝ := fun j =>
      if h : j ∈ (Finset.univ.filter fun j => x j ≠ 0) then gg ⟨j, h⟩ else 0 with hlamr
    have hlam_supp : ∀ j, x j = 0 → lamr j = 0 := by
      intro j hj
      rw [hlamr]
      have : j ∉ (Finset.univ.filter fun j => x j ≠ 0) := by simp [hj]
      simp [this]
    have hlamr_val : ∀ (j : V) (h : j ∈ (Finset.univ.filter fun k => x k ≠ 0)),
        lamr j = gg ⟨j, h⟩ := by
      intro j h
      show (if h' : j ∈ (Finset.univ.filter fun k => x k ≠ 0) then gg ⟨j, h'⟩ else 0)
          = gg ⟨j, h⟩
      rw [dif_pos h]
    have hlam_mulVec : A *ᵥ lamr = 0 := by
      ext w
      have h1 : (A *ᵥ lamr) w = ∑ j, A w j * lamr j := rfl
      rw [h1]
      have h2 : ∑ j, A w j * lamr j
          = ∑ j ∈ (Finset.univ.filter fun j => x j ≠ 0), A w j * lamr j := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
        intro j _ hj
        have : lamr j = 0 := by rw [hlamr]; simp [hj]
        rw [this, mul_zero]
      rw [h2, ← Finset.sum_attach (Finset.univ.filter fun j => x j ≠ 0)
        (fun j => A w j * lamr j)]
      have h3 : ∀ j : ↥(Finset.univ.filter fun j => x j ≠ 0),
          A w (j : V) * lamr (j : V) = gg j * Aᵀ (j : V) w := by
        intro j
        rw [hlamr_val (j : V) j.2]
        simp [Matrix.transpose_apply, mul_comm]
      rw [Finset.sum_congr rfl fun j _ => h3 j]
      have h4 := congrFun hsum w
      simpa [Finset.sum_apply] using h4
    have hlam_ne : lamr (i0 : V) ≠ 0 := by
      rw [hlamr_val (i0 : V) i0.2]
      exact hi0
    -- normalise so that some coordinate is positive
    obtain ⟨lam, hlamsupp, hlamz, hlampos⟩ :
        ∃ lam : V → ℝ, (∀ j, x j = 0 → lam j = 0) ∧ A *ᵥ lam = 0 ∧ ∃ j, 0 < lam j := by
      rcases lt_or_gt_of_ne hlam_ne with h | h
      · refine ⟨-lamr, fun j hj => by simp [hlam_supp j hj], ?_, ⟨(i0 : V), by simpa using h⟩⟩
        rw [show ((-lamr : V → ℝ)) = (-1 : ℝ) • lamr by ext j; simp, mulVec_smul,
          hlam_mulVec, smul_zero]
      · exact ⟨lamr, hlam_supp, hlam_mulVec, ⟨(i0 : V), h⟩⟩
    obtain ⟨jp, hjp⟩ := hlampos
    set T := Finset.univ.filter fun j => 0 < lam j with hT
    have hTne : T.Nonempty := ⟨jp, by simp [hT, hjp]⟩
    obtain ⟨j0, hj0T, hj0min⟩ := Finset.exists_min_image T (fun j => x j / lam j) hTne
    have hlamj0 : 0 < lam j0 := by simpa [hT] using hj0T
    have hxj0 : 0 < x j0 := by
      rcases (hx j0).lt_or_eq with h | h
      · exact h
      · exact absurd (hlamsupp j0 h.symm) (ne_of_gt hlamj0)
    set θ := x j0 / lam j0 with hθ
    have hθpos : 0 < θ := div_pos hxj0 hlamj0
    have hkey : ∀ j, 0 < lam j → θ * lam j ≤ x j := by
      intro j hj
      have hjT : j ∈ T := by simp [hT, hj]
      have hle := hj0min j hjT
      rw [hθ]
      exact (le_div_iff₀ hj).mp hle
    refine ih (x - θ • lam) (fun j => ?_) ?_ ?_
    · have hgoal : (x - θ • lam) j = x j - θ * lam j := by simp
      rw [hgoal]
      rcases lt_or_ge 0 (lam j) with h | h
      · linarith [hkey j h]
      · nlinarith [hx j, hθpos, h]
    · rw [mulVec_sub, mulVec_smul, hlamz, smul_zero, sub_zero, hAx]
    · have hsub : (Finset.univ.filter fun j => (x - θ • lam) j ≠ 0)
          ⊆ (Finset.univ.filter fun j => x j ≠ 0).erase j0 := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply,
          Pi.smul_apply, smul_eq_mul] at hj
        refine Finset.mem_erase.mpr ⟨?_, ?_⟩
        · intro hjj
          rw [hjj, hθ] at hj
          apply hj
          rw [div_mul_cancel₀ _ (ne_of_gt hlamj0), sub_self]
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro hxj
          exact hj (by rw [hxj, hlamsupp j hxj, mul_zero, sub_zero])
      have hcard2 := Finset.card_le_card hsub
      have hj0mem : j0 ∈ (Finset.univ.filter fun j => x j ≠ 0) := by
        simp [ne_of_gt hxj0]
      rw [Finset.card_erase_of_mem hj0mem] at hcard2
      omega

private theorem fkCone_closed {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    (A : Matrix W V ℝ) : IsClosed (fkCone A) := by
  classical
  -- the pieces indexed by independent column subsets
  set Ind := {S : Finset V // LinearIndependent ℝ fun j : ↥S => Aᵀ (j : V)} with hInd
  have hpiece : ∀ p : Ind, IsClosed
      {z : W → ℝ | ∃ x : V → ℝ, (∀ j, 0 ≤ x j) ∧ (∀ j ∉ (p : Ind).1, x j = 0) ∧ A *ᵥ x = z} := by
    intro p
    obtain ⟨S, hS⟩ := p
    set ψ : (↥S → ℝ) →ₗ[ℝ] (W → ℝ) :=
      { toFun := fun c => ∑ i : ↥S, c i • Aᵀ (i : V)
        map_add' := by intro c d; simp [add_smul, Finset.sum_add_distrib]
        map_smul' := by intro a c; simp [Finset.smul_sum, smul_smul] } with hψ
    have hker : LinearMap.ker ψ = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro c hc
      have := Fintype.linearIndependent_iff.mp hS c hc
      exact funext this
    have hemb := LinearMap.isClosedEmbedding_of_injective (f := ψ) hker
    have hortho : IsClosed {c : ↥S → ℝ | ∀ i, 0 ≤ c i} := by
      have : {c : ↥S → ℝ | ∀ i, 0 ≤ c i} = ⋂ i : ↥S, {c : ↥S → ℝ | 0 ≤ c i} := by
        ext c; simp
      rw [this]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    have himg := hemb.isClosedMap _ hortho
    have hset : ψ '' {c : ↥S → ℝ | ∀ i, 0 ≤ c i}
        = {z : W → ℝ | ∃ x : V → ℝ, (∀ j, 0 ≤ x j) ∧ (∀ j ∉ S, x j = 0) ∧ A *ᵥ x = z} := by
      ext z
      constructor
      · rintro ⟨c, hc, rfl⟩
        refine ⟨fun j => if h : j ∈ S then c ⟨j, h⟩ else 0, fun j => ?_, fun j hj => by simp [hj],
          ?_⟩
        · by_cases h : j ∈ S
          · simp only [dif_pos h]; exact hc ⟨j, h⟩
          · simp [h]
        · ext w
          show ∑ j, A w j * (if h : j ∈ S then c ⟨j, h⟩ else 0) = _
          rw [← Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => by simp [hj])]
          rw [← Finset.sum_attach S (fun j => A w j * (if h : j ∈ S then c ⟨j, h⟩ else 0))]
          show _ = (∑ i : ↥S, c i • Aᵀ (i : V)) w
          rw [Finset.sum_apply]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [i.2, Matrix.transpose_apply, mul_comm]
      · rintro ⟨x, hx, hoff, rfl⟩
        refine ⟨fun i : ↥S => x (i : V), fun i => hx _, ?_⟩
        ext w
        show (∑ i : ↥S, x (i : V) • Aᵀ (i : V)) w = ∑ j, A w j * x j
        rw [Finset.sum_apply]
        rw [← Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => by rw [hoff j hj, mul_zero])]
        rw [← Finset.sum_attach S (fun j => A w j * x j)]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [Matrix.transpose_apply, mul_comm]
    rw [← hset]
    exact himg
  have hunion : fkCone A = ⋃ p : Ind,
      {z : W → ℝ | ∃ x : V → ℝ, (∀ j, 0 ≤ x j) ∧ (∀ j ∉ (p : Ind).1, x j = 0) ∧ A *ᵥ x = z} := by
    ext z
    constructor
    · rintro ⟨x, hx, hAx⟩
      obtain ⟨x', hx', hAx', hli⟩ :=
        fk_reduce A z (Finset.univ.filter fun j => x j ≠ 0).card x hx hAx le_rfl
      refine Set.mem_iUnion.mpr ⟨⟨_, hli⟩, ⟨x', hx', fun j hj => ?_, hAx'⟩⟩
      by_contra hc
      exact hj (by simp [hc])
    · intro hz
      obtain ⟨p, x, hx, -, hAx⟩ := Set.mem_iUnion.mp hz
      exact ⟨x, hx, hAx⟩
  rw [hunion]
  exact isClosed_iUnion_of_finite hpiece

private theorem fk_farkas {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] (A : Matrix W V ℝ) (b : W → ℝ) :
    (∃ x : V → ℝ, (∀ j, 0 ≤ x j) ∧ A *ᵥ x = b) ↔
      (∀ y : W → ℝ, (∀ j, 0 ≤ vecMul y A j) → 0 ≤ y ⬝ᵥ b) := by
  constructor
  · rintro ⟨x, hx, rfl⟩ y hy
    rw [dotProduct_mulVec]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hy j) (hx j)
  · intro hy
    by_contra hnot
    have hb : b ∈ (fkCone A)ᶜ := by
      intro hc
      exact hnot hc
    obtain ⟨ε, hε, hball⟩ :=
      Metric.isOpen_iff.mp (fkCone_closed A).isOpen_compl b hb
    have hdisj : Disjoint (Metric.ball b ε) (fkCone A) :=
      Set.disjoint_left.mpr fun a ha hk => (hball ha) hk
    obtain ⟨f, u, hfball, hfK⟩ := geometric_hahn_banach_open
      (convex_ball b ε) Metric.isOpen_ball (fkCone_convex A) hdisj
    have hfb : f b < u := hfball b (Metric.mem_ball_self hε)
    have hu0 : u ≤ 0 := by
      have := hfK 0 (fkCone_zero A)
      simpa using this
    have hfnn : ∀ z ∈ fkCone A, 0 ≤ f z := by
      intro z hz
      by_contra hc
      rw [not_le] at hc
      set t := (u - 1) / f z with htdef
      have htpos : 0 < t := by
        rw [htdef]
        apply div_pos_of_neg_of_neg <;> linarith
      have hmem := fkCone_smul A htpos.le hz
      have := hfK _ hmem
      rw [map_smul, smul_eq_mul, htdef] at this
      rw [div_mul_cancel₀ _ (ne_of_lt hc)] at this
      linarith
    have hrep : ∀ v : W → ℝ, f v = v ⬝ᵥ (fun w => f (Pi.single w (1 : ℝ))) := by
      intro v
      have hv : v = ∑ w, v w • (Pi.single w (1 : ℝ)) := by
        ext w'
        simp [Finset.sum_apply, Pi.single_apply]
      have h2 : f v = ∑ w, v w * f (Pi.single w (1 : ℝ)) := by
        conv_lhs => rw [hv]
        rw [map_sum]
        simp only [map_smul, smul_eq_mul]
      rw [h2]
      simp only [dotProduct]
    have hcol : ∀ j, 0 ≤ vecMul (fun w => f (Pi.single w (1 : ℝ))) A j := by
      intro j
      have h1 : vecMul (fun w => f (Pi.single w (1 : ℝ))) A j
          = (Aᵀ j) ⬝ᵥ (fun w => f (Pi.single w (1 : ℝ))) := by
        simp only [vecMul, dotProduct, Matrix.transpose_apply]
        exact Finset.sum_congr rfl fun w _ => by ring
      rw [h1, ← hrep]
      exact hfnn _ (fkCone_col A j)
    have hneg := hy _ hcol
    rw [dotProduct_comm, ← hrep] at hneg
    linarith

theorem solution {V W : Type*} [Fintype V] [Fintype W] (A : Matrix W V ℝ)
    (b : W → ℝ) :
    (∃ x : V → ℝ, (∀ j, 0 ≤ x j) ∧ A.mulVec x = b) ↔
      (∀ y : W → ℝ, (∀ j, 0 ≤ Matrix.vecMul y A j) → 0 ≤ dotProduct y b) := by
  letI : DecidableEq V := Classical.decEq V
  letI : DecidableEq W := Classical.decEq W
  exact fk_farkas A b
