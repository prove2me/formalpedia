-- Prove2me | solution 1 for ContinuousLinearMap.exists_ordered_positive_eigenbasis
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T03:51:16.068005+00:00
-- url     : https://prove2.me/submissions/d60d5d0f-2465-4518-b9d2-0cfd82aa3a6a

import Mathlib

namespace EB104

open Filter Topology

/-- An infinite type with a positive weight whose superlevel sets are finite can be enumerated
by `ℕ` with antitone weights. -/
theorem exists_antitone_enum {ι : Type*} [Infinite ι] (f : ι → ℝ)
    (hfin : ∀ ε > 0, {i | ε ≤ f i}.Finite) (hpos : ∀ i, 0 < f i) :
    ∃ e : ℕ ≃ ι, Antitone (f ∘ e) := by
  classical
  have hcount : Countable ι := by
    have : (Set.univ : Set ι) = ⋃ n : ℕ, {i | 1 / ((n : ℝ) + 1) ≤ f i} := by
      ext i
      simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hpos i)
      exact ⟨n, hn.le⟩
    rw [← Set.countable_univ_iff, this]
    exact Set.countable_iUnion fun n => (hfin _ (by positivity)).countable
  obtain ⟨g, hg⟩ := exists_injective_nat ι
  -- strict order: `j ≺ i`
  let R : ι → ι → Prop := fun j i => f i < f j ∨ (f j = f i ∧ g j < g i)
  let S : ι → Set ι := fun i => {j | R j i}
  have hSfin : ∀ i, (S i).Finite := fun i =>
    (hfin (f i) (hpos i)).subset fun j hj => by
      rcases hj with h | h
      · exact h.le
      · exact h.1.symm.le
  let r : ι → ℕ := fun i => (hSfin i).toFinset.card
  have htrans : ∀ a b c, R a b → R b c → R a c := by
    intro a b c h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact Or.inl (h2.trans h1)
    · exact Or.inl (h2.1 ▸ h1)
    · exact Or.inl (h1.1 ▸ h2)
    · exact Or.inr ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
  have hirr : ∀ a, ¬ R a a := by
    intro a h
    rcases h with h | h
    · exact lt_irrefl _ h
    · exact lt_irrefl _ h.2
  have hmono : ∀ j i, R j i → r j < r i := by
    intro j i hji
    apply Finset.card_lt_card
    rw [Set.Finite.toFinset_ssubset_toFinset]
    refine ⟨fun a ha => htrans a j i ha hji, fun h => hirr j (h hji)⟩
  have htri : ∀ i j, i ≠ j → R i j ∨ R j i := by
    intro i j hij
    rcases lt_trichotomy (f i) (f j) with h | h | h
    · exact Or.inr (Or.inl h)
    · rcases lt_trichotomy (g i) (g j) with h' | h' | h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact absurd (hg h') hij
      · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
    · exact Or.inl (Or.inl h)
  have hr : Function.Injective r := by
    intro i j hij
    by_contra hne
    rcases htri i j hne with h | h
    · exact absurd hij (hmono _ _ h).ne
    · exact absurd hij (hmono _ _ h).ne'
  haveI : Infinite (Set.range r) := Set.infinite_range_of_injective hr |>.to_subtype
  let o := Nat.Subtype.orderIsoOfNat (Set.range r)
  let e : ℕ ≃ ι := o.toEquiv.trans (Equiv.ofInjective r hr).symm
  have hre : ∀ k, r (e k) = (o k : ℕ) := by
    intro k
    simp only [e, Equiv.trans_apply]
    exact Equiv.apply_ofInjective_symm hr _
  refine ⟨e, fun k l hkl => ?_⟩
  rcases hkl.lt_or_eq with hkl | rfl
  · have h1 : r (e k) < r (e l) := by
      rw [hre, hre]
      exact o.strictMono hkl
    have hne : e k ≠ e l := fun h => h1.ne (congrArg r h)
    rcases htri (e k) (e l) hne with h | h
    · rcases h with h | h
      · exact h.le
      · exact h.1.symm.le
    · exact absurd (hmono _ _ h) (not_lt.mpr h1.le)
  · exact le_rfl

end EB104

namespace EB104

open Filter Topology Module End

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem fd_eigenspace (K : E →L[ℝ] E) (hc : IsCompactOperator K)
    (hp : ∀ x : E, x ≠ 0 → 0 < inner ℝ (K x) x) (μ : ℝ) :
    FiniteDimensional ℝ (eigenspace (K : E →ₗ[ℝ] E) μ) := by
  by_cases hμ : μ = 0
  · subst hμ
    have : eigenspace (K : E →ₗ[ℝ] E) 0 = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [mem_eigenspace_iff, zero_smul] at hx
      by_contra h
      have := hp x h
      rw [show K x = 0 from hx, inner_zero_left] at this
      exact lt_irrefl _ this
    rw [this]
    infer_instance
  · exact K.finite_dimensional_eigenspace hc μ hμ

/-- Orthonormal vectors with `‖K v‖ ≥ ε` (`K v = μ v`) are finite in number. -/
theorem finite_large (K : E →L[ℝ] E) (hc : IsCompactOperator K) {ι : Type*} (v : ι → E)
    (hv : Orthonormal ℝ v) (f : ι → ℝ) (hf : ∀ i, K (v i) = f i • v i) (ε : ℝ) (hε : 0 < ε) :
    {i | ε ≤ f i}.Finite := by
  by_contra hinf
  have hinf' : Infinite {i | ε ≤ f i} := Set.infinite_coe_iff.mpr hinf
  obtain ⟨s, hs⟩ : ∃ s : ℕ → {i | ε ≤ f i}, Function.Injective s :=
    ⟨_, (Infinite.natEmbedding _).injective⟩
  let u : ℕ → E := fun n => K (v (s n))
  have hu : ∀ n, u n ∈ closure (K '' Metric.closedBall 0 1) := fun n =>
    subset_closure ⟨v (s n), by simp [hv.1], rfl⟩
  obtain ⟨a, -, φ, hφ, hlim⟩ := (hc.isCompact_closure_image_closedBall 1).tendsto_subseq hu
  have hcau := hlim.cauchySeq
  rw [Metric.cauchySeq_iff'] at hcau
  obtain ⟨N, hN⟩ := hcau ε hε
  have hne : (s (φ (N + 1)) : ι) ≠ s (φ N) := by
    intro h
    exact (hφ (Nat.lt_succ_self N)).ne' (hs (Subtype.ext h))
  have key : dist (u (φ (N + 1))) (u (φ N)) ^ 2 =
      f (s (φ (N + 1))) ^ 2 + f (s (φ N)) ^ 2 := by
    simp only [u, hf, dist_eq_norm]
    rw [@norm_sub_sq_real, norm_smul, norm_smul, hv.1, hv.1, real_inner_smul_left,
      real_inner_smul_right, hv.2 hne]
    simp [sq_abs]
  have h1 := hN (N + 1) (Nat.le_succ N)
  have hA : ε ≤ f (s (φ (N + 1))) := (s (φ (N + 1))).2
  have hB : ε ≤ f (s (φ N)) := (s (φ N)).2
  have hd := dist_nonneg (x := u (φ (N + 1))) (y := u (φ N))
  change dist (u (φ (N + 1))) (u (φ N)) < ε at h1
  nlinarith [mul_le_mul hA hA hε.le (hε.le.trans hA), mul_le_mul hB hB hε.le (hε.le.trans hB),
    mul_lt_mul'' h1 h1 hd hd]

theorem main (hinf : ¬ FiniteDimensional ℝ E) (K : E →L[ℝ] E) (hc : IsCompactOperator K)
    (hs : (K : E →ₗ[ℝ] E).IsSymmetric)
    (hp : ∀ x : E, x ≠ 0 → 0 < inner ℝ (K x) x)
    (enum : ∀ {ι : Type} [Infinite ι] (f : ι → ℝ), (∀ ε > 0, {i | ε ≤ f i}.Finite) →
      (∀ i, 0 < f i) → ∃ e : ℕ ≃ ι, Antitone (f ∘ e)) :
    ∃ (κ : ℕ → ℝ) (b : HilbertBasis ℕ ℝ E),
      (∀ k, 0 < κ k) ∧ Antitone κ ∧ Tendsto κ atTop (𝓝 0) ∧
      ∀ k, K (b k) = κ k • b k := by
  classical
  let V : ℝ → Submodule ℝ E := fun μ => eigenspace (K : E →ₗ[ℝ] E) μ
  have hfd := fd_eigenspace K hc hp
  let n : ℝ → ℕ := fun μ => finrank ℝ (V μ)
  let ob : ∀ μ, OrthonormalBasis (Fin (n μ)) ℝ (V μ) := fun μ =>
    haveI := hfd μ; stdOrthonormalBasis ℝ (V μ)
  let v : (Σ μ : ℝ, Fin (n μ)) → E := fun a => (ob a.1 a.2 : E)
  have hon : Orthonormal ℝ v :=
    (hs.orthogonalFamily_eigenspaces).orthonormal_sigma_orthonormal (fun μ => (ob μ).orthonormal)
  let f : (Σ μ : ℝ, Fin (n μ)) → ℝ := fun a => a.1
  have hf : ∀ a, K (v a) = f a • v a := fun a => by
    have := (ob a.1 a.2).2
    rw [mem_eigenspace_iff] at this
    exact this
  have hle : (⨆ μ, eigenspace (K : E →ₗ[ℝ] E) μ) ≤ Submodule.span ℝ (Set.range v) := by
    refine iSup_le fun μ x hx => ?_
    have hx' : (⟨x, hx⟩ : V μ) = ∑ i, inner ℝ (ob μ i) (⟨x, hx⟩ : V μ) • ob μ i :=
      ((ob μ).sum_repr' _).symm
    have : x = ∑ i, inner ℝ (ob μ i) (⟨x, hx⟩ : V μ) • (ob μ i : E) := by
      have := congrArg Subtype.val hx'
      simpa using this
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨μ, i⟩, rfl⟩)
  have hsp : (Submodule.span ℝ (Set.range v))ᗮ = ⊥ := by
    rw [eq_bot_iff, ← K.orthogonalComplement_iSup_eigenspaces_eq_bot hc hs]
    exact Submodule.orthogonal_le hle
  let b0 := HilbertBasis.mkOfOrthogonalEqBot hon hsp
  have hb0 : ⇑b0 = v := HilbertBasis.coe_mkOfOrthogonalEqBot hon hsp
  haveI : Infinite (Σ μ : ℝ, Fin (n μ)) := by
    by_contra h
    rw [not_infinite_iff_finite] at h
    haveI := Fintype.ofFinite (Σ μ : ℝ, Fin (n μ))
    exact hinf (Module.Finite.of_basis b0.toOrthonormalBasis.toBasis)
  have hpos : ∀ a, 0 < f a := fun a => by
    have h1 := hp (v a) (hon.ne_zero a)
    rw [hf, real_inner_smul_left, real_inner_self_eq_norm_sq, hon.1, one_pow, mul_one] at h1
    exact h1
  have hfin := finite_large K hc v hon f hf
  obtain ⟨e, he⟩ := enum f hfin hpos
  have hon' : Orthonormal ℝ (v ∘ e) := hon.comp e e.injective
  have hsp' : (Submodule.span ℝ (Set.range (v ∘ e)))ᗮ = ⊥ := by
    rw [e.surjective.range_comp]; exact hsp
  refine ⟨f ∘ e, HilbertBasis.mkOfOrthogonalEqBot hon' hsp', fun k => hpos _, he, ?_, fun k => ?_⟩
  · have hf0 : Tendsto f cofinite (𝓝 0) := by
      rw [tendsto_order]
      refine ⟨fun a ha => Eventually.of_forall fun i => ha.trans (hpos i), fun a ha => ?_⟩
      rw [eventually_cofinite]
      simpa [not_lt] using hfin a ha
    rw [← Nat.cofinite_eq_atTop]
    exact hf0.comp e.injective.tendsto_cofinite
  · rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
    exact hf _

end EB104

open Filter Topology

theorem solution
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (hinf : ¬ FiniteDimensional ℝ E) (K : E →L[ℝ] E) (hc : IsCompactOperator K)
    (hs : (K : E →ₗ[ℝ] E).IsSymmetric)
    (hp : ∀ x : E, x ≠ 0 → 0 < inner ℝ (K x) x) :
    ∃ (κ : ℕ → ℝ) (b : HilbertBasis ℕ ℝ E),
      (∀ k, 0 < κ k) ∧ Antitone κ ∧ Tendsto κ atTop (𝓝 0) ∧
      ∀ k, K (b k) = κ k • b k :=
  EB104.main hinf K hc hs hp (fun f h1 h2 => EB104.exists_antitone_enum f h1 h2)
