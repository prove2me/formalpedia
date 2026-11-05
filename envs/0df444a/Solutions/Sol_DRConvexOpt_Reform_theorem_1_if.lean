-- Prove2me | solution 1 for DRConvexOpt.Reform.theorem_1_if
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T12:02:40.354743+00:00
-- url     : https://prove2.me/submissions/4d737b1e-7323-478e-87aa-5b9c911557e5

import Mathlib
import Definitions.Def_DRConvexOpt_Reform_Setting

open MeasureTheory Matrix DRConvexOpt.Reform

namespace DRCOIfAux

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

lemma pointwise {nP nQ nK nI nN nL : ℕ} [NeZero nL]
    (d : AmbData nP nQ nK nI) (v : PWAff nN nP nL) (hN : Nesting d) (x : Fin nN → ℝ)
    (β : Fin nK → ℝ) (κ lam : Fin (nI + 1) → ℝ)
    (φ : (i : Fin (nI + 1)) → Fin nL → Fin (d.L i) → ℝ)
    (hφK : ∀ i l, φ i l ∈ dualCone (d.K i))
    (hsys : ∀ i l, d.c i ⬝ᵥ φ i l + v.s l ⬝ᵥ x + v.t0 l ≤ ∑ i' ∈ anc d i, (κ i' - lam i') ∧
        (d.C i)ᵀ *ᵥ φ i l + d.Aᵀ *ᵥ β = (v.S l)ᵀ *ᵥ x + v.tv l ∧
        (d.D i)ᵀ *ᵥ φ i l + d.Bᵀ *ᵥ β = 0)
    (ω : (Fin nP → ℝ) × (Fin nQ → ℝ)) (j0 : Fin (nI + 1)) (hj0 : ω ∈ d.conf j0) :
    v.eval x ω.1 ≤ (d.A *ᵥ ω.1 + d.B *ᵥ ω.2) ⬝ᵥ β +
      ∑ j, (d.conf j).indicator (fun _ => (1 : ℝ)) ω * (κ j - lam j) := by
  classical
  obtain ⟨i, hωi, hanc⟩ := exists_anc_eq d hN ω j0 hj0
  have hsum : ∑ j, (d.conf j).indicator (fun _ => (1 : ℝ)) ω * (κ j - lam j) =
      ∑ i' ∈ anc d i, (κ i' - lam i') := by
    rw [hanc, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : ω ∈ d.conf j <;> simp [hj]
  rw [hsum]
  unfold PWAff.eval
  refine Finset.sup'_le _ _ fun l _ => ?_
  obtain ⟨h1, h2, h3⟩ := hsys i l
  have hd := hφK i l _ hωi
  have e2 := congrArg (· ⬝ᵥ ω.1) h2
  have e3 := congrArg (· ⬝ᵥ ω.2) h3
  simp only [add_dotProduct, tdot, zero_dotProduct] at e2 e3
  simp only [sub_dotProduct, add_dotProduct] at hd
  simp only [add_dotProduct]
  linarith

/-- the linear functional `y ↦ y ⬝ᵥ a` -/
def dotL {n : ℕ} (a : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun y := y ⬝ᵥ a
  map_add' y z := add_dotProduct y z a
  map_smul' r y := by simp [smul_dotProduct]

end DRCOIfAux

open DRCOIfAux in
theorem solution {nP nQ nK nI nN nL : ℕ} [NeZero nL]
    (d : AmbData nP nQ nK nI) (v : PWAff nN nP nL)
    (hK : ∀ i, IsProperCone (d.K i))
    (hC1 : Bornology.IsBounded (d.conf (Fin.last nI)) ∧ d.plo (Fin.last nI) = 1 ∧
      d.phi (Fin.last nI) = 1)
    (hN : Nesting d) (x : Fin nN → ℝ) (w : ℝ) :
    (∃ (β : Fin nK → ℝ) (κ lam : Fin (nI + 1) → ℝ)
      (φ : (i : Fin (nI + 1)) → Fin nL → Fin (d.L i) → ℝ),
      (∀ i, 0 ≤ κ i) ∧ (∀ i, 0 ≤ lam i) ∧ (∀ i l, φ i l ∈ dualCone (d.K i)) ∧
      d.b ⬝ᵥ β + ∑ i, (d.phi i * κ i - d.plo i * lam i) ≤ w ∧
      ∀ i l, d.c i ⬝ᵥ φ i l + v.s l ⬝ᵥ x + v.t0 l ≤ ∑ i' ∈ anc d i, (κ i' - lam i') ∧
        (d.C i)ᵀ *ᵥ φ i l + d.Aᵀ *ᵥ β = (v.S l)ᵀ *ᵥ x + v.tv l ∧
        (d.D i)ᵀ *ᵥ φ i l + d.Bᵀ *ᵥ β = 0) →
    ∀ μ ∈ ambiguitySet d, ∫ ω, v.eval x ω.1 ∂μ ≤ w := by
  rintro ⟨β, κ, lam, φ, hκ, hlam, hφK, hobj, hsys⟩ μ ⟨hprob, hint, hmean, hconf⟩
  have hmeas : ∀ i, MeasurableSet (d.conf i) := fun i => (conf_closed d hK i).measurableSet
  have hCI : μ (d.conf (Fin.last nI)) = 1 := by
    have h := hconf (Fin.last nI)
    rw [hC1.2.1, hC1.2.2] at h
    have h1 : μ.real (d.conf (Fin.last nI)) = 1 := le_antisymm h.2 h.1
    exact (ENNReal.toReal_eq_one_iff _).mp h1
  have hae : ∀ᵐ ω ∂μ, ω ∈ d.conf (Fin.last nI) :=
    mem_ae_iff.mpr ((prob_compl_eq_zero_iff (hmeas _)).mpr hCI)
  -- the linear part `(Az + Bu)ᵀβ`
  let Lg : ((Fin nP → ℝ) × (Fin nQ → ℝ)) →ₗ[ℝ] (Fin nK → ℝ) :=
    d.A.mulVecLin ∘ₗ LinearMap.fst ℝ _ _ + d.B.mulVecLin ∘ₗ LinearMap.snd ℝ _ _
  have hLg : ∀ ω, Lg ω = d.A *ᵥ ω.1 + d.B *ᵥ ω.2 := fun ω => rfl
  let L := (dotL β ∘ₗ Lg).toContinuousLinearMap
  have hL : ∀ ω, L ω = (d.A *ᵥ ω.1 + d.B *ᵥ ω.2) ⬝ᵥ β := fun ω => rfl
  have hLint : Integrable (fun ω => L ω) μ := L.integrable_comp hint
  have hLmean : ∫ ω, L ω ∂μ = d.b ⬝ᵥ β := by
    rw [L.integral_comp_comm hint]
    have hG : ∫ ω, (d.A *ᵥ ω.1 + d.B *ᵥ ω.2) ∂μ = Lg.toContinuousLinearMap (∫ ω, ω ∂μ) := by
      rw [← ContinuousLinearMap.integral_comp_comm _ hint]; rfl
    rw [hmean] at hG
    show dotL β (Lg (∫ ω, ω ∂μ)) = _
    rw [show Lg (∫ ω, ω ∂μ) = d.b from hG.symm]
    rfl
  -- the indicator part
  have hind : ∀ j ω, (d.conf j).indicator (fun _ => (1 : ℝ)) ω * (κ j - lam j) =
      (d.conf j).indicator (fun _ => κ j - lam j) ω := by
    intro j ω; by_cases h : ω ∈ d.conf j <;> simp [h]
  have hFint : ∀ j, Integrable (fun ω => (d.conf j).indicator (fun _ => (1 : ℝ)) ω *
      (κ j - lam j)) μ := by
    intro j; simp_rw [hind]; exact (integrable_const _).indicator (hmeas j)
  -- integrability of `v`
  have hvl : ∀ l, Integrable (fun ω : (Fin nP → ℝ) × (Fin nQ → ℝ) =>
      (v.S l *ᵥ ω.1 + v.s l) ⬝ᵥ x + (v.tv l ⬝ᵥ ω.1 + v.t0 l)) μ := by
    intro l
    let Ll : ((Fin nP → ℝ) × (Fin nQ → ℝ)) →ₗ[ℝ] ℝ :=
      (dotL x ∘ₗ (v.S l).mulVecLin + dotL (v.tv l)) ∘ₗ LinearMap.fst ℝ _ _
    have h := (Ll.toContinuousLinearMap.integrable_comp hint).add
      (integrable_const (v.s l ⬝ᵥ x + v.t0 l))
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp only [LinearMap.coe_toContinuousLinearMap', Ll, LinearMap.comp_apply,
      LinearMap.add_apply, LinearMap.fst_apply, dotL, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.mulVecLin_apply, add_dotProduct]
    simp only [Pi.add_apply]
    rw [dotProduct_comm ω.1]
    ring
  have hvint : Integrable (fun ω : (Fin nP → ℝ) × (Fin nQ → ℝ) => v.eval x ω.1) μ := by
    have : (fun ω : (Fin nP → ℝ) × (Fin nQ → ℝ) => v.eval x ω.1) =
        Finset.univ.sup' Finset.univ_nonempty (fun l => fun ω : (Fin nP → ℝ) × (Fin nQ → ℝ) =>
          (v.S l *ᵥ ω.1 + v.s l) ⬝ᵥ x + (v.tv l ⬝ᵥ ω.1 + v.t0 l)) := by
      funext ω; rw [Finset.sup'_apply]; rfl
    rw [this]
    exact Finset.sup'_induction (p := fun f => Integrable f μ) _ _
      (fun a ha b hb => Integrable.sup ha hb) fun l _ => hvl l
  calc ∫ ω, v.eval x ω.1 ∂μ
      ≤ ∫ ω, (L ω + ∑ j, (d.conf j).indicator (fun _ => (1 : ℝ)) ω * (κ j - lam j)) ∂μ := by
        refine integral_mono_ae hvint (hLint.add (integrable_finsetSum _ fun j _ => hFint j)) ?_
        filter_upwards [hae] with ω hω
        rw [hL]
        exact pointwise d v hN x β κ lam φ hφK hsys ω _ hω
    _ = d.b ⬝ᵥ β + ∑ j, μ.real (d.conf j) * (κ j - lam j) := by
        rw [integral_add hLint (integrable_finsetSum _ fun j _ => hFint j), hLmean,
          integral_finsetSum _ fun j _ => hFint j]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        simp_rw [hind]
        rw [integral_indicator_const _ (hmeas j), smul_eq_mul]
    _ ≤ d.b ⬝ᵥ β + ∑ i, (d.phi i * κ i - d.plo i * lam i) := by
        gcongr with j
        have h := hconf j
        nlinarith [mul_le_mul_of_nonneg_right h.2 (hκ j), mul_le_mul_of_nonneg_right h.1 (hlam j)]
    _ ≤ w := hobj
