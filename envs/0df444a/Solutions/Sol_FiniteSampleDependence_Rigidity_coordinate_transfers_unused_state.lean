-- Prove2me | solution 1 for FiniteSampleDependence.Rigidity.coordinate_transfers_unused_state
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:00:26.210092+00:00
-- url     : https://prove2.me/submissions/85b58825-681b-47d3-916a-cf4b62916fb0

import Mathlib
import Definitions.Def_FiniteSampleDependence_Rigidity_Model
import Theorems.Thm_FiniteSampleDependence_Rigidity_reversible_merging

section
set_option autoImplicit false

namespace FiniteSampleDependence.Dev.Lem32

open FiniteSampleDependence.Rigidity Matrix

lemma merge_apply {n m : ℕ} (i j : Fin n) (hij : i ≠ j) (U : Matrix (Fin n) (Fin m) ℝ)
    (k : Fin n) (α : Fin m) :
    (mergeMatrix i j * U) k α =
      if k = i then U i α + U j α else if k = j then 0 else U k α := by
  simp only [Matrix.mul_apply, mergeMatrix, Matrix.of_apply]
  by_cases hk : k = i
  · subst hk
    simp only [if_true]
    rw [Finset.sum_eq_add_of_mem k j (Finset.mem_univ _) (Finset.mem_univ _) hij]
    · simp [hij.symm, hij]
    · intro l _ hl
      simp [hl.1, hl.2]
  · by_cases hkj : k = j
    · subst hkj
      simp [hk]
    · simp only [hk, hkj, if_false]
      rw [Finset.sum_eq_single k]
      · simp
      · intro l _ hl
        simp [hl]
      · simp

lemma merge_cs {n : ℕ} (i j : Fin n) (hij : i ≠ j) : IsColumnStochastic (mergeMatrix i j) := by
  refine ⟨fun k l => ?_, fun l => ?_⟩
  · simp only [mergeMatrix, Matrix.of_apply]
    split_ifs <;> simp
  · simp only [mergeMatrix, Matrix.of_apply]
    by_cases hl : l = i ∨ l = j
    · rw [Finset.sum_eq_single i]
      · simp [hl]
      · intro k _ hk
        rcases hl with rfl | rfl
        · simp [hk, Ne.symm hk]
        · simp [hk]
          intro h e
          exact h e.symm
      · simp
    · push Not at hl
      rw [Finset.sum_eq_single l]
      · simp [hl.1, hl.2]
      · intro k _ hk
        by_cases hki : k = i
        · simp [hki, hl.1, hl.2]
        · by_cases hkj : k = j
          · simp [hkj, hij.symm]
          · simp [hki, hkj, Ne.symm hk]
      · simp

/-- Direction moving row `i` into row `r` (scaled by `U i`). -/
def Dh {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) (i r : Fin n) : Ambient n m :=
  fun k β => (if k = r then U i β else 0) - (if k = i then U i β else 0)

/-- The path point. -/
def X {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) (i r : Fin n) (α : Fin m) (η t : ℝ) :
    Ambient n m :=
  Matrix.of.symm U + η • Dh U i r + t • (entryDir r α - entryDir i α)

lemma X_apply {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) (i r : Fin n) (hir : i ≠ r) (α : Fin m)
    (η t : ℝ) (k : Fin n) (β : Fin m) :
    X U i r α η t k β =
      U k β + η * ((if k = r then U i β else 0) - (if k = i then U i β else 0))
        + t * ((if k = r ∧ β = α then 1 else 0) - (if k = i ∧ β = α then 1 else 0)) := by
  simp only [X, Dh, entryDir, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    Pi.single_apply]
  by_cases h1 : k = r <;> by_cases h2 : k = i <;> by_cases h3 : β = α <;>
    simp [h1, h2, h3, hir, Ne.symm hir]

lemma tau_W {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) (i r : Fin n) (hir : i ≠ r) (α : Fin m)
    (η t : ℝ) : tau (Matrix.of (X U i r α η t)) = tau U := by
  unfold tau
  simp only [Matrix.of_apply, X_apply U i r hir α η t]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp [Finset.sum_ite_eq, Finset.sum_ite_irrel, ite_and]

lemma W_merge {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) (i r : Fin n) (hir : i ≠ r)
    (hr : ∀ α, U r α = 0) (α : Fin m) (η t : ℝ) :
    mergeMatrix i r * Matrix.of (X U i r α η t) = U := by
  ext k β
  rw [merge_apply i r hir]
  simp only [Matrix.of_apply, X_apply U i r hir α η t]
  by_cases h1 : k = i
  · subst h1
    by_cases h3 : β = α <;> simp [hir, hr, Ne.symm hir, h3] <;> ring
  · by_cases h2 : k = r
    · simp [h2, hr, hir, Ne.symm hir]
    · simp [h1, h2]

lemma W_simplex {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) (hU : U ∈ simplex n m) (i r : Fin n)
    (hir : i ≠ r) (hr : ∀ α, U r α = 0) (α : Fin m) (η t : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (ht1 : -(η * U i α) ≤ t) (ht2 : t ≤ (1 - η) * U i α) :
    Matrix.of (X U i r α η t) ∈ simplex n m := by
  refine ⟨fun k β => ?_, by rw [tau_W U i r hir α η t]; exact hU.2⟩
  have hu : ∀ k β, 0 ≤ U k β := hU.1
  simp only [Matrix.of_apply, X_apply U i r hir α η t]
  by_cases h1 : k = i
  · subst h1
    by_cases h3 : β = α
    · subst h3
      simp [hir, Ne.symm hir]
      nlinarith [hu k β]
    · simp [hir, Ne.symm hir, h3]
      nlinarith [hu k β]
  · by_cases h2 : k = r
    · subst h2
      by_cases h3 : β = α
      · subst h3
        simp [hr, hir, h1]
        nlinarith [hu i β]
      · simp [hr, h3, h1]
        exact mul_nonneg hη0 (hu i β)
    · simp [h1, h2]
      exact hu k β

lemma key {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (F : Matrix (Fin n) (Fin m) ℝ → ℝ) (hF : LFDPI F)
    (U : Matrix (Fin n) (Fin m) ℝ) (hU : U ∈ simplex n m) (r : Fin n)
    (hr : ∀ α, U r α = 0) (hpos : ∀ i α, i ≠ r → 0 < U i α)
    (Ω : Set (Ambient n m)) (G : Ambient n m → ℝ) (hG : IsC1Extension F Ω G)
    (i : Fin n) (hir : i ≠ r) (α : Fin m) :
    fderiv ℝ G (Matrix.of.symm U) (entryDir i α) =
      fderiv ℝ G (Matrix.of.symm U) (entryDir r α) := by
  obtain ⟨hΩo, hΩs, hGC, hGF⟩ := hG
  -- Step 1: for η ∈ (0,1), the derivative identity at X η 0.
  have step : ∀ η : ℝ, 0 < η → η < 1 →
      fderiv ℝ G (X U i r α η 0) (entryDir r α) = fderiv ℝ G (X U i r α η 0) (entryDir i α) := by
    intro η hη0 hη1
    have hUi := hpos i α hir
    have hsimp : ∀ t, -(η * U i α) ≤ t → t ≤ (1 - η) * U i α →
        Matrix.of (X U i r α η t) ∈ simplex n m := fun t h1 h2 =>
      W_simplex U hU i r hir hr α η t hη0.le hη1.le h1 h2
    have hF0 : F (Matrix.of (X U i r α η 0)) = F U := by
      have h := (reversible_merging hn hm F hF i r hir (Matrix.of (X U i r α η 0))
        (hsimp 0 (by nlinarith) (by nlinarith))).2 (1 - η) η (U i) (by linarith) hη0.le
        (fun β => hU.1 i β)
        (by intro β; simp [X_apply U i r hir α η 0, hir]; ring)
        (by intro β; simp [X_apply U i r hir α η 0, hir, Ne.symm hir, hr])
      rw [W_merge U i r hir hr] at h
      exact h.symm
    have hmin : IsLocalMin (fun t : ℝ => G (X U i r α η t)) 0 := by
      have hb : Set.Ioo (-(η * U i α)) ((1 - η) * U i α) ∈ nhds (0:ℝ) :=
        Ioo_mem_nhds (by nlinarith) (by nlinarith)
      filter_upwards [hb] with t ht
      have hs := hsimp t ht.1.le ht.2.le
      have e1 : G (X U i r α η t) = F (Matrix.of (X U i r α η t)) := by
        have := hGF _ hs
        simpa using this
      have e0 : G (X U i r α η 0) = F (Matrix.of (X U i r α η 0)) := by
        have := hGF _ (hsimp 0 (by nlinarith) (by nlinarith))
        simpa using this
      show G (X U i r α η 0) ≤ G (X U i r α η t)
      rw [e1, e0, hF0]
      have := hF _ hs (mergeMatrix i r) (merge_cs i r hir)
      rwa [W_merge U i r hir hr] at this
    have hGd : DifferentiableAt ℝ G (X U i r α η 0) := by
      have hmem : X U i r α η 0 ∈ Ω := by
        have := hΩs _ (hsimp 0 (by nlinarith) (by nlinarith))
        simpa using this
      exact (hGC.differentiableOn one_ne_zero).differentiableAt (hΩo.mem_nhds hmem)
    have hline : HasDerivAt (fun t : ℝ => X U i r α η t) (entryDir r α - entryDir i α) 0 := by
      have : HasDerivAt (fun t : ℝ => t • (entryDir r α - entryDir i α))
          (entryDir r α - entryDir i α) 0 := by
        simpa using (hasDerivAt_id (0:ℝ)).smul_const (entryDir r α - entryDir i α)
      have h2 := this.const_add (Matrix.of.symm U + η • Dh U i r)
      simpa [X, add_assoc] using h2
    have hd := hGd.hasFDerivAt.comp_hasDerivAt (0:ℝ) hline
    have h0 := hmin.hasDerivAt_eq_zero hd
    rw [map_sub] at h0
    exact sub_eq_zero.mp h0
  -- Step 2: the limit η → 0+.
  have hX0 : X U i r α 0 0 = Matrix.of.symm U := by simp [X]
  have hcont : ContinuousAt (fderiv ℝ G) (Matrix.of.symm U) :=
    (hGC.continuousOn_fderiv_of_isOpen hΩo le_rfl).continuousAt (hΩo.mem_nhds (hΩs U hU))
  have hlim : ∀ w : Ambient n m, Filter.Tendsto
      (fun η : ℝ => fderiv ℝ G (X U i r α η 0) w) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (fderiv ℝ G (Matrix.of.symm U) w)) := by
    intro w
    have hc : Continuous (fun η : ℝ => X U i r α η 0) := by
      unfold X
      fun_prop
    have h1 : Filter.Tendsto (fun η : ℝ => X U i r α η 0) (nhds 0) (nhds (Matrix.of.symm U)) := by
      simpa [hX0] using hc.tendsto 0
    have h2 : ContinuousAt (fun x => fderiv ℝ G x w) (Matrix.of.symm U) :=
      hcont.clm_apply continuousAt_const
    exact (h2.tendsto.comp h1).mono_left nhdsWithin_le_nhds
  have hev : (fun η : ℝ => fderiv ℝ G (X U i r α η 0) (entryDir r α)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun η : ℝ => fderiv ℝ G (X U i r α η 0) (entryDir i α)) := by
    have : Set.Ioo (0:ℝ) 1 ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
      Ioo_mem_nhdsGT one_pos
    filter_upwards [this] with η hη using step η hη.1 hη.2
  exact (tendsto_nhds_unique_of_eventuallyEq (hlim _) (hlim _) hev).symm

end FiniteSampleDependence.Dev.Lem32

namespace FiniteSampleDependence.Rigidity

theorem chk_coordinate_transfers_unused_state {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (F : Matrix (Fin n) (Fin m) ℝ → ℝ) (hF : LFDPI F)
    (U : Matrix (Fin n) (Fin m) ℝ) (hU : U ∈ simplex n m) (r : Fin n)
    (hr : ∀ α, U r α = 0) (hpos : ∀ i α, i ≠ r → 0 < U i α)
    (Ω : Set (Ambient n m)) (G : Ambient n m → ℝ) (hG : IsC1Extension F Ω G) :
    ∀ i j : Fin n, i ≠ r → j ≠ r → i ≠ j → ∀ α : Fin m,
      fderiv ℝ G (Matrix.of.symm U) (entryDir i α) =
        fderiv ℝ G (Matrix.of.symm U) (entryDir j α) := by
  intro i j hi hj _ α
  rw [Dev.Lem32.key hn hm F hF U hU r hr hpos Ω G hG i hi α, Dev.Lem32.key hn hm F hF U hU r hr hpos Ω G hG j hj α]


end FiniteSampleDependence.Rigidity

end

theorem solution : type_of% @FiniteSampleDependence.Rigidity.chk_coordinate_transfers_unused_state := @FiniteSampleDependence.Rigidity.chk_coordinate_transfers_unused_state
