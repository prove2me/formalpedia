-- Prove2me | solution 1 for CloudMWU.Bicriteria.kl_projection_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T13:32:55.504848+00:00
-- url     : https://prove2.me/submissions/a4548202-1eac-4301-a750-65637e7b190f

import Mathlib
import Definitions.Def_CloudMWU_Bicriteria_Model

open Finset CloudMWU.Bicriteria

theorem cmw_kl_simplex_closed (N : ℕ) (ε : ℝ) : IsClosed (truncSimplex N ε) := by
  have h1 : IsClosed {x : Fin N → ℝ | ∑ i, x i = 1} :=
    isClosed_eq (continuous_finset_sum _ (fun i _ => continuous_apply i)) continuous_const
  have h2 : IsClosed {x : Fin N → ℝ | ∀ i, ε / (N : ℝ) ≤ x i} := by
    rw [Set.setOf_forall]
    exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
  have : truncSimplex N ε = {x : Fin N → ℝ | ∑ i, x i = 1} ∩ {x | ∀ i, ε / (N : ℝ) ≤ x i} := by
    ext x; simp [truncSimplex]
  rw [this]; exact h1.inter h2

theorem cmw_kl_exists (N : ℕ) (hN : 2 ≤ N) (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (y : Fin N → ℝ) (hy : ∀ i, 0 < y i) : ∃ x, IsKLProj ε y x := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hεN : 0 < ε / (N : ℝ) := by positivity
  set S := truncSimplex N ε with hS
  have hne : S.Nonempty := by
    refine ⟨fun _ => 1 / (N : ℝ), ?_, ?_⟩
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    · intro i
      apply div_le_div_of_nonneg_right (by linarith) hNpos.le
  have hsub : S ⊆ Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1) := by
    intro x hx
    obtain ⟨hsum, hfl⟩ := hx
    have h0 : ∀ i, 0 ≤ x i := fun i => le_trans hεN.le (hfl i)
    refine ⟨fun i => h0 i, fun i => ?_⟩
    have := Finset.single_le_sum (f := x) (fun j _ => h0 j) (Finset.mem_univ i)
    rw [hsum] at this; exact this
  have hcpt : IsCompact S := isCompact_Icc.of_isClosed_subset (cmw_kl_simplex_closed N ε) hsub
  have hcont : ContinuousOn (fun x => klObj x y) S := by
    unfold klObj
    apply continuousOn_finset_sum
    intro i _
    have hci : Continuous (fun x : Fin N → ℝ => x i) := continuous_apply i
    apply ContinuousOn.mul hci.continuousOn
    apply ContinuousOn.log (hci.continuousOn.div_const (y i))
    intro x hx
    have := lt_of_lt_of_le hεN (hx.2 i)
    exact (div_pos this (hy i)).ne'
  obtain ⟨x, hxS, hxmin⟩ := hcpt.exists_isMinOn hne hcont
  exact ⟨x, hy, hxS, fun x' hx' => hxmin hx'⟩

theorem cmw_kl_unique (N : ℕ) (hN : 2 ≤ N) (ε : ℝ) (hε : 0 < ε)
    (y x1 x2 : Fin N → ℝ) (h1 : IsKLProj ε y x1) (h2 : IsKLProj ε y x2) : x1 = x2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hεN : 0 < ε / (N : ℝ) := by positivity
  obtain ⟨hy, ⟨hs1, hf1⟩, hm1⟩ := h1
  obtain ⟨_, ⟨hs2, hf2⟩, hm2⟩ := h2
  by_contra hne
  have hp1 : ∀ i, 0 < x1 i := fun i => lt_of_lt_of_le hεN (hf1 i)
  have hp2 : ∀ i, 0 < x2 i := fun i => lt_of_lt_of_le hεN (hf2 i)
  set m : Fin N → ℝ := fun i => (x1 i + x2 i) / 2 with hm
  have hmS : m ∈ truncSimplex N ε := by
    refine ⟨?_, fun i => ?_⟩
    · simp only [hm, ← Finset.sum_div, Finset.sum_add_distrib, hs1, hs2]; norm_num
    · simp only [hm]; linarith [hf1 i, hf2 i]
  -- coordinatewise convexity
  have hφ : ∀ i, m i * Real.log (m i / y i)
      ≤ (x1 i * Real.log (x1 i / y i) + x2 i * Real.log (x2 i / y i)) / 2 := by
    intro i
    have hc := Real.strictConvexOn_mul_log.convexOn.2 (Set.mem_Ici.mpr (hp1 i).le)
      (Set.mem_Ici.mpr (hp2 i).le) (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (0:ℝ) ≤ 1 / 2)
      (by norm_num)
    simp only [smul_eq_mul] at hc
    have hmi : 0 < m i := by simp only [hm]; linarith [hp1 i, hp2 i]
    rw [Real.log_div hmi.ne' (hy i).ne', Real.log_div (hp1 i).ne' (hy i).ne',
      Real.log_div (hp2 i).ne' (hy i).ne']
    have e : m i = 1 / 2 * x1 i + 1 / 2 * x2 i := by simp only [hm]; ring
    rw [e]; nlinarith
  obtain ⟨j, hj⟩ : ∃ j, x1 j ≠ x2 j := by
    by_contra hcon; push_neg at hcon; exact hne (funext hcon)
  have hφs : m j * Real.log (m j / y j)
      < (x1 j * Real.log (x1 j / y j) + x2 j * Real.log (x2 j / y j)) / 2 := by
    have hc := Real.strictConvexOn_mul_log.2 (Set.mem_Ici.mpr (hp1 j).le)
      (Set.mem_Ici.mpr (hp2 j).le) hj (by norm_num : (0:ℝ) < 1 / 2) (by norm_num : (0:ℝ) < 1 / 2)
      (by norm_num)
    simp only [smul_eq_mul] at hc
    have hmj : 0 < m j := by simp only [hm]; linarith [hp1 j, hp2 j]
    rw [Real.log_div hmj.ne' (hy j).ne', Real.log_div (hp1 j).ne' (hy j).ne',
      Real.log_div (hp2 j).ne' (hy j).ne']
    have e : m j = 1 / 2 * x1 j + 1 / 2 * x2 j := by simp only [hm]; ring
    rw [e]; nlinarith
  have hlt : klObj m y < (klObj x1 y + klObj x2 y) / 2 := by
    unfold klObj
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_lt_sum (fun i _ => hφ i) ⟨j, Finset.mem_univ _, hφs⟩
  have := hm1 m hmS
  have := hm1 x2 ⟨hs2, hf2⟩
  have := hm2 x1 ⟨hs1, hf1⟩
  linarith

theorem cmw_queue_congr (ℓ : ℕ → ℝ) : ∀ (t : ℕ) (a b : ℕ → ℝ), (∀ τ, τ < t → a τ = b τ) →
    queue a ℓ t = queue b ℓ t := by
  intro t
  induction t with
  | zero => intro a b _; rfl
  | succ t ih =>
    intro a b hab
    simp only [queue]
    rw [ih a b (fun τ hτ => hab τ (by omega)), hab t (by omega)]

/-- joint recursion for allocations and queues -/
noncomputable def cmwState {N : ℕ} (ε η : ℝ) (β : Fin N → ℝ) (L : ℕ → Fin N → ℝ)
    (proj : (Fin N → ℝ) → (Fin N → ℝ)) (h₀ : Fin N → ℝ) :
    ℕ → (Fin N → ℝ) × (Fin N → ℝ)
  | 0 => (h₀, 0)
  | t + 1 =>
    ((proj (boosted ε η β (cmwState ε η β L proj h₀ t).1 (cmwState ε η β L proj h₀ t).2)),
      fun i => max 0 (L t i + (cmwState ε η β L proj h₀ t).2 i - (cmwState ε η β L proj h₀ t).1 i))

theorem solution (N : ℕ) (hN : 2 ≤ N) (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10) :
    (∀ y : Fin N → ℝ, (∀ i, 0 < y i) → ∃! x : Fin N → ℝ, IsKLProj ε y x) ∧
    (∀ (η : ℝ) (β : Fin N → ℝ) (L : ℕ → Fin N → ℝ) (h₀ : Fin N → ℝ), h₀ ∈ truncSimplex N ε →
      ∃! h : ℕ → Fin N → ℝ, h 0 = h₀ ∧ IsAlg1Run ε η β L h) := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hεN : 0 < ε / (N : ℝ) := by positivity
  have part1 : ∀ y : Fin N → ℝ, (∀ i, 0 < y i) → ∃! x : Fin N → ℝ, IsKLProj ε y x := by
    intro y hy
    obtain ⟨x, hx⟩ := cmw_kl_exists N hN ε hε hε' y hy
    exact ⟨x, hx, fun x' hx' => cmw_kl_unique N hN ε hε y x' x hx' hx⟩
  refine ⟨part1, ?_⟩
  intro η β L h₀ hh₀
  let proj : (Fin N → ℝ) → (Fin N → ℝ) := fun y =>
    if hy : ∀ i, 0 < y i then Classical.choose (cmw_kl_exists N hN ε hε hε' y hy) else y
  have hproj : ∀ y, (∀ i, 0 < y i) → IsKLProj ε y (proj y) := by
    intro y hy
    simp only [proj, dif_pos hy]
    exact Classical.choose_spec (cmw_kl_exists N hN ε hε hε' y hy)
  set st := cmwState ε η β L proj h₀ with hst
  set hseq : ℕ → Fin N → ℝ := fun t => (st t).1 with hhseq
  have hq : ∀ t i, runQueue hseq L t i = (st t).2 i := by
    intro t
    induction t with
    | zero => intro i; simp [runQueue, queue, hst, cmwState]
    | succ t ih =>
      intro i
      simp only [runQueue] at ih ⊢
      simp only [queue]
      rw [ih i]
      simp only [hhseq, hst, cmwState]
  have hboost_pos : ∀ (v q : Fin N → ℝ), v ∈ truncSimplex N ε → ∀ i, 0 < boosted ε η β v q i := by
    intro v q hv i
    unfold boosted
    exact mul_pos (lt_of_lt_of_le hεN (hv.2 i)) (Real.exp_pos _)
  have hmem : ∀ t, hseq t ∈ truncSimplex N ε := by
    intro t
    induction t with
    | zero => simpa [hhseq, hst, cmwState] using hh₀
    | succ t ih =>
      have : hseq (t + 1) = proj (boosted ε η β (hseq t) (st t).2) := by
        simp only [hhseq, hst, cmwState]
      rw [this]
      exact (hproj _ (hboost_pos _ _ ih)).2.1
  have hrun : IsAlg1Run ε η β L hseq := by
    refine ⟨hmem 0, fun t => ?_⟩
    have e1 : runQueue hseq L t = (st t).2 := funext (hq t)
    have e2 : hseq (t + 1) = proj (boosted ε η β (hseq t) (st t).2) := by
      simp only [hhseq, hst, cmwState]
    rw [e1, e2]
    exact hproj _ (hboost_pos _ _ (hmem t))
  have h0 : hseq 0 = h₀ := by simp [hhseq, hst, cmwState]
  refine ⟨hseq, ⟨h0, hrun⟩, ?_⟩
  -- uniqueness
  rintro h' ⟨h'0, h'run⟩
  have key : ∀ t, ∀ s ≤ t, h' s = hseq s := by
    intro t
    induction t with
    | zero => intro s hs; rw [Nat.le_zero.mp hs, h'0, h0]
    | succ t ih =>
      intro s hs
      rcases Nat.lt_or_ge s (t + 1) with hlt | hge
      · exact ih s (by omega)
      · have hs' : s = t + 1 := by omega
        rw [hs']
        have hqe : runQueue h' L t = runQueue hseq L t := by
          funext i
          unfold runQueue
          exact cmw_queue_congr _ t _ _ (fun τ hτ => by rw [ih τ (by omega)])
        have hte : h' t = hseq t := ih t le_rfl
        have A := h'run.2 t
        have B := hrun.2 t
        rw [hqe, hte] at A
        exact cmw_kl_unique N hN ε hε _ _ _ A B
  funext t
  exact key t t le_rfl
