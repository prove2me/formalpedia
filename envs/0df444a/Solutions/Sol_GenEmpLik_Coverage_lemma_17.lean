-- Prove2me | solution 1 for GenEmpLik.Coverage.lemma_17
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T02:14:19.765048+00:00
-- url     : https://prove2.me/submissions/04897779-82b7-4d7a-9398-9c1581fc7470

import Mathlib

open Filter Topology

theorem solution {E : Type*} [MetricSpace E]
    (X : Set E) (F H : E → ℝ) (Hn : ℕ → E → ℝ) (t : ℕ → ℝ)
    (hXclosed : IsClosed X) (hXnonempty : X.Nonempty)
    (hFlsc : LowerSemicontinuousOn F X)
    (hsublevel : ∃ ε₀ : ℝ, 0 < ε₀ ∧
      IsCompact {x | x ∈ X ∧ F x ≤ sInf (F '' X) + ε₀} ∧
      Set.Nonempty {x | x ∈ X ∧ F x ≤ sInf (F '' X) + ε₀})
    (hHcont : ContinuousOn H X)
    (hHbdd : BddAbove ((fun x => |H x|) '' X))
    (hHnbdd : ∀ n, BddAbove ((fun x => |Hn n x|) '' X))
    (htpos : ∀ n, 0 < t n) (htzero : Tendsto t atTop (𝓝 0))
    (hHn : Tendsto (fun n => ⨆ x : X, |Hn n x - H x|) atTop (𝓝 0)) :
    Tendsto (fun n =>
      (sInf ((fun x => F x + t n * Hn n x) '' X) - sInf (F '' X)) / t n)
      atTop (𝓝 (sInf (H '' {x | x ∈ X ∧ F x = sInf (F '' X)}))) := by
  obtain ⟨ε₀, hε₀, hKc, hKne⟩ := hsublevel
  set v := sInf (F '' X) with hv
  set K := {x | x ∈ X ∧ F x ≤ v + ε₀} with hK
  -- a minimiser
  obtain ⟨x₀, hx₀K, hx₀min⟩ := (hFlsc.mono (fun x hx => hx.1)).exists_isMinOn hKne hKc
  have hFge : ∀ x ∈ X, F x₀ ≤ F x := by
    intro x hx
    by_cases hxK : F x ≤ v + ε₀
    · exact hx₀min ⟨hx, hxK⟩
    · push Not at hxK; linarith [hx₀K.2]
  have hv0 : v = F x₀ := by
    refine IsLeast.csInf_eq ⟨⟨x₀, hx₀K.1, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩; exact hFge x hx
  have hFv : ∀ x ∈ X, v ≤ F x := fun x hx => hv0 ▸ hFge x hx
  set S := {x | x ∈ X ∧ F x = v} with hS
  have hx₀S : x₀ ∈ S := ⟨hx₀K.1, hv0.symm⟩
  -- bounds
  obtain ⟨CH, hCH⟩ := hHbdd
  have hCH' : ∀ x ∈ X, |H x| ≤ CH := fun x hx => hCH ⟨x, hx, rfl⟩
  have hHS : BddBelow (H '' S) := ⟨-CH, by
    rintro _ ⟨x, hx, rfl⟩; have := hCH' x hx.1; rw [abs_le] at this; linarith⟩
  set m := sInf (H '' S) with hm
  set δ := fun n => ⨆ x : X, |Hn n x - H x| with hδ
  have hδle : ∀ n, ∀ x ∈ X, |Hn n x - H x| ≤ δ n := by
    intro n x hx
    obtain ⟨Bn, hBn⟩ := hHnbdd n
    refine le_ciSup (f := fun x : X => |Hn n x - H x|) ⟨Bn + CH, ?_⟩ ⟨x, hx⟩
    rintro _ ⟨y, rfl⟩
    have h1 := hBn ⟨y, y.2, rfl⟩
    have h2 := hCH' y y.2
    simp only at h1 h2 ⊢
    calc |Hn n y - H y| ≤ |Hn n y| + |H y| := abs_sub _ _
      _ ≤ Bn + CH := add_le_add h1 h2
  have hδ0 : ∀ n, 0 ≤ δ n := fun n => (abs_nonneg _).trans (hδle n x₀ hx₀K.1)
  set V := fun n => sInf ((fun x => F x + t n * Hn n x) '' X) with hV
  have hVbdd : ∀ n, BddBelow ((fun x => F x + t n * Hn n x) '' X) := by
    intro n
    obtain ⟨Bn, hBn⟩ := hHnbdd n
    refine ⟨v - t n * Bn, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have h1 := hBn ⟨x, hx, rfl⟩
    simp only at h1
    rw [abs_le] at h1
    have := hFv x hx
    have := htpos n
    nlinarith [h1.1]
  have hVle : ∀ n, ∀ x ∈ X, V n ≤ F x + t n * Hn n x := fun n x hx =>
    csInf_le (hVbdd n) ⟨x, hx, rfl⟩
  rw [tendsto_order]
  constructor
  · -- lower bound
    intro a ha
    by_contra hcon
    rw [not_eventually] at hcon
    obtain ⟨φ, hφ, hφa⟩ := extraction_of_frequently_atTop hcon
    set η := m - a with hη
    have hηpos : 0 < η := by linarith
    -- near minimisers
    have hex : ∀ n, ∃ x ∈ X, F x + t n * Hn n x < V n + t n * (η / 2) := by
      intro n
      have hlt : V n < V n + t n * (η / 2) := by
        have := htpos n; nlinarith
      obtain ⟨_, ⟨x, hx, rfl⟩, hlt'⟩ := exists_lt_of_csInf_lt
        (hXnonempty.image (fun x => F x + t n * Hn n x)) hlt
      exact ⟨x, hx, hlt'⟩
    choose x hxX hxlt using hex
    -- along the subsequence
    have hk1 : ∀ k, H (x (φ k)) ≤ m - η / 2 + δ (φ k) := by
      intro k
      set n := φ k
      have hD : (V n - v) / t n ≤ a := not_lt.mp (hφa k)
      have htn := htpos n
      rw [div_le_iff₀ htn] at hD
      have h1 := hxlt n
      have h2 := hFv (x n) (hxX n)
      have h3 := hδle n (x n) (hxX n)
      rw [abs_le] at h3
      have : t n * Hn n (x n) < t n * (m - η / 2) := by nlinarith
      have h4 : Hn n (x n) < m - η / 2 := lt_of_mul_lt_mul_left this htn.le
      linarith [h3.1]
    have hk2 : ∀ k, F (x (φ k)) - v ≤ t (φ k) * (m + CH + δ (φ k)) := by
      intro k
      set n := φ k
      have hD : (V n - v) / t n ≤ a := not_lt.mp (hφa k)
      have htn := htpos n
      rw [div_le_iff₀ htn] at hD
      have h1 := hxlt n
      have h3 := hδle n (x n) (hxX n)
      have h5 := hCH' (x n) (hxX n)
      rw [abs_le] at h3 h5
      have : t n * (-(Hn n (x n))) ≤ t n * (CH + δ n) := by
        apply mul_le_mul_of_nonneg_left _ htn.le; linarith [h3.1, h5.1]
      nlinarith
    have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
    have htφ : Tendsto (fun k => t (φ k)) atTop (𝓝 0) := htzero.comp hφt
    have hδφ : Tendsto (fun k => δ (φ k)) atTop (𝓝 0) := hHn.comp hφt
    have hFlim : Tendsto (fun k => F (x (φ k))) atTop (𝓝 v) := by
      have hup : Tendsto (fun k => v + t (φ k) * (m + CH + δ (φ k))) atTop (𝓝 v) := by
        have := (htφ.mul ((tendsto_const_nhds (x := m + CH)).add hδφ)).const_add v
        simpa using this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
        (fun k => hFv _ (hxX _)) (fun k => by linarith [hk2 k])
    -- eventually in K
    have hevK : ∀ᶠ k in atTop, x (φ k) ∈ K := by
      have := hFlim.eventually (gt_mem_nhds (show v < v + ε₀ by linarith))
      filter_upwards [this] with k hk
      exact ⟨hxX _, hk.le⟩
    obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hevK
    obtain ⟨xb, hxbK, ψ, hψ, hψlim⟩ := hKc.tendsto_subseq (x := fun j => x (φ (j + k₀)))
      (fun j => hk₀ _ (by omega))
    have hxbX : xb ∈ X := hxbK.1
    set N := fun j => φ (ψ j + k₀) with hN
    have hNt : Tendsto N atTop atTop :=
      hφt.comp ((tendsto_add_atTop_nat k₀).comp hψ.tendsto_atTop)
    have hzlim : Tendsto (fun j => x (N j)) atTop (𝓝 xb) := hψlim
    have hzlimX : Tendsto (fun j => x (N j)) atTop (𝓝[X] xb) :=
      tendsto_nhdsWithin_iff.2 ⟨hzlim, Eventually.of_forall fun j => hxX _⟩
    have hFz : Tendsto (fun j => F (x (N j))) atTop (𝓝 v) :=
      hFlim.comp ((tendsto_add_atTop_nat k₀).comp hψ.tendsto_atTop)
    -- xb is a minimiser
    have hFxb : F xb = v := by
      refine le_antisymm ?_ (hFv xb hxbX)
      by_contra hc
      push Not at hc
      have h1 := (hFlsc xb hxbX) ((v + F xb) / 2) (by linarith)
      have h2 := hzlimX.eventually h1
      have h3 := hFz.eventually (gt_mem_nhds (show v < (v + F xb) / 2 by linarith))
      obtain ⟨j, hj1, hj2⟩ := (h2.and h3).exists
      linarith
    have hxbS : xb ∈ S := ⟨hxbX, hFxb⟩
    have hmle : m ≤ H xb := csInf_le hHS ⟨xb, hxbS, rfl⟩
    have hHz : Tendsto (fun j => H (x (N j))) atTop (𝓝 (H xb)) :=
      (hHcont xb hxbX).tendsto.comp hzlimX
    have hδN : Tendsto (fun j => δ (N j)) atTop (𝓝 0) := hHn.comp hNt
    have hle : H xb ≤ m - η / 2 := by
      have hup : Tendsto (fun j => m - η / 2 + δ (N j)) atTop (𝓝 (m - η / 2)) := by
        simpa using hδN.const_add (m - η / 2)
      exact le_of_tendsto_of_tendsto hHz hup (Eventually.of_forall fun j => hk1 _)
    linarith
  · -- upper bound
    intro b hb
    have hev := hHn.eventually (gt_mem_nhds (show (0:ℝ) < b - m by linarith))
    filter_upwards [hev] with n hn
    have htn := htpos n
    have key : (V n - v) / t n - δ n ≤ m := by
      refine le_csInf ⟨H x₀, x₀, hx₀S, rfl⟩ ?_
      rintro _ ⟨x, hxS, rfl⟩
      have h1 := hVle n x hxS.1
      rw [hxS.2] at h1
      have h3 := hδle n x hxS.1
      rw [abs_le] at h3
      rw [sub_le_iff_le_add, div_le_iff₀ htn]
      nlinarith [h3.2]
    have : δ n < b - m := hn
    show (V n - v) / t n < b
    linarith
