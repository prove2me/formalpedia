-- Prove2me | solution 1 for FoundationsRL.LinUCB.epsilon_net_unit_ball
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T08:54:39.957566+00:00
-- url     : https://prove2.me/submissions/52fc08b9-4775-4ffd-88c1-75cbd0bff667

import Mathlib

open Matrix MeasureTheory
open scoped ENNReal

theorem solution {d : ℕ} (Θ : Set (Fin d → ℝ)) (hΘ : ∀ θ ∈ Θ, θ ⬝ᵥ θ ≤ 1)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N : Finset (Fin d → ℝ), (N : Set (Fin d → ℝ)) ⊆ Θ ∧ (N.card : ℝ) ≤ (3 / ε) ^ d ∧
      ∀ θ ∈ Θ, ∃ θ' ∈ N, (θ - θ') ⬝ᵥ (θ - θ') ≤ ε ^ 2 := by
  classical
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- ## `d = 0`: the space is a singleton
    subst hd0
    haveI : Subsingleton (Fin 0 → ℝ) := ⟨fun f g => funext fun i => i.elim0⟩
    by_cases h0 : (fun _ : Fin 0 => (0 : ℝ)) ∈ Θ
    · refine ⟨Finset.univ, ?_, ?_, ?_⟩
      · intro x _
        have hx : x = (fun _ : Fin 0 => (0 : ℝ)) := Subsingleton.elim x _
        rw [hx]
        exact h0
      · have hc : (Finset.univ : Finset (Fin 0 → ℝ)).card = 1 := by simp
        rw [hc, Nat.cast_one]
        norm_num
      · intro θ _
        exact ⟨θ, Finset.mem_univ _, by simp [dotProduct, sq_nonneg]⟩
    · refine ⟨∅, by simp, by simp, ?_⟩
      intro θ hθ
      exact absurd (by simpa [Subsingleton.elim θ (fun _ : Fin 0 => (0 : ℝ))] using hθ) h0
  · -- ## `d ≥ 1`
    haveI : Nonempty (Fin d) := ⟨⟨0, hdpos⟩⟩
    let E := EuclideanSpace ℝ (Fin d)
    let e : E ≃L[ℝ] (Fin d → ℝ) := EuclideanSpace.equiv (Fin d) ℝ
    have hnorm : ∀ v : Fin d → ℝ, ‖e.symm v‖ ^ 2 = v ⬝ᵥ v := by
      intro v
      rw [EuclideanSpace.real_norm_sq_eq]
      have hof : (e.symm v).ofLp = v := rfl
      rw [hof]
      simp [dotProduct, sq]
    -- the preimage of `Θ` in `EuclideanSpace`
    let Θ' : Set E := e ⁻¹' Θ
    have hΘ'mem : ∀ x : E, x ∈ Θ' ↔ e x ∈ Θ := fun x => Iff.rfl
    have hball : Θ' ⊆ Metric.closedBall (0 : E) 1 := by
      intro x hx
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : ‖x‖ ^ 2 = (e x) ⬝ᵥ (e x) := by
        conv_lhs => rw [show x = e.symm (e x) from (e.symm_apply_apply x).symm]
        exact hnorm (e x)
      have h2 : (e x) ⬝ᵥ (e x) ≤ 1 := hΘ (e x) hx
      have h3 : ‖x‖ ^ 2 ≤ 1 := by rw [h1]; exact h2
      have h4 : Real.sqrt (‖x‖ ^ 2) ≤ 1 := Real.sqrt_le_one.mpr h3
      rwa [Real.sqrt_sq (norm_nonneg x)] at h4
    -- ## Zorn: a maximal `ε`-separated subset of `Θ'`
    let fam : Set (Set E) :=
      {S | S ⊆ Θ' ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ε ≤ dist x y}
    have hzorn : ∃ m, Maximal (fun x => x ∈ fam) m := by
      apply zorn_subset
      intro c hc hchain
      refine ⟨⋃₀ c, ?_, fun S hS => Set.subset_sUnion_of_mem hS⟩
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [Set.mem_sUnion] at hx
        obtain ⟨S, hSc, hxS⟩ := hx
        exact (hc hSc).1 hxS
      · intro x hx y hy hxy
        rw [Set.mem_sUnion] at hx hy
        obtain ⟨S, hSc, hxS⟩ := hx
        obtain ⟨T, hTc, hyT⟩ := hy
        by_cases hST : S = T
        · rw [← hST] at hyT
          exact (hc hSc).2 x hxS y hyT hxy
        · rcases hchain hSc hTc hST with hsub | hsub
          · exact (hc hTc).2 x (hsub hxS) y hyT hxy
          · exact (hc hSc).2 x hxS y (hsub hyT) hxy
    obtain ⟨N₀, hN₀fam, hN₀max⟩ := hzorn
    have hN₀sub : N₀ ⊆ Θ' := hN₀fam.1
    have hN₀sep : ∀ x ∈ N₀, ∀ y ∈ N₀, x ≠ y → ε ≤ dist x y := hN₀fam.2
    -- every point of `Θ'` is within `ε` of `N₀`
    have hnet : ∀ x ∈ Θ', ∃ y ∈ N₀, dist x y ≤ ε := by
      intro x hx
      by_contra h
      push_neg at h
      have hxN : x ∉ N₀ := by
        intro hxN
        have := h x hxN
        rw [dist_self] at this
        linarith
      have hfam : insert x N₀ ∈ fam := by
        refine ⟨?_, ?_⟩
        · intro z hz
          rcases hz with rfl | hz
          · exact hx
          · exact hN₀sub hz
        · intro y hy z hz hyz
          rcases hy with rfl | hy <;> rcases hz with rfl | hz
          · exact (hyz rfl).elim
          · exact (h z hz).le
          · rw [dist_comm]
            exact (h y hy).le
          · exact hN₀sep y hy z hz hyz
      exact hxN (hN₀max hfam (Set.subset_insert x N₀) (Set.mem_insert x N₀))
    -- ## finiteness of `N₀` via total boundedness
    have hδpos : 0 < ε / 2 := by linarith
    have hTB : TotallyBounded Θ' :=
      (isCompact_closedBall (0 : E) 1).totallyBounded.subset hball
    obtain ⟨F, hFfin, hFcover⟩ := Metric.totallyBounded_iff.mp hTB (ε / 2) hδpos
    have hNfin : N₀.Finite := by
      have hcoverN : N₀ ⊆ ⋃ y ∈ F, Metric.ball y (ε / 2) := hN₀sub.trans hFcover
      have hsingle : ∀ y, (N₀ ∩ Metric.ball y (ε / 2)).Subsingleton := by
        intro y x hx x' hx'
        by_contra hne
        have hsep : ε ≤ dist x x' := hN₀sep x hx.1 x' hx'.1 hne
        have hlt : dist x x' < ε := by
          calc dist x x' ≤ dist x y + dist y x' := dist_triangle x y x'
            _ < ε / 2 + ε / 2 := by
                refine add_lt_add ?_ ?_
                · exact hx.2
                · rw [dist_comm]; exact hx'.2
            _ = ε := by ring
        linarith
      have hEq : N₀ = ⋃ y ∈ F, (N₀ ∩ Metric.ball y (ε / 2)) := by
        refine Set.Subset.antisymm ?_ ?_
        · intro x hx
          have hx' := hcoverN hx
          simp only [Set.mem_iUnion, exists_prop] at hx' ⊢
          obtain ⟨y, hyF, hyb⟩ := hx'
          exact ⟨y, hyF, hx, hyb⟩
        · intro x hx
          simp only [Set.mem_iUnion, exists_prop] at hx
          obtain ⟨y, _, hxN, _⟩ := hx
          exact hxN
      rw [hEq]
      exact hFfin.biUnion (fun y _ => (hsingle y).finite)
    let Nf : Finset E := hNfin.toFinset
    have hNf : ∀ x, x ∈ Nf ↔ x ∈ N₀ := fun x => hNfin.mem_toFinset
    -- ## packing bound via volume
    have hVpos : 0 < volume (Metric.ball (0 : E) 1) := Metric.measure_ball_pos volume 0 one_pos
    have hVne : volume (Metric.ball (0 : E) 1) ≠ 0 := hVpos.ne'
    have hVtop : volume (Metric.ball (0 : E) 1) ≠ ⊤ := measure_ball_lt_top.ne
    have hvol : ∀ x : E, volume (Metric.ball x (ε / 2)) =
        ENNReal.ofReal ((ε / 2) ^ d) * volume (Metric.ball (0 : E) 1) := by
      intro x
      rw [Measure.addHaar_ball volume x (by linarith)]
      rw [finrank_euclideanSpace, Fintype.card_fin]
    have hvol0 : volume (Metric.ball (0 : E) (1 + ε / 2)) =
        ENNReal.ofReal ((1 + ε / 2) ^ d) * volume (Metric.ball (0 : E) 1) := by
      rw [Measure.addHaar_ball volume 0 (by linarith)]
      rw [finrank_euclideanSpace, Fintype.card_fin]
    have hdisj : (↑Nf : Set E).PairwiseDisjoint (fun x => Metric.ball x (ε / 2)) := by
      intro x hx y hy hxy
      apply Metric.ball_disjoint_ball
      have hsep : ε ≤ dist x y := hN₀sep x ((hNf x).mp hx) y ((hNf y).mp hy) hxy
      linarith
    have hsub_ball : (⋃ x ∈ Nf, Metric.ball x (ε / 2)) ⊆ Metric.ball (0 : E) (1 + ε / 2) := by
      intro z hz
      simp only [Set.mem_iUnion, exists_prop] at hz
      obtain ⟨x, hxF, hxz⟩ := hz
      have hxmem : x ∈ N₀ := (hNf x).mp hxF
      have hxnorm : ‖x‖ ≤ 1 := by
        have := hball (hN₀sub hxmem)
        rwa [Metric.mem_closedBall, dist_zero_right] at this
      rw [Metric.mem_ball] at hxz ⊢
      have hx0 : dist x 0 ≤ 1 := by rwa [dist_zero_right]
      calc dist z 0 ≤ dist z x + dist x 0 := dist_triangle z x 0
        _ < ε / 2 + 1 := add_lt_add_of_lt_of_le hxz hx0
        _ = 1 + ε / 2 := by ring
    have hmeasure : (Nf.card : ℝ≥0∞) * (ENNReal.ofReal ((ε / 2) ^ d) * volume (Metric.ball (0 : E) 1))
        ≤ ENNReal.ofReal ((1 + ε / 2) ^ d) * volume (Metric.ball (0 : E) 1) := by
      calc (Nf.card : ℝ≥0∞) * (ENNReal.ofReal ((ε / 2) ^ d) * volume (Metric.ball (0 : E) 1))
          = ∑ _x ∈ Nf, (ENNReal.ofReal ((ε / 2) ^ d) * volume (Metric.ball (0 : E) 1)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = ∑ x ∈ Nf, volume (Metric.ball x (ε / 2)) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [hvol x]
        _ = volume (⋃ x ∈ Nf, Metric.ball x (ε / 2)) := by
            rw [measure_biUnion_finset hdisj (fun x _ => measurableSet_ball)]
        _ ≤ volume (Metric.ball (0 : E) (1 + ε / 2)) := measure_mono hsub_ball
        _ = ENNReal.ofReal ((1 + ε / 2) ^ d) * volume (Metric.ball (0 : E) 1) := hvol0
    have hcancel : (Nf.card : ℝ≥0∞) * ENNReal.ofReal ((ε / 2) ^ d) ≤
        ENNReal.ofReal ((1 + ε / 2) ^ d) := by
      have h := hmeasure
      rw [← mul_assoc, ENNReal.mul_le_mul_iff_left hVne hVtop] at h
      exact h
    have hreal : (Nf.card : ℝ) * (ε / 2) ^ d ≤ (1 + ε / 2) ^ d := by
      have hane : ((Nf.card : ℝ≥0∞) * ENNReal.ofReal ((ε / 2) ^ d)) ≠ ⊤ :=
        ENNReal.mul_ne_top (by simp) (by simp)
      have hbne : (ENNReal.ofReal ((1 + ε / 2) ^ d)) ≠ ⊤ := by simp
      have h1 : ((Nf.card : ℝ≥0∞) * ENNReal.ofReal ((ε / 2) ^ d)).toReal ≤
          (ENNReal.ofReal ((1 + ε / 2) ^ d)).toReal :=
        (ENNReal.toReal_le_toReal hane hbne).mpr hcancel
      have h2 : ((Nf.card : ℝ≥0∞) * ENNReal.ofReal ((ε / 2) ^ d)).toReal =
          (Nf.card : ℝ) * (ε / 2) ^ d := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)]
      have h3 : (ENNReal.ofReal ((1 + ε / 2) ^ d)).toReal = (1 + ε / 2) ^ d :=
        ENNReal.toReal_ofReal (by positivity)
      rwa [h2, h3] at h1
    have hbound : (Nf.card : ℝ) ≤ (3 / ε) ^ d := by
      have hδd : (0 : ℝ) < (ε / 2) ^ d := by positivity
      have h1 : (Nf.card : ℝ) ≤ (1 + ε / 2) ^ d / (ε / 2) ^ d := by
        rw [le_div_iff₀ hδd]
        linarith
      have h2 : (1 + ε / 2) ^ d / (ε / 2) ^ d = ((1 + ε / 2) / (ε / 2)) ^ d := by
        rw [← div_pow]
      have h3 : (1 + ε / 2) / (ε / 2) = 1 + 2 / ε := by
        field_simp
        ring
      have h4 : (1 : ℝ) + 2 / ε ≤ 3 / ε := by
        have hεinv : (1 : ℝ) ≤ 1 / ε := by
          rw [le_div_iff₀ hε0]
          linarith
        have h3e : (3 : ℝ) / ε = 2 / ε + 1 / ε := by ring
        rw [h3e]
        linarith
      calc (Nf.card : ℝ) ≤ (1 + ε / 2) ^ d / (ε / 2) ^ d := h1
        _ = (1 + 2 / ε) ^ d := by rw [h2, h3]
        _ ≤ (3 / ε) ^ d := pow_le_pow_left₀ (by positivity) h4 d
    -- ## assemble
    refine ⟨Nf.image e, ?_, ?_, ?_⟩
    · intro y hy
      simp only [Finset.coe_image, Set.mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact hN₀sub ((hNf x).mp hx)
    · rw [Finset.card_image_of_injective Nf e.injective]
      exact hbound
    · intro θ hθ
      have hx : e.symm θ ∈ Θ' := by
        show e (e.symm θ) ∈ Θ
        rwa [e.apply_symm_apply]
      obtain ⟨y, hyN, hdy⟩ := hnet (e.symm θ) hx
      refine ⟨e y, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_image]
        exact ⟨y, (hNf y).mpr hyN, rfl⟩
      · have hlin : e.symm (θ - e y) = e.symm θ - y := by
          rw [map_sub, e.symm_apply_apply]
        have hsquare := hnorm (θ - e y)
        rw [hlin] at hsquare
        have hle : ‖e.symm θ - y‖ ≤ ε := by
          rwa [dist_eq_norm] at hdy
        rw [← hsquare]
        nlinarith [norm_nonneg (e.symm θ - y)]

