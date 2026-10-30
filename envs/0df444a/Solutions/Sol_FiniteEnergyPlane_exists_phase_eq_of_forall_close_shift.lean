-- Prove2me | solution 1 for FiniteEnergyPlane.exists_phase_eq_of_forall_close_shift
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-29T21:38:24.834439+00:00
-- url     : https://prove2.me/submissions/ddd82442-611a-45b2-80aa-27959e102a76

import Mathlib



namespace FiniteEnergyPlane

open Filter Topology

theorem exists_phase_eq_of_forall_close_shift_aux {F : Type*} [NormedAddCommGroup F] {x : ℝ → F}
    {T : ℝ} (hT : 0 < T) (hx : Continuous x) (hxT : Function.Periodic x T) (κ : ℝ)
    (f : ℕ → ℝ → F) (L : ℝ → F) (hf : ∀ t, Tendsto (fun j => f j t) atTop (𝓝 (L t)))
    (hclose : ∀ ε > 0, ∀ᶠ j in atTop, ∃ c : ℝ, ∀ t : ℝ, ‖f j t - x (κ * t + c)‖ ≤ ε) :
    ∃ c : ℝ, ∀ t : ℝ, L t = x (κ * t + c) := by
  -- the phases `ε`-good for `L`, reduced to one period
  set K : ℕ → Set ℝ := fun i => Set.Icc 0 T ∩
    {c | ∀ t : ℝ, ‖L t - x (κ * t + c)‖ ≤ 1 / ((i : ℝ) + 1)} with hKdef
  have hcont : ∀ t, Continuous fun c : ℝ => ‖L t - x (κ * t + c)‖ := fun t =>
    (continuous_const.sub (hx.comp (continuous_const.add continuous_id))).norm
  have hKc : ∀ i, IsClosed (K i) := fun i => isClosed_Icc.inter <| by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun t => isClosed_le (hcont t) continuous_const
  have hKk : ∀ i, IsCompact (K i) := fun i => isCompact_Icc.of_isClosed_subset (hKc i)
    Set.inter_subset_left
  have hKmono : ∀ i, K (i + 1) ⊆ K i := by
    intro i c hc
    refine ⟨hc.1, fun t => (hc.2 t).trans ?_⟩
    gcongr
    push_cast
    linarith
  have hKne : ∀ i, (K i).Nonempty := by
    intro i
    set ε : ℝ := 1 / ((i : ℝ) + 1) with hε
    have hε0 : 0 < ε := by positivity
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hclose ε hε0)
    choose c hc using fun j : ℕ => hN (j + N) (Nat.le_add_left _ _)
    set c' : ℕ → ℝ := fun j => toIcoMod hT 0 (c j) with hc'def
    have hc'mem : ∀ j, c' j ∈ Set.Icc 0 T := fun j => by
      have := toIcoMod_mem_Ico hT 0 (c j)
      simp only [zero_add] at this
      exact ⟨this.1, this.2.le⟩
    have hc'eq : ∀ j t, x (κ * t + c' j) = x (κ * t + c j) := by
      intro j t
      simp only [hc'def, toIcoMod]
      rw [← add_sub_assoc, hxT.sub_zsmul_eq]
    obtain ⟨c₀, hc₀, ψ, hψ, hlim⟩ := isCompact_Icc.tendsto_subseq hc'mem
    refine ⟨c₀, hc₀, fun t => ?_⟩
    have h1 : Tendsto (fun l => ‖f (ψ l + N) t - x (κ * t + c' (ψ l))‖) atTop
        (𝓝 ‖L t - x (κ * t + c₀)‖) := by
      have hfψ : Tendsto (fun l => f (ψ l + N) t) atTop (𝓝 (L t)) :=
        (hf t).comp ((tendsto_add_atTop_nat N).comp hψ.tendsto_atTop)
      exact (hfψ.sub ((hx.tendsto _).comp (tendsto_const_nhds.add hlim))).norm
    refine le_of_tendsto' h1 fun l => ?_
    rw [hc'eq]
    exact hc (ψ l) t
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hKmono
    hKne (hKk 0) hKc
  refine ⟨c, fun t => ?_⟩
  rw [Set.mem_iInter] at hc
  have hle : ∀ i : ℕ, ‖L t - x (κ * t + c)‖ ≤ 1 / ((i : ℝ) + 1) := fun i => (hc i).2 t
  have h0 : ‖L t - x (κ * t + c)‖ ≤ 0 :=
    ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat hle
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

end FiniteEnergyPlane

open FiniteEnergyPlane

open Filter Topology

theorem solution {F : Type*} [NormedAddCommGroup F] {x : ℝ → F}
    {T : ℝ} (hT : 0 < T) (hx : Continuous x) (hxT : Function.Periodic x T) (κ : ℝ)
    (f : ℕ → ℝ → F) (L : ℝ → F) (hf : ∀ t, Tendsto (fun j => f j t) atTop (𝓝 (L t)))
    (hclose : ∀ ε > 0, ∀ᶠ j in atTop, ∃ c : ℝ, ∀ t : ℝ, ‖f j t - x (κ * t + c)‖ ≤ ε) :
    ∃ c : ℝ, ∀ t : ℝ, L t = x (κ * t + c) :=
  exists_phase_eq_of_forall_close_shift_aux hT hx hxT κ f L hf hclose
