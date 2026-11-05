-- Prove2me | solution 1 for Dubey1986.Inefficiency.eff_interior_mem_Estar
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T00:37:02.989404+00:00
-- url     : https://prove2.me/submissions/284fbab2-9025-4771-bdba-dc962ec07570

import Mathlib
import Definitions.Def_Dubey1986_Inefficiency_Setting
import Definitions.Def_Dubey1986_Inefficiency_Derivative

open Dubey1986.Inefficiency Filter Topology

theorem solution {n : ℕ} (hn : 2 ≤ n) (k : Fin n → ℕ) (hk : ∀ i, 1 ≤ k i)
    (V : ∀ i, Set (Fin (k i) → ℝ)) (hVo : ∀ i, IsOpen (V i))
    (hSV : ∀ i, simplex (k i) ⊆ V i) (u : Fin n → Strat k → ℝ) (hu : IsGame V u)
    (s : Strat k) (hint : ∀ i, s i ∈ interior (simplex (k i))) (hs : s ∈ EffSet u) :
    Dmap u s ∈ Estar k := by
  intro hli
  -- Step 1: a common ascent direction `h` with `Du^i(s) h = 1` for all `i`.
  let Φ : Strat k →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun h i => Dmap u s i h
      map_add' := by intro a b; funext i; simp
      map_smul' := by intro c a; funext i; simp }
  have hsurj : LinearMap.range Φ = ⊤ := by
    by_contra hne
    obtain ⟨g, hg0, hg⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hg0
    have hc : ∀ i, g (Pi.single i 1) = 0 := by
      have := (Fintype.linearIndependent_iff.1 hli) (fun i => g (Pi.single i 1))
      apply this
      ext h
      have hm : Φ h ∈ LinearMap.ker g := hg ⟨h, rfl⟩
      rw [LinearMap.mem_ker] at hm
      have hdecomp : Φ h = ∑ i, (Dmap u s i h) • (Pi.single i (1:ℝ) : Fin n → ℝ) := by
        funext j; simp [Φ, Pi.single_apply]
      rw [hdecomp, map_sum] at hm
      simp only [map_smul, smul_eq_mul] at hm
      simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
        Pi.smul_apply, smul_eq_mul, zero_apply]
      rw [← hm]; apply Finset.sum_congr rfl; intro i _; ring
    apply LinearMap.ext_on_range (Pi.basisFun ℝ (Fin n)).span_eq
    intro i
    simpa [Pi.basisFun_apply] using hc i
  obtain ⟨h, hh⟩ : ∃ h, Φ h = fun _ => 1 := by
    have : (fun _ => (1:ℝ)) ∈ LinearMap.range Φ := by rw [hsurj]; trivial
    exact this
  have hh' : ∀ i, Dmap u s i h = 1 := fun i => congrFun hh i
  -- Step 2: differentiability of each payoff at `s`.
  have hVopen : IsOpen (Vset V) := isOpen_set_pi Set.finite_univ (fun i _ => hVo i)
  have hsV : s ∈ Vset V := Set.mem_univ_pi.2 fun i => hSV i (interior_subset (hint i))
  have hd : ∀ i, DifferentiableAt ℝ (u i) s := fun i =>
    ((hu i).1.differentiableOn (by norm_num)).differentiableAt (hVopen.mem_nhds hsV)
  -- Step 3: for small `t > 0`, `s + t h` is feasible and strictly better for all players.
  have hfeas : ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ i, s i + t • h i ∈ simplex (k i) := by
    apply eventually_nhdsWithin_of_eventually_nhds
    rw [eventually_all]
    intro i
    have hc : Continuous fun t : ℝ => s i + t • h i := by fun_prop
    have : ∀ᶠ t in 𝓝 (0:ℝ), s i + t • h i ∈ interior (simplex (k i)) := by
      apply hc.continuousAt.eventually_mem
      simpa using isOpen_interior.mem_nhds (hint i)
    exact this.mono fun t ht => interior_subset ht
  have hbetter : ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ i, u i s < u i (s + t • h) := by
    rw [eventually_all]
    intro i
    have hD : HasDerivAt (fun t : ℝ => u i (s + t • h)) (Dmap u s i h) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => s + t • h) h 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).smul_const h).const_add s
      have h2 : HasFDerivAt (u i) (fderiv ℝ (u i) s) (s + (0:ℝ) • h) := by
        simpa using (hd i).hasFDerivAt
      have := h2.comp_hasDerivAt (0:ℝ) h1
      exact this
    rw [hh' i, hasDerivAt_iff_tendsto_slope] at hD
    have hD' := hD.mono_left (nhdsWithin_mono _ (fun t (ht : t ∈ Set.Ioi (0:ℝ)) => ne_of_gt ht))
    have hpos : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < slope (fun t : ℝ => u i (s + t • h)) 0 t :=
      hD'.eventually_const_lt (by norm_num)
    filter_upwards [hpos, self_mem_nhdsWithin] with t ht ht0
    rw [slope_def_field] at ht
    simp only [zero_smul, add_zero, sub_zero] at ht
    have ht0' : (0:ℝ) < t := ht0
    have := (div_pos_iff_of_pos_right ht0').1 ht
    linarith
  obtain ⟨t, ht1, ht2⟩ := (hfeas.and hbetter).exists
  apply hs.2
  refine ⟨s + t • h, fun i _ => ht1 i, fun i _ => ?_, ⟨0, by omega⟩, Finset.mem_univ _, ?_⟩
  · have : update s Finset.univ (s + t • h) = s + t • h := by funext i; simp [update]
    rw [this]; exact (ht2 i).le
  · have : update s Finset.univ (s + t • h) = s + t • h := by funext i; simp [update]
    rw [this]; exact ht2 _
