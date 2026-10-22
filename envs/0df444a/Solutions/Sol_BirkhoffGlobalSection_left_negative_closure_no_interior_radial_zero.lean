-- Prove2me | solution 1 for BirkhoffGlobalSection.left_negative_closure_no_interior_radial_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T22:10:35.850868+00:00
-- url     : https://prove2.me/submissions/4a3843d6-db75-4471-bcbb-f1b97a9ec3aa

import Definitions.Def_BirkhoffGlobalSection
import Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_radial_transversality
import Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_nonpositive_energy
import Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_avoids_second_collision
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ s ∈ closure
      (connectedComponentIn
        {u : Phase | leviCivitaHamiltonian μ c u < 0 ∧
          0 < secondCollisionDistanceSq u}
        (fun _ : Fin 4 => (0 : ℝ))),
      ∀ a : ℝ, 0 ≤ a → a < 1 →
        leviCivitaHamiltonian μ c
          (fun i : Fin 4 => a * s i) ≠ 0 := by
  have hTr := left_negative_closure_radial_transversality μ c hμ0 hμ1 hc
  have hNP := left_negative_closure_nonpositive_energy μ c hμ0 hμ1 hc
  have hAv := left_negative_closure_avoids_second_collision μ c hμ0 hμ1 hc
  set U : Set Phase := {u : Phase | leviCivitaHamiltonian μ c u < 0 ∧
      0 < secondCollisionDistanceSq u} with hU
  set K : Set Phase := connectedComponentIn U (fun _ : Fin 4 => (0 : ℝ)) with hK
  have hsc : ∀ (a : ℝ) (s : Phase), (fun i : Fin 4 => a * s i) = a • s :=
    fun _ _ => rfl
  -- the origin lies in `U`
  have hD0 : secondCollisionDistanceSq (0 : Phase) = 1 := by
    simp [secondCollisionDistanceSq]
  have hH0 : leviCivitaHamiltonian μ c (0 : Phase) < 0 := by
    simp only [leviCivitaHamiltonian, hD0, zNormSq, wNormSq, Real.sqrt_one]
    simp
    linarith
  have h0U : (0 : Phase) ∈ U := ⟨hH0, by rw [hD0]; norm_num⟩
  -- openness of `U`
  have hDcont : Continuous secondCollisionDistanceSq := by
    unfold secondCollisionDistanceSq; fun_prop
  have hHcont : ContinuousOn (leviCivitaHamiltonian μ c)
      {s | 0 < secondCollisionDistanceSq s} := by
    unfold leviCivitaHamiltonian zNormSq wNormSq
    apply ContinuousOn.sub
    · exact Continuous.continuousOn (by fun_prop)
    · apply ContinuousOn.div
      · exact Continuous.continuousOn (by fun_prop)
      · exact Continuous.continuousOn (Real.continuous_sqrt.comp hDcont)
      · intro x hx
        exact (Real.sqrt_pos.2 hx).ne'
  have hUopen : IsOpen U := by
    have hUeq : U = {s | 0 < secondCollisionDistanceSq s} ∩
        leviCivitaHamiltonian μ c ⁻¹' Set.Iio 0 := by
      ext x; simp [U, and_comm]
    rw [hUeq]
    exact hHcont.isOpen_inter_preimage (isOpen_lt continuous_const hDcont) isOpen_Iio
  -- the radially star-shaped part of `U`
  set V : Set Phase := {x | ∀ t ∈ Set.Icc (0 : ℝ) 1, t • x ∈ U} with hV
  have hsV : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ V, t • y ∈ V := by
    intro t ht y hy r hr
    rw [smul_smul]
    exact hy (r * t) ⟨mul_nonneg hr.1 ht.1, mul_le_one₀ hr.2 ht.1 ht.2⟩
  have h0V : (0 : Phase) ∈ V := by
    intro t _; rw [smul_zero]; exact h0U
  have hVU : V ⊆ U := by
    intro x hx
    simpa using hx 1 ⟨zero_le_one, le_rfl⟩
  have hVopen : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).eventually_forall_of_forall_eventually
      (x₀ := x) (P := fun (y : Phase) (t : ℝ) => t • y ∈ U) (by
        intro t ht
        have hcont : Continuous (fun z : Phase × ℝ => z.2 • z.1) :=
          continuous_snd.smul continuous_fst
        exact hcont.continuousAt.preimage_mem_nhds (hUopen.mem_nhds (hx t ht)))
    exact this
  have hVstar : StarConvex ℝ (0 : Phase) V := by
    intro y hy a b _ hb hab
    rw [smul_zero, zero_add]
    exact hsV b ⟨hb, by linarith⟩ y hy
  have hVpre : IsPreconnected V :=
    (hVstar.isPathConnected h0V).isConnected.isPreconnected
  have hVK : V ⊆ K := hVpre.subset_connectedComponentIn h0V hVU
  have hKU : K ⊆ U := connectedComponentIn_subset _ _
  -- the key step: `K ⊆ V`
  have hclos : closure V ∩ K ⊆ V := by
    rintro x ⟨hxV, hxK⟩
    have hC : ∀ t ∈ Set.Icc (0 : ℝ) 1, t • x ∈ closure K := fun t ht =>
      closure_mono hVK (map_mem_closure (continuous_const_smul t) hxV
        (fun y hy => hsV t ht y hy))
    intro t ht
    refine ⟨lt_of_le_of_ne (hNP _ (hC t ht)) ?_, hAv _ (hC t ht)⟩
    intro hzero
    rcases eq_or_lt_of_le ht.1 with rfl | ht0
    · rw [zero_smul] at hzero; linarith
    rcases eq_or_lt_of_le ht.2 with rfl | ht1
    · rw [one_smul] at hzero; linarith [(hKU hxK).1]
    have hd := hTr (t • x) (hC t ht) hzero
    have hmax : IsLocalMax
        (fun a : ℝ => leviCivitaHamiltonian μ c (fun i : Fin 4 => a * (t • x) i)) 1 := by
      have hnhds : Set.Icc (0 : ℝ) (1 / t) ∈ nhds (1 : ℝ) :=
        Icc_mem_nhds (by norm_num) (by rw [lt_div_iff₀ ht0]; linarith)
      filter_upwards [hnhds] with a ha
      have e1 : (fun i : Fin 4 => (1 : ℝ) * (t • x) i) = t • x := by
        funext i; simp
      have e2 : (fun i : Fin 4 => a * (t • x) i) = (a * t) • x := by
        funext i; simp [mul_assoc]
      simp only [e1, e2, hzero]
      exact hNP _ (hC (a * t) ⟨mul_nonneg ha.1 ht0.le,
        by have := (le_div_iff₀ ht0).1 ha.2; linarith⟩)
    rw [hmax.deriv_eq_zero] at hd
    exact lt_irrefl _ hd
  have hKV : K ⊆ V :=
    isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hVopen
      ⟨0, mem_connectedComponentIn h0U, h0V⟩ hclos
  -- the closure is radially star-shaped
  have hCs : ∀ s ∈ closure K, ∀ a ∈ Set.Icc (0 : ℝ) 1, a • s ∈ closure K := by
    intro s hs a ha
    have hKK : Set.MapsTo (fun y : Phase => a • y) K K := fun y hy =>
      hVK (hsV a ha y (hKV hy))
    exact map_mem_closure (continuous_const_smul a) hs hKK
  intro s hs a ha0 ha1 hzero
  rw [hsc] at hzero
  rcases eq_or_lt_of_le ha0 with rfl | ha0'
  · rw [zero_smul] at hzero; linarith
  have hy := hCs s hs a ⟨ha0, ha1.le⟩
  have hd := hTr (a • s) hy hzero
  have hmax : IsLocalMax
      (fun u : ℝ => leviCivitaHamiltonian μ c (fun i : Fin 4 => u * (a • s) i)) 1 := by
    have hnhds : Set.Icc (0 : ℝ) (1 / a) ∈ nhds (1 : ℝ) :=
      Icc_mem_nhds (by norm_num) (by rw [lt_div_iff₀ ha0']; linarith)
    filter_upwards [hnhds] with u hu
    have e1 : (fun i : Fin 4 => (1 : ℝ) * (a • s) i) = a • s := by
      funext i; simp
    have e2 : (fun i : Fin 4 => u * (a • s) i) = (u * a) • s := by
      funext i; simp [mul_assoc]
    simp only [e1, e2, hzero]
    exact hNP _ (hCs s hs (u * a) ⟨mul_nonneg hu.1 ha0,
      by have := (le_div_iff₀ ha0').1 hu.2; linarith⟩)
  rw [hmax.deriv_eq_zero] at hd
  exact lt_irrefl _ hd
