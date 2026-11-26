-- Prove2me | solution 1 for DeepONetUniversal.universal_approximation_functional
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T23:37:19.77887+00:00
-- url     : https://prove2.me/submissions/116eeecb-0015-4457-a03b-b7267e5903c1

import Mathlib
import Definitions.Def_DeepONetUniversal_Basic

open MeasureTheory Filter Topology DeepONetUniversal

theorem solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (σ : ℝ → ℝ) (hσ : IsTauberWiener σ)
    (K : Set X) (hK : IsCompact K) (V : Set C(K, ℝ)) (hV : IsCompact V)
    (f : C(K, ℝ) → ℝ) (hf : ContinuousOn f V) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ (m : ℕ) (x : Fin m → K) (c θ : Fin n → ℝ) (ξ : Fin n → Fin m → ℝ),
      ∀ u ∈ V, |f u - branchNet σ c ξ θ (fun j => u (x j))| < ε := by
  by_cases hVne : V.Nonempty
  · have : CompactSpace ↥V := isCompact_iff_compactSpace.mp hV
    have : Nonempty ↥V := hVne.to_subtype
    -- Define exponential linear functionals on V indexed by finitely supported measures on K
    let expEval (μ : K →₀ ℝ) : C(↥V, ℝ) :=
      ⟨fun u => Real.exp (μ.sum fun k r => r * u.1 k), by
        refine Real.continuous_exp.comp ?_
        unfold Finsupp.sum
        refine continuous_finsetSum _ fun k _ => ?_
        exact continuous_const.mul ((continuous_eval_const k).comp continuous_subtype_val)⟩
    have hexp_zero : expEval 0 = 1 := by
      ext u
      simp [expEval]
    have hexp_mul : ∀ μ₁ μ₂ : K →₀ ℝ, expEval μ₁ * expEval μ₂ = expEval (μ₁ + μ₂) := by
      intro μ₁ μ₂
      ext u
      simp only [ContinuousMap.mul_apply, expEval, ContinuousMap.coe_mk, ← Real.exp_add]
      congr 1
      rw [Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
    -- Form the subalgebra spanned by Set.range expEval
    let Sspan : Submodule ℝ C(↥V, ℝ) := Submodule.span ℝ (Set.range expEval)
    let A : Subalgebra ℝ C(↥V, ℝ) :=
      { carrier := Sspan
        mul_mem' := by
          intro g₁ g₂ hg₁ hg₂
          change g₁ ∈ Sspan at hg₁
          change g₂ ∈ Sspan at hg₂
          change g₁ * g₂ ∈ Sspan
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hg₁
          · rintro _ ⟨μ₁, rfl⟩
            refine Submodule.span_induction ?_ ?_ ?_ ?_ hg₂
            · rintro _ ⟨μ₂, rfl⟩
              rw [hexp_mul]
              exact Submodule.subset_span ⟨μ₁ + μ₂, rfl⟩
            · rw [mul_zero]; exact Sspan.zero_mem
            · intro x y _ _ hx hy; rw [mul_add]; exact Sspan.add_mem hx hy
            · intro r x _ hx; rw [mul_smul_comm]; exact Sspan.smul_mem r hx
          · rw [zero_mul]; exact Sspan.zero_mem
          · intro x y _ _ hx hy; rw [add_mul]; exact Sspan.add_mem hx hy
          · intro r x _ hx; rw [smul_mul_assoc]; exact Sspan.smul_mem r hx
        one_mem' := by
          change (1 : C(↥V, ℝ)) ∈ Sspan
          rw [← hexp_zero]
          exact Submodule.subset_span ⟨0, rfl⟩
        add_mem' := fun ha hb => Sspan.add_mem ha hb
        zero_mem' := Sspan.zero_mem
        algebraMap_mem' := fun r => by
          change algebraMap ℝ C(↥V, ℝ) r ∈ Sspan
          rw [Algebra.algebraMap_eq_smul_one]
          refine Sspan.smul_mem r ?_
          rw [← hexp_zero]
          exact Submodule.subset_span ⟨0, rfl⟩ }
    have hAsep : A.SeparatesPoints := by
      intro u₁ u₂ hne
      have hval : u₁.1 ≠ u₂.1 := fun h => hne (Subtype.ext h)
      have hexk : ∃ k : K, u₁.1 k ≠ u₂.1 k := by
        by_contra hall
        push Not at hall
        exact hval (DFunLike.ext _ _ hall)
      obtain ⟨k, hk⟩ := hexk
      refine ⟨expEval (Finsupp.single k 1), ?_, ?_⟩
      · exact ⟨expEval (Finsupp.single k 1), Submodule.subset_span ⟨Finsupp.single k 1, rfl⟩, rfl⟩
      · intro h
        have h1 : expEval (Finsupp.single k 1) u₁ = Real.exp (u₁.1 k) := by
          simp [expEval, Finsupp.sum_single_index]
        have h2 : expEval (Finsupp.single k 1) u₂ = Real.exp (u₂.1 k) := by
          simp [expEval, Finsupp.sum_single_index]
        rw [h1, h2] at h
        exact hk (Real.exp_injective h)
    -- Apply Stone-Weierstrass to f|_V
    obtain ⟨⟨g, hgA⟩, hg_approx⟩ :=
      ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints A hAsep
        (fun u : ↥V => f u.1) hf.domRestrict (ε / 2) (half_pos hε)
    -- Express g as a finite linear combination of expEval (μ s)
    have hg_span : g ∈ Submodule.span ℝ (Set.range expEval) := hgA
    rw [Finsupp.mem_span_range_iff_exists_finsupp] at hg_span
    obtain ⟨coeff, hcoeff⟩ := hg_span
    let S : ℕ := coeff.support.card
    let eS : Fin S ≃ coeff.support := coeff.support.equivFin.symm
    let a : Fin S → ℝ := fun s => coeff (eS s).1
    let μ : Fin S → (K →₀ ℝ) := fun s => (eS s).1
    have hg_eq : ∀ u : ↥V, g u = ∑ s : Fin S, a s * Real.exp ((μ s).sum fun k r => r * u.1 k) := by
      intro u
      rw [← hcoeff]
      simp only [Finsupp.sum, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply,
        smul_eq_mul]
      rw [← Finset.sum_coe_sort coeff.support]
      rw [← Equiv.sum_comp eS]
      rfl
    by_cases hS : S = 0
    · refine ⟨1, zero_lt_one, 0, Fin.elim0, fun _ => 0, fun _ => 0, fun _ => Fin.elim0, ?_⟩
      intro u huV
      have hgu : g ⟨u, huV⟩ = 0 := by
        rw [hg_eq ⟨u, huV⟩]
        exact Finset.sum_eq_zero fun s _ => absurd s.2 (by omega)
      have h1 : |g ⟨u, huV⟩ - f u| < ε / 2 := by
        simpa [Real.norm_eq_abs] using hg_approx ⟨u, huV⟩
      rw [hgu, zero_sub, abs_neg] at h1
      simp only [branchNet, zero_mul, Finset.sum_const_zero, sub_zero]
      linarith
    · have hSpos : 0 < S := Nat.pos_of_ne_zero hS
      classical
      -- Pool all sensor points from all μ s
      let suppK : Finset K := Finset.univ.biUnion fun s : Fin S => (μ s).support
      let m : ℕ := suppK.card
      let eK : Fin m ≃ suppK := suppK.equivFin.symm
      let x : Fin m → K := fun j => (eK j).1
      let W : Fin S → Fin m → ℝ := fun s j => μ s (x j)
      have hsum_eq : ∀ (s : Fin S) (u : C(K, ℝ)),
          (μ s).sum (fun k r => r * u k) = ∑ j : Fin m, W s j * u (x j) := by
        intro s u
        unfold Finsupp.sum
        have hsub : (μ s).support ⊆ suppK :=
          Finset.subset_biUnion_of_mem (fun s : Fin S => (μ s).support) (Finset.mem_univ s)
        rw [Finset.sum_subset hsub (fun k _ hk => by
          dsimp only
          rw [Finsupp.notMem_support_iff.mp hk, zero_mul])]
        rw [← Finset.sum_coe_sort suppK]
        rw [← Equiv.sum_comp eK]
      -- For each s, approximate exp on the compact range of u ↦ ∑ j, W s j * u (x j)
      have happrox_s : ∀ s : Fin S,
          ∃ (Ns : ℕ) (cs lams θs : Fin Ns → ℝ),
            ∀ u ∈ V, |Real.exp (∑ j : Fin m, W s j * u (x j)) -
              ∑ i : Fin Ns, cs i * σ (lams i * (∑ j : Fin m, W s j * u (x j)) + θs i)| <
              ε / (2 * S * (|a s| + 1)) := by
        intro s
        let Ls : C(↥V, ℝ) :=
          ⟨fun u => ∑ j : Fin m, W s j * u.1 (x j),
            continuous_finsetSum _ fun j _ =>
              continuous_const.mul ((continuous_eval_const (x j)).comp continuous_subtype_val)⟩
        let R : ℝ := ‖Ls‖
        have hδpos : 0 < ε / (2 * S * (|a s| + 1)) := by
          have : (0 : ℝ) < S := Nat.cast_pos.mpr hSpos
          positivity
        obtain ⟨Ns, cs, lams, θs, hNs⟩ :=
          hσ (-R) R Real.exp Real.continuous_exp.continuousOn (ε / (2 * S * (|a s| + 1))) hδpos
        refine ⟨Ns, cs, lams, θs, fun u huV => ?_⟩
        have hmem : ∑ j : Fin m, W s j * u (x j) ∈ Set.Icc (-R) R := by
          have hle : |Ls ⟨u, huV⟩| ≤ R := ContinuousMap.norm_coe_le_norm Ls ⟨u, huV⟩
          exact abs_le.mp hle
        exact hNs _ hmem
      choose Ns cs lams θs hNs using happrox_s
      -- Combine all (s, i) into a single Fin n with n = card (Σ s, Fin (Ns s)) + 1 > 0
      let Idx := Σ s : Fin S, Fin (Ns s)
      let n₀ : ℕ := Fintype.card Idx
      let eIdx : Fin n₀ ≃ Idx := (Fintype.equivFin Idx).symm
      let n : ℕ := n₀ + 1
      let c_all : Fin n → ℝ := fun k =>
        if hk : k.1 < n₀ then
          let p := eIdx ⟨k.1, hk⟩
          a p.1 * cs p.1 p.2
        else 0
      let θ_all : Fin n → ℝ := fun k =>
        if hk : k.1 < n₀ then
          let p := eIdx ⟨k.1, hk⟩
          θs p.1 p.2
        else 0
      let ξ_all : Fin n → Fin m → ℝ := fun k j =>
        if hk : k.1 < n₀ then
          let p := eIdx ⟨k.1, hk⟩
          lams p.1 p.2 * W p.1 j
        else 0
      refine ⟨n, Nat.succ_pos n₀, m, x, c_all, θ_all, ξ_all, ?_⟩
      intro u huV
      have hnet : branchNet σ c_all ξ_all θ_all (fun j => u (x j)) =
          ∑ s : Fin S, a s * ∑ i : Fin (Ns s),
            cs s i * σ (lams s i * (∑ j : Fin m, W s j * u (x j)) + θs s i) := by
        unfold branchNet
        rw [Fin.sum_univ_castSucc]
        have hlast : c_all (Fin.last n₀) * σ (∑ j, ξ_all (Fin.last n₀) j * u (x j) + θ_all (Fin.last n₀)) = 0 := by
          simp [c_all]
        rw [hlast, add_zero]
        have hsum_cast : (∑ k : Fin n₀,
            c_all k.castSucc * σ (∑ j, ξ_all k.castSucc j * u (x j) + θ_all k.castSucc)) =
            ∑ p : Idx, a p.1 * (cs p.1 p.2 *
              σ (lams p.1 p.2 * (∑ j : Fin m, W p.1 j * u (x j)) + θs p.1 p.2)) := by
          rw [← Equiv.sum_comp eIdx]
          refine Finset.sum_congr rfl fun k _ => ?_
          have hk : k.castSucc.1 < n₀ := k.2
          simp only [c_all, θ_all, ξ_all, dif_pos hk, Fin.val_castSucc, Fin.eta, mul_assoc]
          congr 3
          rw [Finset.mul_sum]
        rw [hsum_cast, Fintype.sum_sigma]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
      have h1 : |f u - g ⟨u, huV⟩| < ε / 2 := by
        have := hg_approx ⟨u, huV⟩
        rw [Real.norm_eq_abs, abs_sub_comm] at this
        exact this
      have h2 : |g ⟨u, huV⟩ - branchNet σ c_all ξ_all θ_all (fun j => u (x j))| < ε / 2 := by
        rw [hg_eq ⟨u, huV⟩, hnet, ← Finset.sum_sub_distrib]
        calc |∑ s : Fin S, (a s * Real.exp ((μ s).sum fun k r => r * u k) -
                a s * ∑ i : Fin (Ns s), cs s i * σ (lams s i * (∑ j : Fin m, W s j * u (x j)) + θs s i))|
            ≤ ∑ s : Fin S, |a s * Real.exp ((μ s).sum fun k r => r * u k) -
                a s * ∑ i : Fin (Ns s), cs s i * σ (lams s i * (∑ j : Fin m, W s j * u (x j)) + θs s i)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ < ∑ _s : Fin S, ε / (2 * S) := by
              refine Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hSpos)) ?_
              intro s _
              rw [hsum_eq s u, ← mul_sub, abs_mul]
              have hlt := hNs s u huV
              have hS_rpos : (0 : ℝ) < S := Nat.cast_pos.mpr hSpos
              have ha_pos : 0 < |a s| + 1 := by positivity
              calc |a s| * |Real.exp (∑ j : Fin m, W s j * u (x j)) -
                      ∑ i : Fin (Ns s), cs s i * σ (lams s i * (∑ j : Fin m, W s j * u (x j)) + θs s i)|
                  ≤ |a s| * (ε / (2 * S * (|a s| + 1))) := by gcongr
                _ < (|a s| + 1) * (ε / (2 * S * (|a s| + 1))) := by
                    have : 0 < ε / (2 * S * (|a s| + 1)) := by positivity
                    nlinarith
                _ = ε / (2 * S) := by field_simp [ha_pos.ne', hS_rpos.ne']
          _ = ε / 2 := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              have hS_rpos : (0 : ℝ) < S := Nat.cast_pos.mpr hSpos
              field_simp [hS_rpos.ne']
      calc |f u - branchNet σ c_all ξ_all θ_all (fun j => u (x j))|
          = |(f u - g ⟨u, huV⟩) + (g ⟨u, huV⟩ - branchNet σ c_all ξ_all θ_all (fun j => u (x j)))| := by
            congr 1; ring
        _ ≤ |f u - g ⟨u, huV⟩| + |g ⟨u, huV⟩ - branchNet σ c_all ξ_all θ_all (fun j => u (x j))| :=
            abs_add_le _ _
        _ < ε / 2 + ε / 2 := add_lt_add h1 h2
        _ = ε := add_halves ε
  · rw [Set.not_nonempty_iff_eq_empty] at hVne
    refine ⟨1, zero_lt_one, 0, Fin.elim0, fun _ => 0, fun _ => 0, fun _ => Fin.elim0, ?_⟩
    intro u huV
    rw [hVne] at huV
    exact huV.elim
